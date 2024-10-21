# Enum shorthand prototype report

Paul Berry
October 21, 2024

## Background

During Wednesday morning's Dart language team meeting, we debated the best way to scope the "enum shorthands" feature. Should it:
1. Be limited just to static gets (e.g., `Endian littleEndian = .little;`),
2. Also support static method invocations (e.g., `int value = .parse(input);`) and/or constructor invocations (e.g., `String s = .fromCharCode(42);`),
3. Also support arbitrary length selector chains that start with `.` (e.g., `int posNum = .parse(userInput).abs();`) (as suggested by [Lasse's latest proposal](https://github.com/dart-lang/language/blob/main/working/3616%20-%20enum%20value%20shorthand/proposal-simple-lrhn.md)),
4. Or support any expression that starts with `.` (e.g. `int i = .parse(userInput).abs() / 2 + 1;`)?

A key concern, as I understood it, was that in the more ambitious options, the context would have to be threaded through the analysis pipeline from one part of the syntax tree to another, and it wasn't clear whether doing so would be a significant source of complexity. I filed https://github.com/dart-lang/language/issues/4130 in the hopes that we could continue the discussion offline, comparing the cost and the user benefit of the various alternatives.

Starting late Thursday, in an effort to better understand the implementation complexity, I embarked on a one-day prototyping effort, with an eye to understanding how the various options differed in terms of their implementation complexity.

## TL/DR

Over a 9 hour prototyping effort, I was able to add analyzer support for all but one example from Lasse's proposal, plus support for option 4, including type checking and error handling. I came up with a "parser breadcrumb" technique that allowed me to thread the context through the analysis pipeline without having to touch the behavior of any of the AST nodes that the context would have to be "threaded through". This made the implementation complexity of options 2, 3, and 4 all very similar to one another. I believe this technique will also work with the CFE, though I haven't confirmed it.

I took some significant shortcuts in the AST representation (since modifying analyzer AST classes is expensive), so those shortcuts would have to be reworked in order to convert my prototype into something shippable.

## Type inference modifications and parser breadcrumbs

As I explained in https://github.com/dart-lang/language/issues/4130, a key difficulty with supporting selector chains (or arbitrary expressions starting with `.`) is that the inference context must be captured at one point in the parse tree, threaded down through several kinds of expression nodes, and then used at a potentially much lower place in the parse tree. Repeating my example from that issue, `A x = .b()()![1].c;` will be parsed as something like:

```
  VariableDeclaration
 /     |      |      \
A      x      =       PropertyGet
                     /           \
                 Index            .c
                /     \
            NullCheck  [1]
           /         \
       Function       !
       Invocation
      /          \
  Method          ()
  Invocation
            \
             .b()
```

The downward inference context needs to be captured at the point where type inference enters the `PropertyGet`, and used to resolve the enum shorthand at the point of the `MethodResolution`.

To avoid having to modify the type inference logic for `Index`, `NullCheck`, and `FunctionInvocation`, I added logic to the parser to make it generate two new nodes:
- A node just above the `PropertyGet`, telling the analyzer that the context needs to be captured. I call this the "enum shorthand context node".
- A node just to the left of the initial `.`, telling the analyzer that this is where the captured context should be used. I call this the "enum shorthand target node".

In my prototype, the enum shorthand context node is represented as a unary expression using the operand `~`, and the enum shorthand target node is represented as the identifier `MAGIC`. I chose these representations to save time, since they allowed me to implement the feature without changing the analyzer's AST representation. Obviously they wouldn't be suitable for a full implementation of the feature.

With these new nodes, the parse tree looks like this:

```
  VariableDeclaration
 /     |      |      \
A      x      =       PrefixExpression
                     /                \
                    ~                  PropertyGet
                                      /           \
                                  Index            .c
                                 /     \
                         NullCheck      [1]
                        /         \
                Function           !
                Invocation
               /          \
      Method               ()
      Invocation
     /          \
MAGIC            .b()
```

Now, in the shared `TypeAnalyzer` mixin (which is used by the analyzer's `ResolverVisitor`), there is a new field, `_enumShorthands`, which is a stack of type schemas. When the `ResolverVisitor` enters the enum shorthand context node, it pushes the context onto this stack. When it enters the `MethodInvocation` whose target is the enum shorthand target node, it retrieves the context from the the top entry in the stack. When it finally leaves the enum shorthand context node, it pops the context off the stack.

The most complex part of this process is the logic for what to do with the context at the site of the `MethodInvocation`. The analyzer needs to find the class (or extension type) declaration associated with the context, and then use this for method lookup instead of trying to resolve the identifier `MAGIC` to a class declaration. This is about 20 lines of code (`MethodInvocationResolver._resolveEnumShorthand`).

Additionally, the `MethodInvocationResolver` needs to be prepared for the possibility that the lookup finds a constructor rather than a static method, and if so rewrite the node from a `MethodInvocation` to an `InstanceCreationExpression`. The analyzer already has logic for doing this sort of rewrite (to handle implicit `new`), but I couldn't use it because it happens before type inference. So I had to recreate it. That was about 35 lines in `MethodInvocationResolver._resolveReceiverTypeLiteral`, plus another 30 lines or so of diffs in `MethodInvocationResolver` to allow the rewritten expression to be plumbed back to the `ResolverVisitor`, and about 25 lines of diffs in the `ResolverVisitor` itself to handle the rewrite.

Similar logic had to be added to `PropertyElementResolver`, to handle enum shorthands that complete to a static getter rather than a static method. But this logic is more isolated, since no rewriting is required. In total it's about 40 new lines in `PropertyElementResolver`.

## Parser changes

TODO

## Special rules for RHS of `==`

Lasse's proposal specifies that it should be possible to use an enum shorthand on the RHS of `==`. This requires extra machinery, because normally the downward inference context on the RHS of `==` is `Object?`. To make this work, I added 

Lasse's proposal includes the use of a special context for resolving 

For example, consider my (admittedly rather silly) example from : `A x = .b()()![1].c;` which parses like this:

To avoid having to add logic to thread this information through all kinds of AST nodes, I added a stack of contexts to the analyzer's `ResolverVisitor`. A context is added to this stack at the point where it is captured, and then the top of the stack is examined at the time the context needs to be used to resolve an enum shorthand.

For example, to handle

Although the grammar of Dart expressions is specified using a large number of BNF rules reflecting the various precedence levels, the parser implementation handles precedence using an [operator precedence parser](https://en.wikipedia.org/wiki/Operator-precedence_parser) technique. The method `parsePrecedenceExpression` consumes the first part of the expression (a `<primary>` optionally preceded by a unary operator) by calling `parseUnaryExpression`, and then, after some special logic to tell if a following `<` is an operator or the beginning of `<typeArguments>`, there is a call to `_parsePrecedenceExpressionLoop`, which consumes the remainder of the expression.

I inserted logic at the top of `parsePrecedenceExpression` that inspects the tokens that are about to be parsed; if they look like `. IDENTIFIER`, it knows that `parseUnaryExpression` will 

## Testing burden

believe there's a nontrivial difference between the implementation complexity of options 1 and 2, , with the exception that I didn't support expressions beginning with `const`. Based on what I've found, I don't believe that  didn't find anything to make me option 3 any significant difference in complexity between options 3 and 4. I took some significant shortcuts in the analyzer AST representation, but I believe to make the prototyping effort go faster, but I tried to do so in a way that wouldn't significantly impact my conclusions on  wouldn't call into question my conclusions on the minimize the extent to which my shortcuts not to take shortcuts in any areas that would impact the  to accept, and properly type check, all the examples from Lasse's proposal except for this one involving const: `Symbol symbol = const .new("orange");`, as well as examples of option 4 (. In my opinion the complexity is manageable  found the complexity to be manageable
