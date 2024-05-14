# Overview information

TODO(paulberry): I'm experimenting with calling the inference in method bodies
and initializer expressions "body inference". Get feedback on this.

Body inference is specified as a transformation from the syntactic artifacts
that constitute method bodies and initializer expressions (expressions,
statements, patterns, and collection elements) to coresponding artifacts in the
compiled output (referred to as "compilation artifacts"). The precise form of
compilation artifacts is not dictated by the specification; instead they are
specified in terms of their runtime behavior.

TODO(paulberry): maybe talk about how when we specify compilation artifacts in
terms of their runtime behavior, we gloss over exception semantics.

TODO(paulberry): maybe talk about the fact that errors are specified in this
doc, and that if at least one error is detected, the only normative behavior is
that compilation aborts; the precise details of error recovery and error
reporting are outside the scope of the specification.

TODO(paulberry): maybe talk about why it's important to specify type inference
as a series of procedural steps because of the state implicitly tracked by flow
analysis.

TODO(paulberry): talk about how we're going to assume soundness in this spec.

TODO(paulberry): is `<:!` OK?

# Expressions

Type inference of an expression always takes place with respect to a type schema
known as the expression's "context". TODO(paulberry): examples?

Type inference of an expression produces a compilation artifact and a static
type.

TODO(paulberry): explain how it's not necessary for the static type of an
expression to conform to its context.

## Null

Type inference of the literal `null`, in context `K`, produces a compilation
artifact with static type `Null`, whose runtime behavior is to evaluate to the
_null object_.

## Numbers

Type inference of an integer literal `l`, in context `K`, proceeds as follows:

- Let `i` be the numeric value of `l`.

- If the type `double` is assignable to `K`, and the type `int` is _not_
  assignable to `K`, then: (TODO(paulberry): assignability is only well defined
  between types; `K` is a type _schema_) (TODO(paulberry): the analyzer accounts
  for strong mode when performing these assignability checks; what is the effect
  of this?)

  - The result of type inference is a compilation artifact with static type
    `double`, whose runtime behavior is to evaluate to an instance of `double`
    representing the value `i`.

  - If `i` cannot be represented _precisely_ by an instance of `double`, then
    there is a compile-time error. TODO(paulberry): does the analyzer actually
    implement this behavior?

- Otherwise, if `l` is a hexadecimal integer literal, 2<sup>63</sup> ≤ `i` <
  2<sup>64</sup>, and the `int` class is represented as signed 64-bit two's
  complement integers:

  - The result of type inference is a compilation artifact with static type
    `int`, whose runtime behavior is to evaluate to an instance of `int`
    representing the value `i` - 2<sup>64</sup>. TODO(paulberry): does the CFE
    actually implement this behavior?

- Otherwise:

  - The result of type inference is a compilation artifact with static type
    `int`, whose runtime behavior is to evaluate to an instance of `int`
    representing the value `i`.

  - If `i` cannot be represented _precisely_ by an instance of `int`, then there
    is a compile-time error. TODO(paulberry): does the analyzer actually
    implement this behavior?

TODO(paulberry): the CFE's `InferenceVisitorImpl.visitIntLiteral` method doesn't
implement int-to-double logic. What's up with that?

TODO(paulberry): non-normative notes about numeric literals preceded by unary
minus.

## Booleans

Type inference of a boolean literal (`true` or `false`), in context `K`,
produces a compilation artifact with static type `bool`, whose runtime behavior
is to evaluate to the object _true_ or _false_ (as appropriate).

## Strings

Type inference of a string literal `s`, in context `K`, proceeds as follows:

- For each _stringInterpolation_ `s_i` inside `s`, in source order:

  - Define `m_i` as follows:
  
    - If `s_i` takes the form '`${`' `e` '`}`':

      - Let `m_i` be the result of performing type inference on `e`, in context `_`.

    - Otherwise, `s_i` takes the form '`$e`', where `e` is either `this` or an
      identifier that doesn't begin with `$`, so:
    
      - Let `m_i` be the result of performing type inference on `e`, in context
        `_`.

  - Let `T_i` be the static type of `m_i`.

  - If `T_i :<! Object` and `T_i` is not `dynamic`, then there is a compile time
    error.

- The result of type inference is a compilation artifact with static type
  `String`, whose runtime behavior is as follows:
  
  - For each `i`, in order:
  
    - Execute compilation artifact `m_i`, and let `o_i` be the resulting value.
    
    - Invoke the `toString` method on `o_i`, with no arguments, and let `r_i` be
      the return value. _(Note that since both `Object.toString` and
      `Null.toString` are declared with a return type of `String`, it follows
      from soundness that `r_i` will have a runtime type of `String`)._

  - Concatenate together the `r_i` strings (interspersing with any
    non-interpolation characters in `s`) to produce an instance of `String`.

## Symbol literal

Type inference of a symbol literal, in context `K`, produces a compilation
artifact with static type `Symbol`, whose runtime behavior is to evaluate to an
appropriate instance of `Symbol`.

## Collection literals

TODO(paulberry): reconcile with spec

### List literal

### Set or map literal

## Throw

Type inference of a throw expression `throw e_1`, in context `K`, proceeds as
follows:

- Let `m_1` be the result of performing type inference on `e_1`, in context `_`.

- Let `T_1` be the static type of `m_1`. If `T_1` is not `dynamic`, and `T_1 <:!
  Object`, then there is a compile-time error.

  - TODO(paulberry): would it be better to spec this in terms of a coercion? CFE
    creates an `AsExpression` so it would make sense.

- The result of type inference is a compilation artifact with static type
  `Never`, whose runtime behavior is as follows:

  - Execute the compilation artifact `m_1`, and let `o_1` be the resulting
    value.

  - If `o_1` is the _null object_, throw an unspecified
    exception. (TODO(paulberry): in practice it's `_TypeError`. Maybe this is
    specified in the null safety spec?)

  - Throw `o_1`.

## Function expressions

## This

Type inference of the expression `this`, in context `K`, proceeds as follows:

- Let `T` be the interface type of the immediately enclosing class, enum, mixin,
  or extension type, or the "on" type of the immediately enclosing extension.
  
- If there is no immediately enclosing class, enum, mixin, extension type, or
  extension, then there is a compile-time error.

- If the expression `this` appears inside a factory constructor, a constructor's
  initializer list, a static method or variable initializer, or in the
  initializing expression of a non-late instance variable, then there is a
  compile-time error.

- The result of type inference is a compilation artifact with static type `T`,
  whose runtime behavior is to evaluate to the target of the current instance
  member invocation.

## Instance creation

## Function invocation

TODO(paulberry): what goes here?

## Function closurization

TODO(paulberry): what goes here?

## Generic function instantiation

TODO(paulberry): what goes here? Anything?

## Lookup

TODO(paulberry): what goes here? Anything?

## Top level getter invocation

TODO(paulberry): what goes here? Anything?

## Member invocations

TODO(paulberry): what goes here? Anything?

### Index expression

## Method invocation

### Cascade expression

TODO(paulberry): this is really weird for this to be here

## Property extraction

TODO(paulberry): reconcile with spec

### Property access

## Assignment

## Conditional

## If-null expressions

TODO(paulberry): split from binary expressions

## Logical boolean expressions

TODO(paulberry): split from binary expressions

## Equality

TODO(paulberry): split from binary expressions

## User-definable binary operations

Note: spec splits these into "relational expressions", "bitwise expressions",
"shift", "additive expressions", and "multiplicative expressions".

TODO(paulberry): make sure all analyzer behaviors are covered either here or in
"equality", "logical boolean expressions", or "if-null expressions".

## Unary expressions

See "prefix expression" in the analyzer

## Await expressions

## Postfix expressions

TODO(paulberry): does `!` go grammatically with other postfix expressions?

## Assignable expressions

TODO(paulberry): what goes here? anything? Maybe l-values?

## Lexical lookup

TODO(paulberry): what goes here? anything?

## Identifier reference

TODO(paulberry): what goes here? anything?

## Type test

## Type cast

==== ABOVE FOLLOWS SPEC

## Augmented expression

TODO(paulberry): postpone working on this?

## Augmented invocation

TODO(paulberry): postpone working on this?

## Constructor reference

TODO(paulberry): is this real?

## Function expression invocation

TODO(paulberry): reconcile this with the spec

## Function reference

TODO(paulberry): reconcile this with the spec

## Parenthesized expression

TODO(paulberry): this is probably worth talking about because of its effect on
null shorting. Where should we talk about it?

## Pattern assignment

## Prefixed identifier

TODO(paulberry): split out cases to match spec

## Record literal

## Rethrow expression

TODO(paulberry): this is spec'ed as a statement.

## Simple identifier

TODO(paulberry): split out cases to match spec?

## Super expression

TODO(paulberry): rework to match spec

## Switch expression

## Type literal

# Other things

TODO(paulberry): patterns

TODO(paulberry): statements

TODO(paulberry): elements
