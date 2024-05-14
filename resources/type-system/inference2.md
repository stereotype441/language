# Overview information

TODO(paulberry): I'm experimenting with calling the inference in method bodies
and initializer expressions "body inference". Get feedback on this.

Body inference is specified as a transformation from the syntactic artifacts
that constitute method bodies and initializer expressions (expressions,
statements, patterns, and collection elements) to coresponding artifacts in the
compiled output (referred to as "compilation artifacts"). The precise form of
compilation artifacts is not dictated by the specification; instead they are
specified in terms of their runtime behavior.

When executed, a compilation artifact may behave in one of three ways: it may
complete normally, complete with an exception, or fail to complete at all
(e.g. due to an infinite loop, or an asynchronous suspension that never
completes).

If a compilation artifact associated with an expression completes normally,
there will be an associated value (and the compilation artifact is said to
_complete with_ the value). Type inference associates each such compilation
artifact with a _static type_, and guarantees that _if_ the compilation artifact
completes normally, the associated value will be an instance of the static
type. This guarantee is known as _expression soundness_.

_Elsewhere in the spec, we speak of an expression having a static type, but in
the presence of coercions, this can sometimes be confusing, since a given
expression might be associated with more than one compilation artifact. For
example in the code `dynamic d = ...; int i = d;`, the expression `d` is
associated with two compilation artifacts: one which is the result of reading
the value of the variable `d`, and one which is the result of casting that value
to the type `int`. The former artifact has static type `dynamic`; the latter has
static type `int`. Since this document details precisely when and how coercions
occur, and makes arguments about soundness of expressions that might involve
coercions, it is useful to be precise by associating static types with the
compilation artifacts._

TODO(paulberry): maybe talk about how when we specify compilation artifacts in
terms of a sequence of steps, it is implied that unless otherwise specified, if
any step in the sequence completes with an exception, then the rest of the
sequence is skipped, and the entire sequence completes with the same
exception. Similarly, if any step in the sequence fails to complete at all, then
the remaining steps are not executed, and the entire sequence fails to complete
at all.

TODO(paulberry): maybe talk about the fact that errors are specified in this
doc, and that if at least one error is detected, the only normative behavior is
that compilation aborts; the precise details of error recovery and error
reporting are outside the scope of the specification.

TODO(paulberry): maybe talk about why it's important to specify type inference
as a series of procedural steps because of the state implicitly tracked by flow
analysis.

## Other soundness guarantees

There are several other soundness guarantees beyond the _expression soundness_
guarantee described above.

It is guaranteed that if a method, function, or constructor having return type
`T` is invoked, and the method completes with a value `v`, then `v` will be an
instance of `T` (with appropriate type substitutions, in the case of a generic
method). This guarantee is known as _return value soundness_.

TODO(paulberry): define a complementary notion of _argument soundness_, and
argue for why it holds in the text below.

It is guaranteed that if a method having static type `T` is torn off, then the
resulting value will be an instance of `T`. This guarantee is known as _tear-off
soundness_.

It is guaranteed that if a future is an instance of the type `Future<T>`, and it
completes with a value `v`, then `v` will be an instance of `T`. This guarantee
is known as _future soundness_.

# Coercions

Coercion is a type inference step that transforms a compilation artifact `m'`,
and a desired static type `T`, into a compilation artifact `m` whose static
type is `T`.

_Coercions are used in most situations where the existing spec calls for an
assignability check._

Coercion of a compilation artifact `m'` to type `T` produces a compilation
artifact `m` with static type `T`, where `m` is determined as follows:

- Let `T'` be the static type of `m'`.

- Define `m` as follows:

  - If `T' <: T`, then let `m` be a compilation artifact whose runtime behavior
    is as follows:

    - Execute compilation artifact `m'`, and let `o` be the resulting value. _By
      execution soundness, `o` will be an instance of the type `T'`._

    - `m` completes with the value `o`. _Expression soundenss follows from the
      fact that since `T' <: T`, `o` must also be an instance of the type `T`._

  - Otherwise, if `T'` is `dynamic`, then let `m` be a compilation artifact
    whose runtime behavior is as follows:

    - Execute compilation artifact `m'`, and let `o` be the resulting value. _By
      execution soundness, `o` will be an instance of the type `T'`._
  
    - If `o` is an instance of the type `T`, `m` completes with the value
      `o`. _Expression soundness follows trivially._
    
    - Otherwise, `m` completes with an exception (TODO(paulberry): which
      exception?). _Expression soundness follows trivially._
    
  - Otherwise, if `T'` is an interface type that contains a method called `call`
    with type `U`, and `U <: T`, then let `m` be a compilation artifact
    whose runtime behavior is as follows:

    - Execute compilation artifact `m'`, and let `o` be the resulting value. _By
      execution soundness, `o` will be an instance of the type `T'`._

    - Let `o'` be the result of tearing off the `call` method of `o`. _This is
      guaranteed to succeed since `o` is an instance of `T'`, and it is
      guaranteed by tear-off soundness that `o'` will be an instance of `U`._
    
    - `m` completes with the value `o'`. _Expression soundness follows from the
      fact that `o'` is an instance of `U` and `U <: T`._

  - TODO(paulberry): add more cases to handle implicit instantiation of generic
    function types, and `call` tearoff with implicit instantiation.

  - Otherwise, there is a compile-time error.

## Shorthand for coercions

In the text that follows, we will sometimes say something like "let `m` be the
result of performing expression type inference on `e`, in context `K`, and then
coercing the result to type `T`." This is shorthand for the following sequence
of steps:

- Let `m'` be the result of performing expression type inference on `e`, in
  context `K`.

- Let `m` be the result of performing coercion of `m'` to type `T`.

# Expression type inference

Expression type inference is the sequence of steps performed by the compiler to
interpret the meaning of an expression in the source code. The specific steps
depend on the form of the expression, and are explained below, for each kind of
expression.

Expression type inference always takes place with respect to a type schema known
as the expression's "context". TODO(paulberry): examples?

The rules below include informal sketches of a proof that each expression type
satisfies expression soundness. These are non-normative, so they are typeset in
_italics_.

TODO(paulberry): explain how it's not necessary for the static type of an
expression to conform to its context.

## Null

Expression type inference of the literal `null` produces a compilation artifact
with static type `Null`, whose runtime behavior is to complete with a value of
the _null object_.

_Expression soundness follows from the fact that the _null object_ is an
instance of the type `Null`._

## Numbers

Expression type inference of an integer literal `l`, in context `K`, produces a
compilation artifact `m` with static type `T`, where `m` and `T` are determined
as follows:

- Let `i` be the numeric value of `l`.

- If the type `double` is assignable to `K`, and the type `int` is _not_
  assignable to `K`, then: (TODO(paulberry): assignability is only well defined
  between types; `K` is a type _schema_) (TODO(paulberry): the analyzer accounts
  for strong mode when performing these assignability checks; what is the effect
  of this?) (TODO(paulberry): account for the analyzer's treating `dynamic` and
  `_` as equivalent contexts)

  - Let `T` be the type `double`, and let `m` be a compilation artifact whose
    runtime behavior is to complete with a value that is an instance of `double`
    representing `i`. _Execution soundness follows trivially._

  - If `i` cannot be represented _precisely_ by an instance of `double`, then
    there is a compile-time error. TODO(paulberry): does the analyzer actually
    implement this behavior?

- Otherwise, if `l` is a hexadecimal integer literal, 2<sup>63</sup> ≤ `i` <
  2<sup>64</sup>, and the `int` class is represented as signed 64-bit two's
  complement integers:

  - Let `T` be the type `int`, and let `m` be a compilation artifact whose
    runtime behavior is to complete with a value that is an instance of `int`
    representing `i` - 2<sup>64</sup>. TODO(paulberry): does the CFE actually
    implement this behavior?
    
  - _Execution soundness follows trivially._

- Otherwise:

  - Let `T` be the type `int`, and let `m` be a compilation artifact whose
    runtime behavior is to complete with a value that is an instance of `int`
    representing `i`. _Execution soundness follows trivially._

  - If `i` cannot be represented _precisely_ by an instance of `int`, then there
    is a compile-time error. TODO(paulberry): does the analyzer actually
    implement this behavior?

TODO(paulberry): the CFE's `InferenceVisitorImpl.visitIntLiteral` method doesn't
implement int-to-double logic. What's up with that?

TODO(paulberry): non-normative notes about numeric literals preceded by unary
minus.

## Booleans

Expression type inference of a boolean literal (`true` or `false`) produces a
compilation artifact with static type `bool`, whose runtime behavior is to
complete with the value _true_ or _false_ (respectively).

_Expression soundness follows from the fact that the objects true and false are
both instances of the type `bool`._

## Strings

Expression type inference of a string literal `s` produces a compilation
artifact `m` with static type `String`, where `m` is determined as follows:

- For each _stringInterpolation_ `s_i` inside `s`, in source order:

  - Define `m_i` as follows:
  
    - If `s_i` takes the form '`${`' `e` '`}`':

      - Let `m_i` be the result of performing expression type inference on `e`,
        in context `_`.

    - Otherwise, `s_i` takes the form '`$e`', where `e` is either `this` or an
      identifier that doesn't begin with `$`, so:
    
      - Let `m_i` be the result of performing expression type inference on `e`,
        in context `_`.

  - Let `T_i` be the static type of `m_i`.

  - If `T_i :<! Object` and `T_i` is not `dynamic`, then there is a compile time
    error.

- Let `m` be a compilation artifact whose runtime behavior is as follows:
  
  - For each `i`, in order:
  
    - Execute compilation artifact `m_i`, and let `o_i` be the resulting value.
    
    - Invoke the `toString` method on `o_i`, with no arguments, and let `r_i` be
      the return value. _Note that since both `Object.toString` and
      `Null.toString` are declared with a return type of `String`, it follows
      from return value soundness that `r_i` will have a runtime type of
      `String`)._

  - Concatenate together the `r_i` strings (interspersing with any
    non-interpolation characters in `s`) to produce `r`, an instance of
    `String`.

  - `m` completes with the value `r`. _Expression soundness follows trivially._

## Symbol literal

Expression type inference of a symbol literal `#s` (where `s` may be an
identifier, a sequence of identifiers separated by `.`, an operator, or `void`)
produces a compilation artifact with static type `Symbol`, whose runtime
behavior is to complete with a value that is an instance of `Symbol`,
representing the tokens in `s`.

_Expression soundness follows trivially._

## Collection literals

TODO(paulberry): write this.

### List literal

TODO(paulberry): write this.

### Set or map literal

TODO(paulberry): write this.

## Throw

Expression type inference of a throw expression `throw e_1` produces a
compilation artifact `m` with static type `Never`, where `m` is determined as
follows:

- Let `m_1` be the result of performing expression type inference on `e_1`, in
  context `_`, and then coercing the result to type `Object`.

- Let `m` be a compilation artifact whose runtime behavior is as follows:

  - Execute the compilation artifact `m_1`, and let `o_1` be the resulting
    value.

  - If `o_1` is the _null object_, throw an unspecified
    exception. (TODO(paulberry): in practice it's `_TypeError`. Maybe this is
    specified in the null safety spec?)

  - `m` completes with the exception `o_1`.

_Expression soundness follows from the fact that `m` does not complete with a
value._

## Function expressions

TODO(paulberry): write this.

## This

Expression type inference of the expression `this` produces a compilation
artifact `m` with static type `T`, where `m` and `T` are determined as follows:

- Let `T` be the interface type of the immediately enclosing class, enum, mixin,
  or extension type, or the "on" type of the immediately enclosing extension.
  
- If there is no immediately enclosing class, enum, mixin, extension type, or
  extension, then there is a compile-time error.

- If the expression `this` appears inside a factory constructor, a constructor's
  initializer list, a static method or variable initializer, or in the
  initializing expression of a non-late instance variable, then there is a
  compile-time error.

- Let `m` be a compilation artifact whose runtime behavior is to complete with a
  value that is the target of the current instance member invocation.

_Expression soundness follows from the fact that within a class, enum, mixin, or
extension type having interface type `T`, the target of any instance member
invocation is always an instance of `T`, and within an extension, the target of
any instance member invocation is always an instance of the extension's "on"
type._

## Instance creation

TODO(paulberry): write this.

## Function invocation

TODO(paulberry): write this.

## Function closurization

TODO(paulberry): write this.

## Generic function instantiation

TODO(paulberry): write this.

## Lookup

TODO(paulberry): what goes here? Anything?

## Top level getter invocation

TODO(paulberry): what goes here? Anything?

## Member invocations

TODO(paulberry): what goes here? Anything?

### Index expression

TODO(paulberry): write this.

## Method invocation

TODO(paulberry): write this.

### Cascade expression

TODO(paulberry): this is really weird for this to be here

## Property extraction

TODO(paulberry): reconcile with spec

### Property access

TODO(paulberry): write this.

## Assignment

TODO(paulberry): write this.

## Conditional

TODO(paulberry): write this.

## If-null expressions

TODO(paulberry): split from binary expressions

## Logical boolean expressions

Expression type inference of a logical "and" expression (`e_1 && e_2`) or a
logical "or" expression (`e_1 || e_2`) produces a compilation artifact `m` with
static type `bool`, where `m` is determined as follows:

- Let `m_1` be the result of performing expression type inference on `e_1`, in
  context `bool`, and then coercing the result to type `bool`.

- Let `m_2` be the result of performing expression type inference on `e_2`, in
  context `bool`, and then coercring the result to type `bool`.

- Let `m` be a compilation artifact whose runtime behavior is as follows:

  - Execute compilation artifact `m_1`, and let `o_1` be the resulting value. By
    expression soundness, `o_1` will be an instance of the type `bool`.

  - If the expression is a logical "and" expression and `o_1` is `false`, or the
    expression is a logical "or" expression and `o_1` is `true`, then `m`
    completes with the value `o_1`. _Expression soundness follows trivially._

  - Otherwise, execute the compilation artifact `m_2`, and let `o_2` be the
    resulting value. By expression soundness, `o_2` will be an instance of the type `bool`.
    
  - Then, `m` completes with the value `o_2`. _Expression soundness follows
    trivially._

## Equality

TODO(paulberry): write this.

## User-definable binary operations

TODO(paulberry): write this.

Note: spec splits these into "relational expressions", "bitwise expressions",
"shift", "additive expressions", and "multiplicative expressions".

TODO(paulberry): make sure all analyzer behaviors are covered either here or in
"equality", "logical boolean expressions", or "if-null expressions".

## Unary expressions

TODO(paulberry): write this.

See "prefix expression" in the analyzer

## Await expressions

Expression type inference of an await expression `await e_1`, in context `K`,
produces a compilation artifact `m` with static type `T`, where `m` and `T` are
determined as follows:

- Define `K_1` as follows:

  - If `K` is `FutureOr<S>` or `FutureOr<S>?` for some type schema `S`, then let
    `K_1` be `K`.

  - Otherwise, if `K` is `dynamic`, then let `K_1` be `FutureOr<_>`.
  
  - Otherwise, let `K_1` be `FutureOr<K>`.

- Let `m_1` be the result of performing expression type inference on `e_1`, in
  context `K_1`.

- Let `T_1` be the static type of `m_1`.

- Let `T` be `flatten(T_1)`.

- Let `m` be a compilation artifact whose runtime behavior is as follows:

  - Execute compilation artifact `m_1`, and let `o_1` be the resulting value. _By
    expression soundness, `o_1` will be an instance of the type `T_1`._

  - Define `o_2` as follows:
  
    - If `o_1` is a subtype of `Future<T>`, then let `o_2` be `o_1`.
    
    - Otherwise, let `o_2` be the result of creating a new object using the
      constructor `Future<T>.value()` with `o_1` as its
      argument.
    
      - TODO(paulberry): How do we ensure soundness in the call to
        `Future<T>.value()`? It seems like `o_1` must be an instance of the type
        `T`, where `T` is `flatten(T_1)`. But what we have is that `o_1` is an
        instance of `T_1`.
    
    - _By expression soundness, `o_2` must be an instance of `Future<T>`._
  
  - Pause the stream associated with the innermost enclosing asynchronous
    **for** loop, if any.

  - Suspend the current invocation of the function body immediately enclosing
    the await expression until after `o_2` completes.

  - At some time after `o_2` is completed, control returns to the current
    invocation.
    
  - If `o_2` is completed with an error `x` and stack trace `t`, then `m`
    completes with the exception `x` and stack trace `t`. _Expression soundness
    follows trivially._

  - If `o_2` is completed with an object `v`, then `m` completes with the value
    `v`. _Since `o_2` is an instance of `Future<T>`, by future soundness, `v`
    must be an instance of `T`. Therefore, expression soundness follows
    trivially._

## Postfix expressions

TODO(paulberry): does `!` go grammatically with other postfix expressions?

## Assignable expressions

TODO(paulberry): what goes here? anything? Maybe l-values?

## Lexical lookup

TODO(paulberry): what goes here? anything?

## Identifier reference

TODO(paulberry): what goes here? anything?

## Type test

TODO(paulberry): write this.

## Type cast

TODO(paulberry): write this.

## Augmented expression

TODO(paulberry): write this.

## Augmented invocation

TODO(paulberry): write this.

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

TODO(paulberry): write this.

## Prefixed identifier

TODO(paulberry): split out cases to match spec

## Record literal

TODO(paulberry): write this.

## Rethrow expression

TODO(paulberry): this is spec'ed as a statement.

## Simple identifier

TODO(paulberry): split out cases to match spec?

## Super expression

TODO(paulberry): rework to match spec

## Switch expression

TODO(paulberry): write this.

## Type literal

TODO(paulberry): write this.

# Other things

TODO(paulberry): patterns

TODO(paulberry): statements

TODO(paulberry): elements
