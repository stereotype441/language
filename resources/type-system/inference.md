# Top-level and local type inference

Owner: leafp@google.com

Status: Draft

## CHANGELOG

2022.05.12
  - Define the notions of "constraint solution for a set of type variables" and
    "Grounded constraint solution for a set of type variables".  These
    definitions capture how type inference handles type variable bounds, as well
    as how inferred types become "frozen" once they are fully known.

2019.09.01
  - Fix incorrect placement of left top rule in constraint solving.

2019.09.01
  - Add left top rule to constraint solving.
  - Specify inference constraint solving.

2020.07.20
  - Clarify that some rules are specific to code without/with null safety.
    'Without null safety, ...' respectively 'with null safety, ...' is used
    to indicate such rules, and the remaining text is applicable in both cases.

2020.07.14:
  - Infer return type `void` from context with function literals.

2020.06.04:
  - Make conflict resolution for override inference explicit.

2020.06.02
  - Account for the special treatment of bottom types during function literal
  inference.

2020.05.27
  - Update function literal return type inference to use
    **futureValueTypeSchema**.

2019.12.03:
  - Update top level inference for non-nullability, function expression
    inference.


## Inference overview

Type inference in Dart takes three different forms.  The first is mixin
inference, which is
specified
[elsewhere](https://github.com/dart-lang/language/blob/master/accepted/2.1/super-mixins/mixin-inference.md).
The second and third forms are local type inference and top-level inference.
These two forms of inference are mutually interdependent, and are specified
here.

Top-level inference is the process by which the types of top-level variables and
several kinds of class members are inferred when type annotations are omitted,
based on the types of overridden members and initializing expressions.  Since
some top-level declarations have their types inferred from initializing
expressions, top-level inference involves local type inference as a
sub-procedure.

Local type inference is the process by which the types of local variables and
closure parameters declared without a type annotation are inferred; and by which
missing type arguments to list literals, map literals, set literals, constructor
invocations, and generic method invocations are inferred.


## Top-level inference

Top-level inference derives the type of declarations based on two sources of
information: the types of overridden declarations, and the types of initializing
expressions.  In particular:

1. **Method override inference**
    * If you omit a return type or parameter type from an overridden or
    implemented method, inference will try to fill in the missing type using the
    signature of the methods you are overriding.
2. **Static variable and field inference**
    * If you omit the type of a field, setter, or getter, which overrides a
   corresponding member of a superclass, then inference will try to fill in the
   missing type using the type of the corresponding member of the superclass.
    * Otherwise, declarations of static variables and fields that omit a type
   will be inferred from their initializer if present.

As a general principle, when inference fails it is an error.  Tools are free to
behave in implementation specific ways to provide a graceful user experience,
but with respect to the language and its semantics, programs for which inference
fails are unspecified.

Some broad principles for type inference that the language team has agreed to,
and which this proposal is designed to satisfy:
* Type inference should be free to fail with an error, rather than being
  required to always produce some answer.
* It should not be possible for a programmer to observe a declaration as having
  two different types at difference points in the program (e.g. dynamic for
  recursive uses, but subsequently int).  Some consistent answer (or an error)
  should always be produced.  See the example below for an approach that
  violates this principle.
* The inference for local variables, top-level variables, and fields, should
  either agree or error out.  The same expression should not be inferred
  differently at different syntactic positions.  It’s ok for an expression to be
  inferrable at one level but not at another.
* Obvious types should be inferred.
* Inferred and annotated types should be treated the same.
* As much as possible, there should be a simple intuition for users as to how
  inference proceeds.
* Inference should be as efficient to implement as possible.
* Type arguments should be mostly inferred.

### Top-level inference procedure

For simplicity of specification, inference of method signatures and inference of
signatures of other declaration forms are specified uniformly.  Note however
that method inference never depends on inference for any other form of
declaration, and hence can validly be performed independently before inferring
other declarations.

Because of the possibility of inference dependency cycles between top-level
declarations, the inference procedure relies on the set of *available* variables
(*which are the variables for which a type is known*).  A variable is
*available* iff:
  - The variable was explicitly annotated with a type by the programmer.
  - A type for the variable was previously inferred.

Any variable which is not *available* is said to be *unavailable*.  If the
inference process requires the type of an *unavailable* variable in order to
proceed, it is an error.  **If there is any order of inference of declarations
which avoids such an error, the inference procedure is required to find it**.  A
valid implementation strategy for finding such an order is to explicitly
maintain the set of variables which are in the process of being inferred, and to
then recursively infer the types of any variables which are: required for
inference to proceed, but are not *available*, but are also not in the process
of being inferred.  To see this, note that if the type of a variable `x` which
is in the process of being inferred is required during the process of inferring
the type of a variable `y`, then inferring the type of `x` must have directly or
indirectly required inferring the type of `y`.  Any order of inference of
declarations must either have chosen to infer `x` or `y` first, and in either
case, the type of the other is both required, and *unavailable*, and hence will
be an error.

#### General top-level inference

The general inference procedure is as follows.

- Mark every top level, static or instance declaration (fields, setters,
  getters, constructors, methods) which is completely type annotated (that is,
  which has all parameters, return types and field types explicitly annotated)
  as *available*.
- For each declaration `D` which is not *available*:
  - If `D` is a method, setter or getter declaration with name `x`:
    - If `D` overrides another method, field, setter, or getter
        - Perform override inference on `D`.
        - Record the type of `x` and mark `x` as *available*.
    - Otherwise record the type of `x` as the type obtained by replacing an
      omitted setter return type with `void` and replacing any other omitted
      types with `dynamic`, and mark `x` as *available*.
  - If `D` is a declaration of a top-level variable or a static field
    declaration or an instance field declaration, declaring the name `x`:
    - if `D` overrides another field, setter, or getter
        - Perform override inference on `D`.
        - Record the type of `x` and mark `x` as *available*.
    - Otherwise, if `D` has an initializing expression `e`:
      - Perform local type inference on `e`.
      - Let `T` be the inferred type of `e`, or `dynamic` if the inferred type
        of `e` is a subtype of `Null`.  Record the type of `x` to be `T` and
        mark `x` as *available*.
    - Otherwise record the type of `x` to be `dynamic` and mark `x` as
      *available*.
  - If `D` is a constructor declaration `C(...)` for which one or more of the
    parameters is declared as an initializing formal without an explicit type:
    - Perform top-level inference on each of the fields used as an initializing
      formal for `C`.
    - Record the inferred type of `C`, and mark it as *available*.


#### Override inference

If override inference is performed on a declaration `D`, and any member which is
directly overridden by `D` is not *available*, it is an error.  As noted above,
the inference algorithm is required to find an ordering which avoids such an
error if there is such an ordering.  Note that method override inference is
independent of non-override inference, and hence can be completed prior to the
rest of top level inference if desired.


##### Method override inference

A method `m` of a class `C` is subject to override inference if it is
missing one or more component types of its signature, and one or more of
the direct superinterfaces of `C` has a member named `m` (*that is, `C.m`
overrides one or more declarations*).  Each missing type is filled in with
the corresponding type from the combined member signature `s` of `m` in the
direct superinterfaces of `C`.

A compile-time error occurs if `s` does not exist.  *E.g., one
superinterface could have signature `void m([int])` and another one could
have signature `void m(num)`, such that none of them is most specific.
There may still exist a valid override of both (e.g., `void m([num])`).  In
this situation `C.m` can be declared with a complete signature, it just
cannot use override inference.*

If there is no corresponding parameter in `s` for a parameter of the
declaration of `m` in `C`, it is treated as `dynamic` (*e.g., this occurs
when overriding a one parameter method with a method that takes a second
optional parameter*).

*Note that override inference does not provide other properties of a
parameter than the type. E.g., it does not make a parameter `required`
based on overridden declarations. This property must then be specified
explicitly if needed.*


##### Instance field, getter, and setter override inference

The inferred type of a getter, setter, or field is computed as follows.  Note
that we say that a setter overrides a getter if there is a getter of the same
name in some superclass or interface (explicitly declared or induced by an
instance variable declaration), and similarly for getters overriding setters,
fields, etc.

The return type of a getter, parameter type of a setter or type of a field
which overrides/implements only one or more getters is inferred to be the
return type of the combined member signature of said getter in the direct
superinterfaces.

The return type of a getter, parameter type of a setter or type of a field
which overrides/implements only one or more setters is inferred to be the
parameter type of the combined member signature of said setter in the
direct superinterfaces.

The return type of a getter which overrides/implements both a setter and a
getter is inferred to be the return type of the combined member signature
of said getter in the direct superinterfaces.

The parameter type of a setter which overrides/implements both a setter and
a getter is inferred to be the parameter type of the combined member
signature of said setter in the direct superinterfaces.

The type of a final field which overrides/implements both a setter and a
getter is inferred to be the return type of the combined member signature
of said getter in the direct superinterfaces.

The type of a non-final field which overrides/implements both a setter and
a getter is inferred to be the parameter type of the combined member
signature of said setter in the direct superinterfaces, if this type is the
same as the return type of the combined member signature of said getter in
the direct superinterfaces. If the types are not the same then inference
fails with an error.

Note that overriding a field is addressed via the implicit induced getter/setter
pair (or just getter in the case of a final field).

Note that `late` fields are inferred exactly as non-`late` fields.  However,
unlike normal fields, the initializer for a `late` field may reference `this`.


## Function literal return type inference.

Function literals which are inferred in an empty typing context (see below) are
inferred using the declared type for all of their parameters.  If a parameter
has no declared type, it is treated as if it was declared with type `dynamic`.
Inference for each returned expression in the body of the function literal is
done in an empty typing context (see below).

Function literals which are inferred in an non-empty typing context where the
context type is a function type are inferred as described below.

Each parameter is assumed to have its declared type if present.  If no type is
declared for a parameter and there is a corresponding parameter in the context
type schema with type schema `K`, the parameter is given an inferred type `T`
where `T` is derived from `K` as follows.  If the greatest closure of `K` is `S`
and `S` is a subtype of `Null`, then without null safety `T` is `dynamic`, and
with null safety `T` is `Object?`. Otherwise, `T` is `S`. If there is no
corresponding parameter in the context type schema, the variable is treated as
having type `dynamic`.

The return type of the context function type is used at several points during
inference.  We refer to this type as the **imposed return type
schema**. Inference for each returned or yielded expression in the body of the
function literal is done using a context type derived from the imposed return
type schema `S` as follows:
  - If the function expression is neither `async` nor a generator, then the
    context type is `S`.
  - If the function expression is declared `async*` and `S` is of the form
    `Stream<S1>` for some `S1`, then the context type is `S1`.
  - If the function expression is declared `sync*` and `S` is of the form
    `Iterable<S1>` for some `S1`, then the context type is `S1`.
  - Otherwise, without null safety, the context type is `FutureOr<flatten(T)>`
    where `T` is the imposed return type schema; with null safety, the context
    type is `FutureOr<futureValueTypeSchema(S)>`.

The function **futureValueTypeSchema** is defined as follows:

- **futureValueTypeSchema**(`S?`) = **futureValueTypeSchema**(`S`), for all `S`.
- **futureValueTypeSchema**(`S*`) = **futureValueTypeSchema**(`S`), for all `S`.
- **futureValueTypeSchema**(`Future<S>`) = `S`, for all `S`.
- **futureValueTypeSchema**(`FutureOr<S>`) = `S`, for all `S`.
- **futureValueTypeSchema**(`void`) = `void`.
- **futureValueTypeSchema**(`dynamic`) = `dynamic`.
- **futureValueTypeSchema**(`_`) = `_`.
- Otherwise, for all `S`, **futureValueTypeSchema**(`S`) = `Object?`.

_Note that it is a compile-time error unless the return type of an asynchronous
non-generator function is a supertype of `Future<Never>`, which means that
the last case will only be applied when `S` is `Object` or a top type._

In order to infer the return type of a function literal, we first infer the
**actual returned type** of the function literal.

The actual returned type of a function literal with an expression body is the
inferred type of the expression body, using the local type inference algorithm
described below with a typing context as computed above.

The actual returned type of a function literal with a block body is computed as
follows.  Let `T` be `Never` if every control path through the block exits the
block without reaching the end of the block, as computed by the **definite
completion** analysis specified elsewhere.  Let `T` be `Null` if any control
path reaches the end of the block without exiting the block, as computed by the
**definite completion** analysis specified elsewhere.  Let `K` be the typing
context for the function body as computed above from the imposed return type
schema.
  - For each `return e;` statement in the block, let `S` be the inferred type of
    `e`, using the local type inference algorithm described below with typing
    context `K`, and update `T` to be `UP(flatten(S), T)` if the enclosing
    function is `async`, or `UP(S, T)` otherwise.
  - For each `return;` statement in the block, update `T` to be `UP(Null, T)`.
  - For each `yield e;` statement in the block, let `S` be the inferred type of
    `e`, using the local type inference algorithm described below with typing
    context `K`, and update `T` to be `UP(S, T)`.
  - If the enclosing function is marked `sync*`, then for each `yield* e;`
    statement in the block, let `S` be the inferred type of `e`, using the
    local type inference algorithm described below with a typing context of
    `Iterable<K>`; let `E` be the type such that `Iterable<E>` is a
    super-interface of `S`; and update `T` to be `UP(E, T)`.
  - If the enclosing function is marked `async*`, then for each `yield* e;`
    statement in the block, let `S` be the inferred type of `e`, using the
    local type inference algorithm described below with a typing context of
    `Stream<K>`; let `E` be the type such that `Stream<E>` is a super-interface
    of `S`; and update `T` to be `UP(E, T)`.

The **actual returned type** of the function literal is the value of `T` after
all `return` and `yield` statements in the block body have been considered.

Let `T` be the **actual returned type** of a function literal as computed above.
Let `R` be the greatest closure of the typing context `K` as computed above.

With null safety: if `R` is `void`, or the function literal is marked `async`
and `R` is `FutureOr<void>`, let `S` be `void` (without null-safety: no special
treatment is applicable to `void`).

Otherwise, if `T <: R` then let `S` be `T`.  Otherwise, let `S` be `R`.  The
inferred return type of the function literal is then defined as follows:

  - If the function literal is marked `async` then the inferred return type is
    `Future<flatten(S)>`.
  - If the function literal is marked `async*` then the inferred return type is
    `Stream<S>`.
  - If the function literal is marked `sync*` then the inferred return type is
    `Iterable<S>`.
  - Otherwise, the inferred return type is `S`.

## Local return type inference.

Without null safety, a local function definition which has no explicit return
type is subject to the same return type inference as a function expression with
no typing context.  During inference of the function body, any recursive calls
to the function are treated as having return type `dynamic`.

With null safety, local function body inference is changed so that the local
function name is not considered *available* for inference while performing
inference on the body.  As a result, any recursive calls to the function for
which the result type is required for inference to complete will no longer be
treated as having return type `dynamic`, but will instead result in an inference
failure.

## Local type inference

When type annotations are omitted on local variable declarations and function
literals, or when type arguments are omitted from literal expressions,
constructor invocations, or generic function invocations, then local type
inference is used to fill in the missing type information.  Local type inference
is also used as part of top-level inference as described above, in order to
infer types for initializer expressions.  In order to uniformly treat use of
local type inference in top-level inference and in method body inference, it is
defined with respect to a set of *available* variables as defined above.  Note
however that top-level inference never depends on method body inference, and so
method body inference can be performed as a subsequent step.  If this order of
inference is followed, then method body inference should never fail due to a
reference to an *unavailable* variable, since local variable declarations can
always be traversed in an appropriate statically pre-determined order.

### Types

We define inference using types as defined in
the
[informal specification of subtyping](https://github.com/dart-lang/language/blob/master/resources/type-system/subtyping.md),
with the same meta-variable conventions.  Specifically:

The meta-variables `X`, `Y`, and `Z` range over type variables.

The meta-variable `L` ranges over lists or sets of type variables.

The meta-variables `T`, `S`, `U`, and `V` range over types.

The meta-variable `C` ranges over classes.

The meta-variable `B` ranges over types used as bounds for type variables.

For convenience, we generally write function types with all named parameters in
an unspecified canonical order, and similarly for the named fields of record
types.  In all cases unless otherwise specifically called out, order of named
parameters and fields is semantically irrelevant: any two types with the same
named parameters (named fields, respectively) are considered the same type.

Similarly, function and method invocations with named arguments and records with
named field entries are written with their named entries in an unspecified
canonical order and position.  Unless otherwise called out, position of named
entries is semantically irrelevant, and all invocations and record literals with
the same named entries (possibly in different orders or locations) and the same
positional entries are considered equivalent.

### Type schemas

Local type inference uses a notion of `type schema`, which is a slight
generalization of the normal Dart type syntax.  The grammar of Dart types is
extended with an additional construct `_` which can appear anywhere that a type
is expected.  The intent is that `_` represents a component of a type which has
not yet been fixed by inference.  Type schemas cannot appear in programs or in
final inferred types: they are purely part of the specification of the local
inference process.  In this document, we sometimes refer to `_` as "the unknown
type".

It is an invariant that a type schema will never appear as the right hand
component of a promoted type variable `X & T`.

The meta-variables `P` and `Q` range over type schemas.

### Variance

We define the notion of the covariant, contravariance, and invariant occurrences
of a type `T` in another type `S` inductively as follows.  Note that this
definition of variance treats type aliases transparently: that is, the variance
of a type which is used as an argument to a type alias is computed by first
expanding the type alias (substituting actuals for formals) and then computing
variance on the result.  This means that the only invariant positions in any
type (given the current Dart type system) are in the bounds of generic function
types.

The covariant occurrences of a type (schema) `T` in another type (schema) `S` are:
  - if `S` and `T` are the same type,
    - `S` is a covariant occurrence of `T`.
  - if `S` is `Future<U>`
    - the covariant occurrences of `T` in `U`
  - if `S` is `FutureOr<U>`
    - the covariant occurrencs of `T` in `U`
  - if `S` is an interface type `C<T0, ..., Tk>`
    - the union of the covariant occurrences of `T` in `Ti` for `i` in `0, ..., k`
  - if `S` is `U Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn, [Tn+1 xn+1, ..., Tm xm])`,
      the union of:
    - the covariant occurrences of `T` in `U`
    - the contravariant occurrences of `T` in `Ti` for `i` in `0, ..., m`
  - if `S` is `U Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn, {Tn+1 xn+1, ..., Tm xm})`
      the union of:
    - the covariant occurrences of `T` in `U`
    - the contravariant occurrences of `T` in `Ti` for `i` in `0, ..., m`
  - if `S` is `(T0, ..., Tn, {Tn+1 xn+1, ..., Tm xm})`,
    - the covariant occurrences of `T` in `Ti` for `i` in `0, ..., m`

The contravariant occurrences of a type `T` in another type `S` are:
  - if `S` is `Future<U>`
    - the contravariant occurrences of `T` in `U`
  - if `S` is `FutureOr<U>`
    - the contravariant occurrencs of `T` in `U`
  - if `S` is an interface type `C<T0, ..., Tk>`
    - the union of the contravariant occurrences of `T` in `Ti` for `i` in `0, ..., k`
  - if `S` is `U Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn, [Tn+1 xn+1, ..., Tm xm])`,
      the union of:
    - the contravariant occurrences of `T` in `U`
    - the covariant occurrences of `T` in `Ti` for `i` in `0, ..., m`
  - if `S` is `U Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn, {Tn+1 xn+1, ..., Tm xm})`
      the union of:
    - the contravariant occurrences of `T` in `U`
    - the covariant occurrences of `T` in `Ti` for `i` in `0, ..., m`
  - if `S` is `(T0, ..., Tn, {Tn+1 xn+1, ..., Tm xm})`,
    - the contravariant occurrences of `T` in `Ti` for `i` in `0, ..., m`

The invariant occurrences of a type `T` in another type `S` are:
  - if `S` is `Future<U>`
    - the invariant occurrences of `T` in `U`
  - if `S` is `FutureOr<U>`
    - the invariant occurrencs of `T` in `U`
  - if `S` is an interface type `C<T0, ..., Tk>`
    - the union of the invariant occurrences of `T` in `Ti` for `i` in `0, ..., k`
  - if `S` is `U Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn, [Tn+1 xn+1, ..., Tm xm])`,
      the union of:
    - the invariant occurrences of `T` in `U`
    - the invariant occurrences of `T` in `Ti` for `i` in `0, ..., m`
    - all occurrences of `T` in `Bi` for `i` in `0, ..., k`
  - if `S` is `U Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn, {Tn+1 xn+1, ..., Tm xm})`
      the union of:
    - the invariant occurrences of `T` in `U`
    - the invariant occurrences of `T` in `Ti` for `i` in `0, ..., m`
    - all occurrences of `T` in `Bi` for `i` in `0, ..., k`
  - if `S` is `(T0, ..., Tn, {Tn+1 xn+1, ..., Tm xm})`,
    - the invariant occurrences of `T` in `Ti` for `i` in `0, ..., m`

### Type variable elimination (least and greatest closure of a type)

Given a type `S` and a set of type variables `L` consisting of the variables
`X0, ..., Xn`, we define the least and greatest closure of `S` with respect to
`L` as follows.

We define the least closure of a type `M` with respect to a set of type
variables `X0, ..., Xn` to be `M` with every covariant occurrence of `Xi`
replaced with `Never`, and every contravariant occurrence of `Xi` replaced with
`Object?`.  The invariant occurrences are treated as described explicitly below.

We define the greatest closure of a type `M` with respect to a set of type
variables `X0, ..., Xn` to be `M` with every contravariant occurrence of `Xi`
replaced with `Never`, and every covariant occurrence of `Xi` replaced with
`Object?`. The invariant occurrences are treated as described explicitly below.

- If `S` is `X` where `X` is in `L`
  - The least closure of `S` with respect to `L` is `Never`
  - The greatest closure of `S` with respect to `L` is `Object?`
- If `S` is a base type (or in general, if it does not contain any variable from
  `L`)
  - The least closure of `S` is `S`
  - The greatest closure of `S` is `S`
- if `S` is `T?`
  - The least closure of `S` with respect to `L` is `U?` where `U` is the
    least closure of `T` with respect to `L`
  - The greatest closure of `S` with respect to `L` is `U?` where `U` is
    the greatest closure of `T` with respect to `L`
- if `S` is `Future<T>`
  - The least closure of `S` with respect to `L` is `Future<U>` where `U` is the
    least closure of `T` with respect to `L`
  - The greatest closure of `S` with respect to `L` is `Future<U>` where `U` is
    the greatest closure of `T` with respect to `L`
- if `S` is `FutureOr<T>`
  - The least closure of `S` with respect to `L` is `FutureOr<U>` where `U` is the
    least closure of `T` with respect to `L`
  - The greatest closure of `S` with respect to `L` is `FutureOr<U>` where `U` is
    the greatest closure of `T` with respect to `L`
- if `S` is an interface type `C<T0, ..., Tk>`
  - The least closure of `S` with respect to `L` is `C<U0, ..., Uk>` where `Ui`
    is the least closure of `Ti` with respect to `L`
  - The greatest closure of `S` with respect to `L` is `C<U0, ..., Uk>` where
    `Ui` is the greatest closure of `Ti` with respect to `L`
- if `S` is `T Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn,
  [Tn+1 xn+1, ..., Tm xm])` and no type variable in `L` occurs in any of the `Bi`:
  - The least closure of `S` with respect to `L` is `U Function<X0 extends B0,
  ..., Xk extends Bk>(U0 x0, ..., Un1 xn, [Un+1 xn+1, ..., Um xm])` where:
    - `U` is the least closure of `T` with respect to `L`
    - `Ui` is the greatest closure of `Ti` with respect to `L`
    - with the usual capture avoiding requirement that the `Xi` do not appear in
  `L`.
  - The greatest closure of `S` with respect to `L` is `U Function<X0 extends B0,
  ..., Xk extends Bk>(U0 x0, ..., Un1 xn, [Un+1 xn+1, ..., Um xm])` where:
    - `U` is the greatest closure of `T` with respect to `L`
    - `Ui` is the least closure of `Ti` with respect to `L`
    - with the usual capture avoiding requirement that the `Xi` do not appear in
  `L`.
- if `S` is `T Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn,
  {Tn+1 xn+1, ..., Tm xm})` and no type variable in `L` occurs in any of the `Bi`:
  - The least closure of `S` with respect to `L` is `U Function<X0 extends B0,
  ..., Xk extends Bk>(U0 x0, ..., Un1 xn, {Un+1 xn+1, ..., Um xm})` where:
    - `U` is the least closure of `T` with respect to `L`
    - `Ui` is the greatest closure of `Ti` with respect to `L`
    - with the usual capture avoiding requirement that the `Xi` do not appear in
  `L`.
  - The greatest closure of `S` with respect to `L` is `U Function<X0 extends B0,
  ..., Xk extends Bk>(U0 x0, ..., Un1 xn, {Un+1 xn+1, ..., Um xm})` where:
    - `U` is the greatest closure of `T` with respect to `L`
    - `Ui` is the least closure of `Ti` with respect to `L`
    - with the usual capture avoiding requirement that the `Xi` do not appear in
  `L`.
- if `S` is `T Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn,
    [Tn+1 xn+1, ..., Tm xm])` or `T Function<X0 extends B0, ..., Xk extends Bk>(T0 x0, ..., Tn xn,
{Tn+1 xn+1, ..., Tm xm})`and `L` contains any free type variables
  from any of the `Bi`:
  - The least closure of `S` with respect to `L` is `Never`
  - The greatest closure of `S` with respect to `L` is `Function`
- if `S` is `(T0 x0, ..., Tn xn,  {Tn+1 xn+1, ..., Tm xm})`:
  - The least closure of `S` with respect to `L` is `(U0 x0, ..., Un1 xn, {Un+1
    xn+1, ..., Um xm})` where:
    - `Ui` is the least closure of `Ti` with respect to `L`
  - The greatest closure of `S` with respect to `L` is `(U0 x0, ..., Un1 xn,
    {Un+1 xn+1, ..., Um xm})` where:
    - `Ui` is the greatest closure of `Ti` with respect to `L`


### Type schema elimination (least and greatest closure of a type schema)

We define the greatest and least closure of a type schema `P` with respect to
`_` in the same way as we define the greatest and least closure with respect to
a type variable `X` above, where `_` is treated as a type variable in the set
`L`.

Note that the least closure of a type schema is always a subtype of any type
which matches the schema, and the greatest closure of a type schema is always a
supertype of any type which matches the schema.


## Upper bound

We write `UP(T0, T1)` for the upper bound of `T0` and `T1`and `DOWN(T0, T1)` for
the lower bound of `T0` and `T1`.  This extends to type schema as follows:
  - We add the axiom that `UP(T, _) == T` and the symmetric version.
  - We replace all uses of `T1 <: T2` in the `UP` algorithm by `S1 <: S2` where
  `Si` is the least closure of `Ti` with respect to `_`.
  - We add the axiom that `DOWN(T, _) == T` and the symmetric version.
  - We replace all uses of `T1 <: T2` in the `DOWN` algorithm by `S1 <: S2` where
  `Si` is the greatest closure of `Ti` with respect to `_`.

The following example illustrates the effect of taking the least/greatest
closure in the subtyping algorithm.

```
class C<X> {
  C(void Function(X) x);
}
T check<T>(C<List<T>> f) {
  return null as T;
}
void test() {
  var x = check(C((List<int> x) {})); // Should infer `int` for `T`
  String s = x; // Should be an error, `T` should be int.
}
```

## Type constraints

Type constraints take the form `Pb <: X <: Pt` for type schemas `Pb` and `Pt`
and type variables `X`.  Constraints of that form indicate a requirement that
any choice that inference makes for `X` must satisfy both `Tb <: X` and `X <:
Tt` for some type `Tb` which satisfies schema `Pb`, and some type `Tt` which
satisfies schema `Pt`.  Constraints in which `X` appears free in either `Pb` or
`Pt` are ill-formed.


### Closure of type constraints

The closure of a type constraint `Pb <: X <: Pt` with respect to a set of type
variables `L` is the subtype constraint `Qb <: X :< Qt` where `Qb` is the
greatest closure of `Pb` with respect to `L`, and `Qt` is the least closure of
`Pt` with respect to `L`.

Note that the closure of a type constraint implies the original constraint: that
is, any solution to the original constraint that is closed with respect to `L`,
is a solution to the new constraint.

The motivation for these operations is that constraint generation may produce a
constraint on a type variable from an outer scope (say `S`) that refers to a
type variable from an inner scope (say `T`).  For example, ` <T>(T) -> List<T> <:
<T>(T) -> S ` constrains `List<T>` to be a subtype of `S`.  But this
constraint is ill-formed outside of the scope of `T`, and hence if inference
requires this constraint to be generated and moved out of the scope of `T`, we
must approximate the constraint to the nearest constraint which does not mention
`T`, but which still implies the original constraint.  Choosing the greatest
closure of `List<T>` (i.e. `List<Object?>`) as the new supertype constraint on
`S` results in the constraint `List<Object?> <: S`, which implies the original
constraint.

Example:
```dart
class C<T> {
  C(T Function<X>(X x));
}

List<Y> foo<Y>(Y y) => [y];

void main() {
  var x = C(foo); // Should infer C<List<Object?>>
}
```

### Constraint solving

Inference works by collecting lists of type constraints for type variables of
interest.  We write a list of constraints using the meta-variable `C`, and use
the meta-variable `c` for a single constraint.  Inference relies on various
operations on constraint sets.

#### Merge of a constraint set

The merge of constraint set `C` for a type variable `X` is a type constraint `Mb
<: X <: Mt` defined as follows:
  - let `Mt` be the lower bound of the `Mti` such that `Mbi <: X <: Mti` is in
      `C` (and `_` if there are no constraints for `X` in `C`)
  - let `Mb` be the upper bound of the `Mbi` such that `Mbi <: X <: Mti` is in
      `C` (and `_` if there are no constraints for `X` in `C`)

Note that the merge of a constraint set `C` summarizes all of the constraints in
the set in the sense that any solution for the merge is a solution for each
constraint individually.

#### Constraint solution for a type variable

The constraint solution for a type variable `X` with respect to a constraint set
`C` is the type schema defined as follows:
  - let `Mb <: X <: Mt` be the merge of `C` with respect to `X`.
  - If `Mb` is known (that is, it does not contain `_`) then the solution is
    `Mb`
  - Otherwise, if `Mt` is known (that is, it does not contain `_`) then the
    solution is `Mt`
  - Otherwise, if `Mb` is not `_` then the solution is `Mb`
  - Otherwise the solution is `Mt`

Note that the constraint solution is a type schema, and hence may contain
occurences of the unknown type.

#### Constraint solution for a set of type variables

The constraint solution for a set of type variables `{X0, ..., Xn}` with respect
to a constraint set `C` and partial solution `{T0, ..., Tn}`, is defined to be
the set of type schemas `{U0, ..., Un}` such that:
  - If `Ti` is known (that is, does not contain `_`), then `Ui = Ti`.  _(Note
    that the upcoming "variance" feature will relax this rule so that it only
    applies to type variables without an explicitly declared variance.)_
  - Otherwise, let `Vi` be the constraint solution for the type variable `Xi`
    with respect to the constraint set `C`.
  - If `Vi` is not known (that is, it contains `_`), then `Ui = Vi`.
  - Otherwise, if `Xi` does not have an explicit bound, then `Ui = Vi`.
  - Otherwise, let `Bi` be the bound of `Xi`.  Then, let `Bi'` be the type
    schema formed by substituting type schemas `{U0, ..., Ui-1, Ti, ..., Tn}` in
    place of the type variables `{X0, ..., Xn}` in `Bi`.  _(That is, we
    substitute `Uj` for `Xj` when `j < i` and `Tj` for `Xj` when `j >= i`)._
    Then `Ui` is the constraint solution for the type variable `Xi` with respect
    to the constraint set `C + (X <: Bi')`.

_This definition can perhaps be better understood in terms of the practical
consequences it has on type inference:_
  - _Once type inference has determined a known type for a type variable (that
    is, a type that does not contain `_`), that choice is frozen and is not
    affected by later type inference steps.  (Type inference accomplishes this
    by passing in any frozen choices as part of the partial solution)._
  - _The bound of a type variable is only included as a constraint when the
    choice of type for that type variable is about to be frozen._
  - _During each round of type inference, type variables are inferred left to
    right.  If the bound of one type variable refers to one or more type
    variables, then at the time the bound is included as a constraint, the type
    variables it refers to are assumed to take on the type schemas most recently
    assigned to them by type inference._

#### Grounded constraint solution for a type variable

The grounded constraint solution for a type variable `X` with respect to a
constraint set `C` is define as follows:
  - let `Mb <: X <: Mt` be the merge of `C` with respect to `X`.
  - If `Mb` is known (that is, it does not contain `_`) then the solution is
    `Mb`
  - Otherwise, if `Mt` is known (that is, it does not contain `_`) then the
    solution is `Mt`
  - Otherwise, if `Mb` is not `_` then the solution is the least closure of
    `Mb` with respect to `_`
  - Otherwise the solution is the greatest closure of `Mt` with respect to `_`.

Note that the grounded constraint solution is a type, and hence may not contain
occurences of the unknown type.

#### Grounded constraint solution for a set of type variables

The grounded constraint solution for a set of type variables `{X0, ..., Xn}`
with respect to a constraint set `C`, with partial solution `{T0, ..., Tn}`, is
defined to be the set of types `{U0, ..., Un}` such that:
  - If `Ti` is known (that is, does not contain `_`), then `Ui = Ti`.  _(Note
    that the upcoming "variance" feature will relax this rule so that it only
    applies to type variables without an explicitly declared variance.)_
  - Otherwise, if `Xi` does not have an explicit bound, then `Ui` is the
    grounded constraint solution for the type variable `Xi` with respect to the
    constraint set `C`.
  - Otherwise, let `Bi` be the bound of `Xi`.  Then, let `Bi'` be the type
    schema formed by substituting type schemas `{U0, ..., Ui-1, Ti, ..., Tn}` in
    place of the type variables `{X0, ..., Xn}` in `Bi`.  _(That is, we
    substitute `Uj` for `Xj` when `j < i` and `Tj` for `Xj` when `j >= i`)._
    Then `Ui` is the grounded constraint solution for the type variable `Xi`
    with respect to the constraint set `C + (X <: Bi')`.

_This definition parallels the definition of the (non-grounded) constraint
solution for a set of type variables._

#### Constrained type variables

A constraint set `C` constrains a type variable `X` if there exists a `c` in `C`
of the form `Pb <: X <: Pt` where either `Pb` or `Pt` is not `_`.

A constraint set `C` partially constrains a type variable `X` if the constraint
solution for `X` with respect to `C` is a type schema (that is, it contains
`_`).

A constraint set `C` fully constrains a type variable `X` if the constraint
solution for `X` with respect to `C` is a proper type (that is, it does not
contain `_`).

## Subtype constraint generation

Subtype constraint generation is an operation on two type schemas `P` and `Q`
and a list of type variables `L`, producing a list of subtype
constraints `C`.

We write this operation as a relation as follows:

```
P <# Q [L] -> C
```

where `P` and `Q` are type schemas, `L` is a list of type variables `X0, ...,
Xn`, and `C` is a list of subtype and supertype constraints on the `Xi`.

This relation can be read as "`P` is a subtype match for `Q` with respect to the
list of type variables `L` under constraints `C`".  Not all schemas `P` and `Q`
are in the relation: the relation may fail to hold, which is distinct from the
relation holding but producing no constraints.

By invariant, at any point in constraint generation, only one of `P` and `Q` may
be a type schema (that is, contain `_`), only one of `P` and `Q` may contain any
of the `Xi`, and neither may contain both.  That is, constraint generation is a
relation on type-schema/type pairs and type/type-schema pairs, only the type
element of which may refer to the `Xi`.  The presentation below does not
explicitly track which side of the relation currently contains a schema and
which currently contains the variables being solved for, but it does at one
point rely on being able to recover this information.  This information can be
tracked explicitly in the relation by (for example) adding a boolean to the
relation which is negated at contravariant points.


### Notes:

- For convenience, ordering matters in this presentation: where any two clauses
  overlap syntactically, the first match is preferred.
- This presentation is assuming appropriate well-formedness conditions on the
  input types (e.g. non-cyclic class hierarchies)

### Syntactic notes:

- `C0 + C1` is the concatenation of constraint lists `C0` and `C1`.

### Rules

For two type schemas `P` and `Q`, a set of type variables `L`, and a set of
constraints `C`, we define `P <# Q [L] -> C` via the following algorithm.

Note that the order matters: we consider earlier clauses first.

Note that the rules are written assuming that if the conditions of a particular
case (including the sub-clauses) fail to hold, then they "fall through" to try
subsequent cluases except in the case that a subclause is prefixed with "Only
if", in which case a failure of the prefixed clause implies that no subsequent
clauses need be tried.

- If `P` is `_` then the match holds with no constraints.
- If `Q` is `_` then the match holds with no constraints.
- If `P` is a type variable `X` in `L`, then the match holds:
  - Under constraint `_ <: X <: Q`.
- If `Q` is a type variable `X` in `L`, then the match holds:
  - Under constraint `P <: X <: _`.
- If `P` and `Q` are identical types, then the subtype match holds under no
  constraints.
- If `P` is a legacy type `P0*` then the match holds under constraint set `C`:
  - Only if `P0` is a subtype match for `Q` under constraint set `C`.
- If `Q` is a legacy type `Q0*` then the match holds under constraint set `C`:
  - If `P` is `dynamic` or `void` and `P` is a subtype match for `Q0` under
    constraint set `C`.
  - Or if `P` is a subtype match for `Q0?` under constraint set `C`.
- If `Q` is `FutureOr<Q0>` the match holds under constraint set `C`:
  - If `P` is `FutureOr<P0>` and `P0` is a subtype match for `Q0` under
    constraint set `C`.
  - Or if `P` is a subtype match for `Future<Q0>` under **non-empty** constraint set
    `C`
  - Or if `P` is a subtype match for `Q0` under constraint set `C`
  - Or if `P` is a subtype match for `Future<Q0>` under **empty** constraint set
    `C`
- If `Q` is `Q0?` the match holds under constraint set `C`:
  - If `P` is `P0?` and `P0` is a subtype match for `Q0` under
    constraint set `C`.
  - Or if `P` is `dynamic` or `void` and `Object` is a subtype match for `Q0`
    under constraint set `C`.
  - Or if `P` is a subtype match for `Q0` under **non-empty** constraint set
    `C`.
  - Or if `P` is a subtype match for `Null` under constraint set `C`.
  - Or if `P` is a subtype match for `Q0` under **empty** constraint set
    `C`.
- If `P` is `FutureOr<P0>` the match holds under constraint set `C1 + C2`:
  - If `Future<P0>` is a subtype match for `Q` under constraint set `C1`
  - And if `P0` is a subtype match for `Q` under constraint set `C2`
- If `P` is `P0?` the match holds under constraint set `C1 + C2`:
  - If `P0` is a subtype match for `Q` under constraint set `C1`
  - And if `Null` is a subtype match for `Q` under constraint set `C2`
- If `Q` is `dynamic`, `Object?`, or `void` then the match holds under no
  constraints.
- If `P` is `Never` then the match holds under no constraints.
- If `Q` is `Object`, then the match holds under no constraints:
  - Only if `P` is non-nullable.
- If `P` is `Null`, then the match holds under no constraints:
  - Only if `Q` is nullable.

- If `P` is a type variable `X` with bound `B` (or a promoted type variable `X &
  B`), the match holds with constraint set `C`:
  - If `B` is a subtype match for `Q` with constraint set `C`
    - Note that we have already eliminated the case that `X` is a variable in
      `L`.

- If `P` is `C<M0, ..., Mk>` and `Q` is `C<N0, ..., Nk>`, and the corresponding
  type parameters declared by the class `C` are `T0, ..., Tk`, then the match
  holds under constraints `C0 + ... + Ck`, if for each `i`:
  - If `Ti` is a **covariant** type variable, and `Mi` is a subtype match for
    `Ni` with respect to `L` under constraints `Ci`,
  - Or `Ti` is a **contravariant** type variable, `Ni` is a subtype match for
    `Mi` with respect to `L` under constraints `Ci`,
  - Or `Ti` is an **invariant** type variable, and:
    - `Mi` is a subtype match for `Ni` with respect to `L` under constraints
      `Ci0`,
    - And `Ni` is a subtype match for `Mi` with respect to `L` under constraints
      `Ci1`,
    - And `Ci` is `Ci0 + Ci1`.

- If `P` is `C0<M0, ..., Mk>` and `Q` is `C1<N0, ..., Nj>` then the match holds
with respect to `L` under constraints `C`:
  - If `C1<B0, ..., Bj>` is a superinterface of `C0<M0, ..., Mk>` and `C1<B0,
..., Bj>` is a subtype match for `C1<N0, ..., Nj>` with respect to `L` under
constraints `C`.
  - Or `R<B0, ..., Bj>` is one of the interfaces implemented by `P<M0, ..., Mk>`
(considered in lexical order) and `R<B0, ..., Bj>` is a subtype match for `Q<N0,
..., Nj>` with respect to `L` under constraints `C`.
  - Or `R<B0, ..., Bj>` is a mixin into `P<M0, ..., Mk>` (considered in lexical
order) and `R<B0, ..., Bj>` is a subtype match for `Q<N0, ..., Nj>` with respect
to `L` under constraints `C`.

- A type `P` is a subtype match for `Function` with respect to `L` under no constraints:
  - If `P` is a function type.

- A function type `(M0,..., Mn, [M{n+1}, ..., Mm]) -> R0` is a subtype match for
  a function type `(N0,..., Nk, [N{k+1}, ..., Nr]) -> R1` with respect to `L`
  under constraints `C0 + ... + Cr + C`
  - If `R0` is a subtype match for a type `R1` with respect to `L` under
  constraints `C`:
  - If `n <= k` and `r <= m`.
  - And for `i` in `0...r`, `Ni` is a subtype match for `Mi` with respect to `L`
  under constraints `Ci`.
- Function types with named parameters are treated analogously to the positional
  parameter case above.

- A generic function type `<T0 extends B00, ..., Tn extends B0n>F0` is a subtype
match for a generic function type `<S0 extends B10, ..., Sn extends B1n>F1` with
respect to `L` under constraint set `C2`
  - If `B0i` is a subtype match for `B1i` with constraint set `Ci0`
  - And `B1i` is a subtype match for `B0i` with constraint set `Ci1`
  - And `Ci2` is `Ci0 + Ci1`
  - And `Z0...Zn` are fresh variables with bounds `B20, ..., B2n`
    - Where `B2i` is `B0i[Z0/T0, ..., Zn/Tn]` if `P` is a type schema
    - Or `B2i` is `B1i[Z0/S0, ..., Zn/Sn]` if `Q` is a type schema
      - In other words, we choose the bounds for the fresh variables from
        whichever of the two generic function types is a type schema and does
        not contain any variables from `L`.
  - And `F0[Z0/T0, ..., Zn/Tn]` is a subtype match for `F1[Z0/S0, ..., Zn/Sn]`
with respect to `L` under constraints `C0`
  - And `C1` is  `C02 + ... + Cn2 + C0`
  - And `C2` is `C1` with each constraint replaced with its closure with respect
    to `[Z0, ..., Zn]`.

- A type `P` is a subtype match for `Record` with respect to `L` under no constraints:
  - If `P` is a record type or `Record`.

- A record type `(M0,..., Mk, {M{k+1} d{k+1}, ..., Mm dm])` is a subtype match
  for a record type `(N0,..., Nk, {N{k+1} d{k+1}, ..., Nm dm])` with respect
  to `L` under constraints `C0 + ... + Cm`
  - If for `i` in `0...m`, `Mi` is a subtype match for `Ni` with respect to `L`
  under constraints `Ci`.

### Dynamic Boundedness

TODO(paulberry): where should this section go?

A type `T` is considered to be _dynamic bounded_ if one of the following is true:

- `T` is `dynamic`.

- `T` is a type variable `X` whose bound is dynamic bounded.

- `T` is a promoted type variable `X & U`, where `U` is dynamic bounded.

## Local type inference procedure

Within a method body or top-level initializing expression, the type inferred for
a local variable, closure parameter, or type argument may depend on:

- The types inferred for local variables appearing earlier in control flow.

- Type promotions determined by the [flow analysis][] of statements and
  expressions appearing earlier in control flow.

- Types that appear in syntactic elements that enclose the local variable,
  closure parameter, or type argument, or that were applied to those syntactic
  elements by top level inference.

[flow anaylsis]: https://github.com/dart-lang/language/blob/main/resources/type-system/flow-analysis.md

For this reason, local type inference is described procedurally, using a
recursive algorithm. Each recursion step is applied to a single syntactic
element (_argumentPart_, statement, expression, or collection element), and is
known as _inferring_ that structure. Each recursion step produces, as output, a
compilation artifact, designated `m`, abstractly representing the code produced
by the compiler for that syntactic element. Many recursion steps accept
additional inputs.

### Compilation Artifacts

In this document, compilation artifacts are described using a syntax that is
similar to the standard syntax of Dart programs, but with the following
differences:

TODO(paulberry): describe in more detail

- The compilation artifact associated with an expression (known as an
  _expression artifact_) also contains a static type `T`. This is typically
  written by appending the suffix `:: T` to the syntax for expressions. _(For
  example, the compilation artifact associated with the boolean literal `true`
  is `true :: bool`.)_

- The compilation artifact associated with an _argumentPart_ (known as an
  _argument part artifact_) also contains a return type `R`. This is typically
  written by appending the suffix `::> R` to the syntax for
  _argumentPart_. _Examples of argument part artifacts are `() ::> int`,
  `<bool>(1 :: int, 'x' :: String) ::> double`, and `(foo: null :: Null) ::>
  void`._

- The compilation artifact `(let bs in m) :: T` is an expression artifact
  representing a "let" expression. It functions as follows:
  
  - `bs` is a possibly empty sequence of bindings, where each binding takes one
    of the following forms:
    
    - A simple binding: `id_i = m_i :: T_i`, where `id_i` is an identifier and
      `m_i` is an expression artifact.
    
    - A guarded binding: `id_i = m_i :: T_i if (guard_i)`, where `id_i` is an
      identifier and `m_i` and `guard_i` are expression artifacts.

  - Evaluation of this expression artifact performs the following steps:
  
    - For each binding i:
    
      - `m_i` is evaluated, and the resulting value is bound to `id_i` in all
        the remaining subexpressions of this "let" expression.

      - If the binding is a guarded binding, then `guard_i` is evaluated; if it
        evaluates to `false`, then evaluation of the "let" expression terminates
        early, producing the value `null`.

    - `m` is evaluated, and the resulting value is the value produced by the
      "let" expression.

- The compilation artifact `(letArgs id = args in m) :: T`, where `args` is an
  _argument part artifact_, is an expression artifact that allows application of
  `args` to be deferred. Evaluation of this expression artifact performs the
  following steps:
  
  - All the expression artifacts within `args` are evaluated (in the order in
    which they appear), and bound to fresh variables.

  - `m` is evaluated. Anywhere `id` appears in `m`, it is substituted with an _argument part artifact_ containing:
  
    - The same type arguments as `args`,
    
    - The same name identifiers as `args`,
    
    - And for each expression artifact in `args`, an expression artifact that
      evaluates to the value of the variable that was bound when `args` was
      evaluated.

TODO(paulberry): maybe some of this stuff can be eliminated

- `instanceGet(m :: T, id)` represents an invocation of the getter named `id` on
  the target `m`. It is guaranteed by soundness that the evaluation result of
  `m` will have a getter named `id` in its interface.

- `extensionGet(m :: T, E.id)` represents an invocation of the getter named `id`
  in the extension `E`, where `this` is bound to the target `m`. It is
  guaranteed by soundness that the extension `E` contains a getter named `id`.
  
- `dynamicMethodCall(m :: T, id, args)` represents a dynamic invocation of the
  method named `id` on the target `m`, applying _argumentPart_ `args`. At
  runtime, the evaluation result of `m` might turn out not to have a method
  named `id` in its interface, or it might have a method that isn't compatible
  with `args`, in which case an exception will be thrown.

- `instanceMethodCall(m :: T, id, args)` represents an invocation of the method
  named `id` on the target `m`, applying _argumentPart_ `args`. It is guaranteed
  by soundness that the evaluation result of `m` will have a method named `id`
  in its interface, which is compatible with `args`.

- `instanceGetterCall(m :: T, id, args)` represents an invocation of the getter
  named `id` on the target `m`, followed by an execution of the resulting
  object's `call` method, supplying _argumentPart_ `args`. It is guaranteed by
  soundness that the evaluation result of `m` will have a getter named `id` in
  its interface, whose return type is compatible with `args`. _Note that it's
  tempting to desugar `instanceGetterCall(m :: T, id, args)` into
  `instanceMethodCall(instanceGet(m :: T, id), call, args)`, but this would not
  be accurate; the former evaluates `args` before invoking `T.id`; the latter
  invokes `T.id` before evaluating `args`._

- `extensionMethodCall(E, m :: T, E.id, args)` represents an invocation of the
  method named `id` in the extension `E`, where `this` is bound to the target
  `m`, applying _argumentPart_ `args`. It is guaranteed by soundness that the
  extension `E` contains a method named `id`, which is compatible with `args`.

- `extensionGetterCall(m :: T, E.id, args)` represents an invocation of the
  getter named `id` in the extension `E`, where `this` is bound to the target
  `m`, followed by an execution of the resulting object's `call` method,
  supplying _argumentPart_ `args`. It is guaranteed by soundness that the
  extension `E` contains a getter named `id`, whose return type is compatible
  with `args`. _Note that it's tempting to desugar `extensionGetterCall(m :: T,
  E.id, args)` into `extensionMethodCall(extensionGet(m :: T, E.id), call,
  args)`, but this would not be accurate; the former evaluates `args` before
  invoking `T.id`; the latter invokes `T.id` before evaluating `args`._

- `concat(components)` represents a built-in operation that performs string
  concatenation; `strings` is a sequence of literal characters or expression
  artifacts whose static type is a subtype of `String`. If `components` does not
  contain any string interpolations, then the result is a canonicalized
  constant.

- `symbol(e)` represents a constant reference to an instance of `Symbol`, where
  `e` conforms to the Dart syntax for a symbol literal.
  
- `int(i)` represents a constant reference to an instance of `int`, whose value
  is the integer `i`.

- `double(n)` represents a constant reference to an instance of `double`, whose
  value is the number `n`.
  
### Argument Part Inference

An _argumentPart_, as specified in the Dart grammar, consists of zero or more
type arguments and zero or more expression arguments; each expression argument
can optionally have an associated name identifier.

_Examples of argument parts include `()`, `<bool>(1, 'x')`, and `(foo: null)`._

The recursion step for inferring an _argumentPart_ takes two additional inputs:

- An inference context `K`.

- A type `F`.

The output of static invocation inference is an _argument part artifact_.

TODO(paulberry): add a description of the algorithm here (refer to the
[horizontal inference spec][]). Note that it should be a compile-time error if:

- `F` is not `dynamic` or a function type.

- `F` is a function type and there is a type mismatch to the _argumentPart_.

[horizontal inference spec]: https://github.com/dart-lang/language/tree/main/accepted/2.18/horizontal-inference/feature-specification.md

### Method Dispatch Inference

A step that is re-used multiple times in the definition of local type inference
is _method dispatch inference_. Method dispatch inference produces an expression
artifact based on an input of the form `(m0 :: T0).id args` and an input context
`K`, where:

- `m0 :: T0` is an expression artifact, known as the _target_ of the invocation.

- `id` is an identifier, known as the _method name_.

- `args` is an _argumentPart_.

To apply method dispatch inference to the input `(m0 :: T0).id args`, in context
`K`:

- Define `F` as follows:

  - If `T0` is [dynamic bounded](#Dynamic-Boundedness), then `F` is `dynamic`.

  - Otherwise, if the interface of `T0` contains a member named `id`, then `F`
    is the type of that member (either explicitly declared, or inferred via
    top-level inference).

  - Otherwise, if extension resolution of `id` on `T0` produces a member named
    `id`, then `F` is the type of that member (either explicitly declared, or
    inferred via top-level inference).

  - Otherwise, it is a compile-time error.

- Infer `args` in context `K` with type `F`, producing `args' :: R`.

- Then the result of method dispatch is `(m0 :: T0).id args' :: R`.

### Deferred Null Shorting

TODO(paulberry)

### L-value Inference

A step that is re-used multiple times in the definition of local type inference
is _l-value inference_. L-value inference acts on a single input expression, and
produces the following outputs:

- A sequence of `bindings` suitable for a let expression.

- An expression artifact `m_read :: T_read`. `m_read` is known as the L-value's
  _read expression_, and `T_read` is known as the L-value's _read type_.

- An expression artifact `m_write :: void Function(T_write)`. `m_write` is known
  as the L-value's _write expression_, and `T_write` is known as the L-value's
  _write type_.

- A context `K`, known as the L-value's _write context_.

L-value inference is only defined for expression types that may appear on the
left hand side of an assignment, or as the target of `--` or `++`.

L-value inference of an expression `e` is defined as follows:

- If `e` is a reference to a local variable `v`, with declared type `T_d` and promoted type `T_p`, then:

  - `bindings` is an empty sequence.
  
  - The read expression is `v :: T_p`.
  
  - The write expression is `(v') { v = v'; } :: void Function(T_d)`, where `v'`
    is a fresh variable.
  
  - The write context is `T_p`.

- If `e` is a property access expression of the form `e1.id` or `e1?.id`, then:

  - Infer `e1` in context `_` with deferred null shorting, producing
    `(bindings', m1 :: T1)`.

  - Let `v` be a fresh variable.
  
  - Define `binding` as follows:
  
    - If `e` takes the form `e1.id`, then `binding` is the simple binding `v =
      m1 :: T1`.
    
    - Otherwise, `binding` is the guarded binding `v = m1 :: T1 if (v != null)`.

  - The read expression is TODO(paulberry)

#### L-value Inference for a Local Variable



several outputs based on a single input expression `e`.  produces an expression
artifact based on an input of the form `(m0 :: T0).id args` and an input context
`K`, where:



### Expression Type Inference

The recursion step for local type inference of an expression takes one
additional input: an inference context `K`. Its output is an _expression
artifact_.

_It is tempting to think of an expression's context as the type that the
expression must have in order to avoid a compile-time error. In many cases, if
an expression's static type fails to satisfy its context, a compile-time error
**will** result. However, there are several situations in which it won't:_

- _In an assignment expression whose left hand side refers to a local variable,
  if the variable has undergone type promotion at the time of the assignment,
  the promoted type of the variable is used as the context of the assignment
  expression's right hand side. If the right hand side of the assignment
  expression fails to satisfy its context, there is no error; the assignment
  simply causes the variable to be demoted back to its declared type, or to a
  previously promoted type._

- _If an if-null expression `e1 ?? e2` occurs in context `_`, then the static
  type of `e1` is used as the context for `e2`. If `e2` fails to satisfy its
  context, there is no error._

- _Sometimes, if an expression fails to satisfy its context, the compiler will
  insert a coercion (such as a dynamic downcast)._

#### Null

To infer a null literal `e` of the form `null` in context `K`:

- Let `m` be an expression artifact that evaluates to the `null` value.

- The result of inference is `m :: Null`.

#### Numbers

##### Integer Literals

To infer an integer literal `e` in context `K`:

- Let `i` be the numeric value of `e`.

- Let `S` be the greatest closure of `K`.

- If `int <: S` or `double <!: S`, then:

  - Define `m` as follows:

    - If `e` is a hexadecimal integer literal, `2^63 <= i < 2^64`, and the `int`
      class is implemented as signed 64-bit two’s complement integers, `m` is an
      expression artifact that evaluates to an instance of `int` with numeric
      value `i - 2^64`. _In other words, a hexadecimal value such as
      `0x800000000000000`, which is too large to be represented as a signed
      64-bit integer, but not too large to be represented by an unsigned 64-bit
      integer, simply "overflows" to the negative integer with an equivalent bit
      representation. This only happens if the implementation represents
      integers as signed 64-bit values._

    - Otherwise, if `i` cannot be represented exactly by an instance of `int`,
      then it is a compile-time error.

    - Otherwise, `m` is an expression artifact that evaluates to an instance of
      `int` with numeric value `i`.

  - Then the result of inferring `e` is `m :: int`.

- Otherwise:

  - If `i` cannot be represented exactly by an instance of `double`, then it is
    a compile-time error. TODO(paulberry): the front end doesn't do this;
    instead it falls back on an integer representation.
    
  - Otherwise:
  
    - Let `m` be an expression artifact that evaluates to an instance of
      `double` with numeric value `i`.
    
    - Then, the result of inferring `e` is `m :: double`.

##### Double Literals

To infer a double literal `e` in context `K`:

- Let `n` be the numeric value of `e`.

- Let `m` be an expression artifact that evaluates to an instance of `double`
  with numeric value `n`.

- The result of inferring `e` is `m :: double`.

#### Boolean Literals

To infer a boolean literal `e` of the form `true` or `false`, in context `K`:

- Let `b` be the boolean value of `e`.

- Let `m` be an expression artifact that evaluates to the instance of `bool`
  with boolean value `b`.

- The result of inferring `e` is `m :: bool`.

#### String Literals

A string literal consists of a sequence of components, each of which is either a
literal character or a string interpolation. String interpolation can take one
of three forms:

- `$id`, where `id` is an identifier.

- `$this`.

- `${e}`, where `e` is some expression.

To infer a string literal `e` in context `K`:

- For each component `c_i` in the string interpolation, define `m_i` as follows:
    
  - If `c_i` is a literal character, then `m_i` is an expression artifact that
    evaluates to a string containing the single character `c_i`.

  - Otherwise:
      
    - Define `e_i` as follows:
  
      - If `c_i` is of the form `$id`, where `id` is an identifier, then `e_i` is
        `id`.
    
      - Otherwise, if `c_i` is of the form `$this`, then `e_i` is `this`.

      - Otherwise, `c_i` must be of the form `${e_i'}`. Then `e_i` is `e_i'`.

    - Infer `e_i` in context `_`, producing `m_i' :: T_i'`.
      
    - Perform method dispatch inference on `(m_i' :: T_i').toString()` in
      context `_`, producing `m_i :: T_i`. _It is guaranteed by soundness that
      `T_i <: String`, because the `Object` and `Null` classes define `toString`
      to have a return type of `String`._

- Let `m` be an expression artifact that evaluates all the `m_i`s and
  concatenates the results into a single instance of `String`.

- Then the result of inferring `e` is `m :: String`.

#### Symbol Literals

To infer a symbol literal `e` in context `K`:

- Let `m` be an expression artifact that evaluates to an instance of `Symbol`
  whose value corresponds to the syntax of `e`.

- The result of inferring `e` is `m :: Symbol`.

#### Collection Literals

TODO(paulberry)

#### Throw Expressions

To infer a throw expression `e` of the form `throw e1`, in context `K`:

- Infer `e1` in context `_`, producing `m1 :: T1`.

- The result of inferring `e` is `throw m1 :: Never`.

#### Function Expressions

TODO(paulberry)

#### This

To infer an expression `e` of the form `this`, in context `K`:

- Define `R` as follows:

  - If `e` occurs in a static context (a factory constructor, a static method or
    variable initializer, or in the initializing expression of a non-late
    instance variable), then it is a compile-time error.

  - Otherwise, if `e` is enclosed in a class, enum, mixin, or extension type,
    then let `R` be its interface.

  - Otherwise, if `e` is enclosed in an extension declaration, then let `R` be
    the extension's `on` type.

  - Otherwise, it is a compile-time error.

- The resulting expression is `this :: R`.

#### Instance Creation

TODO(paulberry)

#### Function Invocation

TODO(paulberry)

#### Function Closurization

_A function closurization is informally known as a "tear off"._

TODO(paulberry)

#### Generic Function Instantiation

TODO(paulberry)

#### Top Level Getter Invocation

A top level getter invocation is an expression of the form `id`, where `id` is
an identifier that resolves to a top level getter.

To infer a top level getter invocation `e`, in context `K`:

- Let `g` be the top level getter that `e` resolves to.

- Let `R` be the return type of `g` (either explicitly declared, or inferred via
  top-level inference).

- The result of inference is `e :: R`.

#### Member Invocation

TODO(paulberry)

#### Cascades

To infer a cascade expression `e` of the form `e1..e2` in context `K`:

- Infer `e1` in context `K`, producing `m1` with static type `T1`.

- Infer `e2` in context `_`, producing `m2` with static type `T2`.

- The resulting expression is `m1..m2`, with static type `T1`.

#### Superinvocations

TODO(paulberry)

#### Property Extractions

TODO(paulberry): how does this differ from a function closurization?

#### Assignment

An assignment `e` may take any of the following forms:

- An ordinary assignment, `e1 = e2`.

- An if-null assignment, `e1 ??= e2`.

- A compound assignment, `e1 op= e2`, where `op` is one of the of the following:
  `*`, `/`, `~/`, `%`, `+`, `-`, `<<`, `>>>`, `>>`, `&`, `^`, or `|`.

To infer an assignment `e` of one of these forms, in context `K`:

- Infer `e1` in context `_` with deferred null shorting (**TODO(paulberry):
  define**), producing `m1`, with static type `Tr`, and guard `mg`. _(`Tr` is
  known as the "read type" of `e1`.)_

- Let `Tw` be the write type of `e1`, defined as follows:

  - If `e1` refers to a local variable, `Tw` is the declared (unpromoted) type
    of the variable.

  - Otherwise, `Tw` is the static type of the single argument of the setter
    associated with `e1` (or, if `e1` is an index expression, the static type of
    the second argument of the appropriate declaration of `operator []=`).

- Let `Tp` be the promoted write type of `e1`, defined as follows:

  - If `e1` refers to a local variable, `Tp` is `Tr` (the promoted type of the
    variable).

  - Otherwise, `Tp` is `Tw`.

- If `e` is a compound assignment:

  - Let `K2` be the static type of the single argument of `Tread.operator op`,
    and let `Tc` be the operator's return type.

  - Infer `e2` in context `K2`, producing `m2` with static type `T2`.

  - Coerce `m2`, with static type `T2`, to context `K2`, producing `m2'` with
    static type `T2'`. **TODO(paulberry): specify this**

  - Let `mc` be the expression `m1 op m2'`.

  - Coerce `mc`, with static type `Tc`, to context `Tw`, producing `mc'` with
    static type `Tc'`.

  - Let `m` be the expression `e1 = mc'`, where it is understood that any
    subexpressions shared by `e1` and `mc'` should only be evaluated once.

  - Let `R` be `Tc'`.

- Otherwise, if `e` is an if-null assignment:

  - Let `Tr'` be `NonNull(Tr)`. _This is the type read from `e1`, in the event
    that the assignment does not occur._

  - Infer `e2` in context `Tp`, producing `m2` with static type `T2`.
  
  - Coerce `m2`, with static type `T2`, to context `Tw`, producing `m2'` with
    static type `T2'`. _`T2'` is the type that will be written to `e1`, in the
    event that the assignment **does** occur._

  - Let `T` be **UP**(`Tr'`, `T2'`).
  
  - Let `S` be the greatest closure of `K`.

  - Let `m` be the expression `m1 ?? (e1 = m2)`, where it is understood that any
    subexpressions shared by `e1` and `m1` should only be evaluated once.

  - Define `R` as follows:

    - If `T <: S`, then let `R` be `T`.

    - Otherwise, if `Tr' <: S` and `T2' <: S`, then let `R` be `S`.

    - Otherwise, let `R` be `T`.

- Otherwise (`e` is an ordinary assignment):

  - Infer `e2` in context `Tp`, producing `m2` with static type `T2`.
  
  - Coerce `m2`, with static type `T2`, to context `Tw`, producing `m2'` with
    static type `T2'`.

  - Let `m` be the expression `m1 = e2`.
  
  - Let `R` be `T2'`.

- If `mg` is empty, then the result of inferring `e` is `m`, with static type
  `R`.

- Otherwise, the result of inferring `e` is `mg ? m : null`, with static type
  `R?`.

#### Conditional Expressions

To infer a conditional expression `e` of the form `e1 ? e2 : e3` in context `K`:

- Infer `e1` in context `bool`, producing `m1`, with static type `T1`.

- Coerce `m1`, with static type `T1`, to context `bool`, producing `m1'` with
  static type `T1'`.

- Infer `e2` in context `K`, producing `m2`, with static type `T2`.

- Infer `e3` in context `K`, producing `m3`, with static type `T3`.

- Let `T` be **UP**(`T2`, `T3`).
  
- Let `S` be the greatest closure of `K`.

- Let `m` be the expression `m1' ? m2 : m3`.

- Define `R` as follows:

  - If `T <: S`, then let `R` be `T`.

  - Otherwise, if `T2 <: S` and `T3 <: S`, then let `R` be `S`.

  - Otherwise, let `R` be `T`.

- Then the result of inferring `e` is `m`, with static type `R`.

#### If-null Expressions

_Note: the front end does not yet completely adhere to this spec; see
https://github.com/dart-lang/language/issues/3650._

To infer an if-null expression `e` of the form `e1 ?? e2`, in context `K`:

- Infer `e1` in context `K?`, producing `m1`, with static type `T1`.

- Let `T1'` be **NonNull**(`T1`). _This is the type of the result of evaluting
  `e1`, in the event that evaluation of `e2` does not occur._

- Define `J` as follows:

  - If `K` is `_` or `dynamic`, let `J` be `T1`.
  
  - Otherwise, let `J` be `K`.

- Infer `e2` in context `J`, producing `m2`, with static type `T2`. _This is the
  type of the result of evaluating `e2`, in the event that evaluation of `e2`
  **does** occur._

- Let `T` be **UP**(`T1'`, `T2`).
  
- Let `S` be the greatest closure of `K`.

- Let `m` be the expression `m1 ?? m2`.

- Define `R` as follows:

  - If `T <: S`, then let `R` be `T`.

  - Otherwise, if `T1' <: S` and `T2 <: S`, then let `R` be `S`.

  - Otherwise, let `R` be `T`.

- Then the result of inferring `e` is `m`, with static type `R`.

#### Logical Boolean Expressions

A logical boolean expression takes the form `e1 op e2`, where `op` is either
`||` or `&&`.

To infer a logical boolean expression `e`, of the form `e1 op e2`, in context `K`:

- Infer `e1` in context `bool`, producing `m1`, with static type `T1`.

- Coerce `m1`, with static type `T1'`, to context `bool`, producing `m1'` with
  static type `T1'`.

- Infer `e2` in context `bool`, producing `m2`, with static type `T2`.

- Coerce `m2`, with static type `T2'`, to context `bool`, producing `m2'` with
  static type `T2'`.

- Then the result of inferring `e` is `m1' op m2'`, with static type `bool`.

#### Equality Expressions

An equality expression takes the form `e1 op e2`, where `op` is either `==` or
`!=`.

To infer an equality expression `e`, of the form `e1 op e2`, in context `K`:

- Infer `e1` in context `_`, producing `m1`, with static type `T1`.

- Let `J` be the static type of the single argument of `T1.operator==`.

- Infer `e2` in context `_`, producing `m2`, with static type `T2`.

- Coerce `m2`, with static type `T2`, to context `J`, producing `m2'` with
  static type `T2'`.

- Then the result of inferring `e` is `m1 op m2'`, with static type `bool`.

#### User-definable Binary Expression

A user-definable binary expression takes the form `e1 op e2`, where `op` is one
of `>=`, `>`, `<=`, `<`, `|`, `^`, `&`, `<<`, `>>>`, `>>`, `+`, `-`, `*`, `/`,
`%`, or `~/`.

To infer a user-definable binary expression `e`, of the form `e1 op e2`, in
context `K`:

- Infer `e1` in context `_`, producing `m1`, with static type `T1`.

- Define `J` and `R` as follows:

  - If the interface of `T1` contains an operator named `op`, `J` is the static
    type of the operator's single argument, and `R` is its return type.

  - Otherwise, it is a compile-time error.

- Infer `e2` in context `_`, producing `m2`, with static type `T2`.

- Coerce `m2`, with static type `T2`, to context `J`, producing `m2'` with
  static type `T2'`.

- Then the result of inferring `e` is `m1 op m2'`, with static type `R`.

#### User-definable Unary Expressions

A user-definable unary expression takes the form `op e1`, where `op` is one of
`-`, `~`.

To infer a user-definable unary expression `e` of the form `op e1`, in context
`K`:

- If `e1` is an integer literal and `op` is `-`, then:

  - Let `i` be the numeric value of `e1`.

  - Let `S` be the greatest closure of `K`.

  - Define `R` as follows:

    - If `int <: S`, then let `R` be `int`.
  
    - Otherwise, if `double <: S`, then let `R` be `double`.

    - Otherwise, let `R` be `int`.

  - Define `m` as follows:

    - If `R` is `int`, then:

      - If `i` is zero, and the `int` class can represent a negative zero value,
        then let `m` be a constant reference to an instance of `int` whose value
        is negative zero.

      - Otherwise, if `-i` cannot be represented exactly by an instance of
        `int`, then it is a compile-time error.

      - Otherwise, let `m` be a constant reference to an instance of `int` with
        value `-i`.

    - Otherwise, if `R` is `double`, then:

      - If `i` is `0`, then let `m` be a constant reference to an instance of
        `double` whose value is negative zero.

      - If `-i` cannot be represented exactly by an instance of `double`, then it
        is a compile-time error.

      - Otherwise, let `m` be a constant reference to an instance of `double`
        with value `-i`.

  - Then the result of inferring `e` is `m`, with static type `R`. _In effect,
    an integer literal preceded by `-` is treated as an integer literal with a
    negative value, rather than an invocation of the `unary-` operator._

- Otherwise:

  - Infer `e1` in context `_`, producing `m1`, with static type `T1`.

  - 

#### Await Expressions

_Note: the analyzer does not yet completely adhere to this spec; see
https://github.com/dart-lang/language/issues/3648._

_Note: the front end does not yet completely adhere to this spec; see
https://github.com/dart-lang/language/issues/3649._

_Note: there is a propsal to improve this; see
https://github.com/dart-lang/language/issues/3648._

To infer an await expression `await e1` in context `K`:

- Define `J` as follows:

  - If `K` is `dynamic`, then `J` is `FutureOr<_>`.

  - Otherwise, `J` is `FutureOr<K>`.

- Infer `e1` in context `J`, producing `m1`, with static type `T1`.

- Let `R` be `flatten(T1)`.

- The resulting expression is `await m1`, with static type `R`.

#### Type Cast

To infer a type cast expression `e1 as T` in context `K`:

- Infer `e1` in context `_`, producing `m1` with static type `T1`.

- The resulting expression is `m1 as T`, with static type `T`.

### Lvalue inference

<!-- THIS MATERIAL HAS NOT BEEN UPDATED

The primary function of expression inference is to determine the parameter and
return types of closure literals which are not explicitly annotated, and to fill
in elided type variables in constructor calls, generic method calls, and generic
literals.

### Expectation contexts

A typing expectation context (written using the meta-variables `J` or `K`) is
a type schema `P`.

### Constraint set resolution

The full resolution of a constraint set `C` for a list of type parameters `<T0
extends B0, ..., Tn extends Bn>` given an initial partial
solution `[T0 -> P0, ..., Tn -> Pn]` is defined as follows.  The resolution
process computes a sequence of partial solutions before arriving at the final
resolution of the arguments.

Solution 0 is `[T0 -> P00, ..., Tn -> P0n]` where `P0i` is `Pi` if `Ti` is fixed
in the initial partial solution (i.e. `Pi` is a type and not a type schema) and
otherwise `Pi` is `?`.

Solution 1 is `[T0 -> P10, ..., Tn -> P1n]` where:
  - If `Ti` is fixed in Solution 0 then `P1i` is `P0i`'
  - Otherwise, let `Ai` be `Bi[P10/T0, ..., ?/Ti, ...,  ?/Tn]`
  - If `C + Ti <: Ai` over constrains `Ti`, then it is an
    inference failure error
  - If `C + Ti <: Ai` does not constrain `Ti` then `P1i` is `?`
  - Otherwise `Ti` is fixed with `P1i`, where `P1i` is the **grounded**
    constraint solution for `Ti` with respect to `C + Ti <: Ai`.

Solution 2 is `[T0 -> M0, ..., Tn -> Mn]` where:
  - let `A0, ..., An` be derived as
    - let `Ai` be `P1i` if `Ti` is fixed in Solution 1
    - let `Ai` be `Bi` otherwise
  - If `<T0 extends A0, ..., Tn extends An>` has no default bounds then it is
    an inference failure error.
  - Otherwise, let `M0, ..., Mn`be the default bounds for `<T0 extends A0,
      ..., Tn extends An>`

If `[M0, ..., Mn]` do not satisfy the bounds `<T0 extends B0, ..., Tn extends
Bn>` then it is an inference failure error.

Otherwise, the full solution is `[T0 -> M0, ..., Tn -> Mn]`.

### Downwards generic instantiation resolution

Downwards resolution is the process by which the return type of a generic method
(or constructor, etc) is matched against a type expectation context from an
invocation of the method to find a (possibly partial) solution for the missing
type arguments

`[T0 -> P0, ..., Tn -> Pn]` is a partial solution for a set of type variables
`<T0 extends B0, ..., Tn extends Bn>` under constraint set `Cp` given a type
expectation of `R` with respect to a return type `Q` (in which the `Ti` may be
free) where the `Pi` are type schemas (potentially just `?` if unresolved)/

If `R <: Q [T0, ..., Tn] -> C` does not hold, then each `Pi` is `?` and `Cp` is
    empty

Otherwise:
  - `R <: Q [T0, ..., Tn] -> C` and `Cp` is `C`
  - If `C` does not constrain `Ti` then `Pi` is `?`
  - If `C` partially constrains `Ti`
    - If `C` is over constrained, then it is an inference failure error
    - Otherwise `Pi` is the constraint solution for `Ti` with respect to `C`
  - If `C` fully constrains `Ti`, then
    - Let `Ai` be `Bi[R0/T0, ..., ?/Ti, ..., ?/Tn]`
    - If `C + Ti <: Ai` is over constrained, it is an inference failure error.
    - Otherwise, `Ti` is fixed to be `Pi`, where `Pi` is the constraint solution
      for `Ti` with respect to `C + Ti <: Ai`.

### Upwards generic instantiation resolution

Upwards resolution is the process by which the parameter types of a generic
method (or constructor, etc) are matched against the actual argument types from
an invocation of a method to find a solution for the missing type arguments that
have not been fixed by downwards resolution.

`[T0 -> M0, ..., Tn -> Mn]` is the upwards solution for an invocation of a
generic method of type `<T0 extends B0, ..., Tn extends Bn>(P0, ..., Pk) -> Q`
given actual argument types `R0, ..., Rk`, a partial solution `[T0 -> P0, ...,
Tn -> Pn]` and a partial constraint set `Cp`:
  - If `Ri <: Pi [T0, ..., Tn] -> Ci`
  - And the full constraint resolution of `Cp + C0 + ... + Cn` for `<T0 extends
B0, ..., Tn extends Bn>` given the initial partial solution `[T0 -> P0, ..., Tn
-> Pn]` is `[T0 -> M0, ..., Tn -> Mn]`

### Discussion

The incorporation of the type bounds information is asymmetric and procedural:
it iterates through the bounds in order (`Bi[R0/T0, ..., ?/Ti, ..., ?/Tn]`).  Is
there a better formulation of this that is symmetric but still allows some
propagation?

-->

### Inference rules

Expression inference occurs 

- TODO(leafp): Generalize the following closure cases to the full function
  signature.
  - In general, if the function signature is compatible with the context type,
    take any available information from the context.  If the function signature
    is not compatible, this should always be a type error anyway, so
    implementations should be free to choose the best error recovery path.
  - The monomorphic case can be treated as a degenerate case of the polymorphic
    rule
- The expression `<T>(P x) => e` is inferred as `<T>(P x) => m` of type `<T>(P)
  -> M` in context `_`
  - If `e` is inferred as `m` of type `M` in context `_`
- The expression `<T>(P x) => e` is inferred as `<T>(P x) => m` of type `<T>(P)
  -> M` in context `<S>(Q) -> N`
  - If `e` is inferred as `m` of type `M` in context `N[T/S]`
  - Note: `x` is resolved as having type `P`  for inference in `e`
- The expression `<T>(x) => e` is inferred as `<T>(dynamic x) => m` of type
  `<T>(dynamic) -> M` in context `_`
  - If `e` is inferred as `m` of type `M` in context `_`
- The expression `<T>(x) => e` is inferred as `<T>(Q[T/S] x) => m` of type
  `<T>(Q[T/S]) -> M` in context `<S>(Q) -> N`
  - If `e` is inferred as `m` of type `M` in context `N[T/S]`
  - Note: `x` is resolved as having type `Q[T/S]` for inference in `e`
- Block bodied lamdas are treated essentially the same as expression bodied
  lambdas above, except that:
  - The final inferred return type is `UP(T0, ..., Tn)`, where the `Ti` are the
    inferred types of the return expressions (`void` if no returns).
  - The returned expression from each `return` in the body of the lamda uses the
    same type expectation context as described above.
  - TODO(leafp): flesh this out.
- For async and generator functions, the downwards context type is computed as
  above, except that the propagated downwards type is taken from the type
  argument to the `Future` or `Iterable` or `Stream` constructor as appropriate.
  If the return type is not the appropriate constructor type for the function,
  then the downwards context is empty.  Note that subtypes of these types are
  not considered (this is a strong mode error).
- The expression `e(e0, .., ek)` is inferred as `m<M0, ..., Mn>(m0, ..., mk)` of
  type `N` in context `_`:
  - If `e` is inferred as `m` of type `<T0 extends B0, ..., Tn extends Bn>(P0,
    ..., Pk) -> Q` in context `_`
  - And the initial downwards solution is `[T0 -> Q0, ..., Tn -> Qn]` with
    partial constraint set `Cp` where:
    - If `K` is `_`, then the `Qi` are `?` and `Cp` is empty
    - If `K` is `Q <> _` then `[T0 -> Q0, ..., Tn -> Qn]` is the partial
solution for `<T0 extends B0, ..., Tn extends Bn>` under constraint set `Cp` in
downwards context `P` with respect to return type `Q`.
  - And `ei` is inferred as `mi` of type `Ri` in context `Pi[?/T0, ..., ?/Tn]`
  - And `<T0 extends B0, ..., Tn extends Bn>(P0, ..., Pk) -> Q` resolves via
upwards resolution to a full solution `[T0 -> M0, ..., Tn -> Mn]`
    - Given partial solution `[T0 -> Q0, ..., Tn -> Qn]`
    - And partial constraint set `Cp`
    - And actual argument types `R0, ..., Rk`
  - And `N` is `Q[M0/T0, ..., Mn/Tn]`
- A constructor invocation is inferred exactly as if it were a static generic
  method invocation of the appropriate type as in the previous case.
- A list or map literal is inferred analagously to a constructor invocation or
  generic method call (but with a variadic number of arguments)
- A (possibly generic) method invocation is inferred using the same process as
  for function invocation.
- A named expression is inferred to have the same type as the sub-expression
- A parenthesized expression is inferred to have the same type as the
  sub-expression
- A tear-off of a generic method, static class method, or top level function `f`
  is inferred as `f<M0, ..., Mn>` of type `(R0, ..., Rm) -> R` in context `K`:
  - If `f` has type `A``T0 extends extends B0, ..., Tn extends Bn>(P0, ..., Pk) ->
    Q`
  - And `K` is `N` where `N` is a monomorphic function type
  - And `(P0, ..., Pk) -> Q <: N [T0, ..., Tn] -> C`
  - And the full resolution of `C` for `<T0 extends B0, ..., Tn extends Bn>`
given an initial partial solution `[T0 -> ?, ..., Tn -> ?]` and empty constraint
set is `[T0 -> M0, ..., Tn -> Mn]`



TODO(leafp): Specify the various typing contexts associated with specific binary
operators.


## Method and function inference.

TODO(leafp)


Constructor declaration (field initializers)
Default parameters

## Statement inference.

TODO(leafp)

Return statements pull the return type from the enclosing function for downwards
inference, and compute the upper bound of all returned values for upwards
inference.  Appropriate adjustments for asynchronous and generator functions.

Do statements
For each statement

-->
