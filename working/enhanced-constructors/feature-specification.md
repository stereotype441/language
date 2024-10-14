# Enhanced Constructors Feature Specification

Author: Paul Berry

Status: Under review

Version 1.0 (see [CHANGELOG](#CHANGELOG) at end)

## Summary

This proposal extends the set of actions that can be performed in the body of a
constructor to include:

- Writing to non-late final fields,

- Explicitly invoking super constructors,

- And explicitly invoking generative constructors in the same class.

This makes constructors more flexible, avoids the need for constructor
initializer lists, and simplifies the interaction between augmentations and
constructors.

To preserve soundness, flow analysis is enhanced to ensure that a reference to
`this` cannot escape from a constructor body before the object has been
completely constructed.

## Background

Dart follows the tradition of C++ and similar languages in requiring super
constructor invocations and final field assignments to occur prior to the
constructor body, in a so-called "initializer list". For example, in the code
below, the constructor for class `C` performs three actions: the assignment `j =
x + 1`, the super constructor invocation `super(x * 2)`, and the ordinary method
invocation `m()`. But the first two of those actions must be performed using
initializer list syntax, prior to the `{` that begins the constructor body,
whereas the third action can be written as an ordinary statement, inside the
constructor body (indeed, it must, since it implicitly refers to `this`).

```dart
class B {
  final int i;
  B(this.i);
  void m() { ... }
}

class C extends B {
  final int j;
  C(int x)
      : j = x + 1,
        super(x * 2) {
    m();
  }
}
```

Programmers unfamiliar with initializer lists might wonder why it's not possible
to write `j = x + 1` and `super(x * 2)` as ordinary statements, like this:

```dart
class C extends B {
  final int j;
  C(int x) {
    j = x + 1;
    super(x * 2);
    m();
  }
}
```

The reason we require the user to use an initializer list to initialize `j` and
to call the super constructor is because initializer lists are restricted in a
way that ensures soundness. In particular, in an initializer list:

- It is not permissible to refer to `this` either explicitly or implicitly,

- And all final fields in the class must be initialized prior to invoking the
  super constructor. (If there is no explicit super constructor invocation in
  the initializer list, an implicit `super()` invocation is appended to the
  initializer list.)

These two restrictions together ensure that it is not possible to refer to
`this` before _all_ fields have been initialized. Therefore, even though object
construction is a multi-step process, it's never possible for a program to try
to read from an uninitialized field.

However, these restrictions come at a cost, both in terms of making the language
less approachable (since they require the user to learn a special syntax that's
used only in constructors), and in terms of flexibility, since they require any
given constructor to always initialize fields in the same order, and always call
the same super constructor. Also, these restrictions have complicated our
efforts to allow augmentations to apply to constructors.

## Proposal

This proposal addresses these costs by allowing the following kinds of
expressions to appear within the body of a generative constructor:

- A write to a non-late final field, either via an implicit `this` reference
  (`this.FIELDNAME = VALUE`) or an implicit `this` reference (`FIELDNAME =
  VALUE`). _Note that in this document, all-caps names are metasyntactic
  variables._

- A call to a super constructor, using the syntax `super(ARGUMENTS)` (for an
  unnamed constructor) or `super.NAME(ARGUMENTS)` (for a named constructor).

- A call to another generative constructor in the same class, using the syntax
  `this(ARGUMENTS)` (for an unnamed constructor) or `this.NAME(ARGUMENTS)` (for
  a named constructor).

To ensure soundness, flow analysis will be modified in order to ensure, at
compile time, that all control flow paths in a generative constructor either:

- Invoke another generative constructor exactly once, prior to accessing `this`,

- Or invoke a super constructor exactly once, after writing to every non-late
  final field exactly once, and prior to accessing `this`. (Exception: a
  constructor can read from fields of `this` that it has already initialized.)

This allows the vast majority of constructor initializer lists to be rewritten
as ordinary statements in the constructor body. For example, this constructor
from the analyzer's `VariableDeclarationImpl` class:

```dart
  VariableDeclarationImpl({
    required this.name,
    required this.equals,
    required ExpressionImpl? initializer,
  })  : _initializer = initializer,
        super(comment: null, metadata: null) {
    _becomeParentOf(_initializer);
  }
```

could be rewritten to:

```dart
  VariableDeclarationImpl({
    required this.name,
    required this.equals,
    required ExpressionImpl? initializer,
  }) {
    _initializer = initializer;
    super(comment: null, metadata: null);
    _becomeParentOf(_initializer);
  }
```

### Mixed style

To avoid a "syntactic cliff" between the old and new styles of coding generative
constructors, it is allowed to mix the two styles. That is, even in a generative
constructor that has an initializer list, the body is allowed to contain writes
to non-late final fields, or invocations of super constructors.

For example, here is the same `VariableDeclarationImpl` constructor again,
written in a mixed style:

```dart
  VariableDeclarationImpl({
    required this.name,
    required this.equals,
    required ExpressionImpl? initializer,
  })  : _initializer = initializer {
    super(comment: null, metadata: null);
    _becomeParentOf(_initializer);
  }
```

The same flow analysis logic that ensures soundness in fully "new style"
constructors also ensures soundness in mixed style constructors.

### Implicit super invocation

Today, Dart allows an implicit `super()` to be elided from an initializer list
of a generative constructor (and allows for the entire initializer list to be
elided, if it contains nothing else). To preserve backwards compatibility, and
to avoid making new style constructors more verbose than old style ones,
enhanced constructors support the same feature. The precise rules are specified
below, but in a nutshell (TODO: link), if neither the body nor the initializer
list of a generative constructor contains an explicit super constructor
invocation, then an implicit call to `super()` is considered to occur at the
earliest point (or points) in the construtcor body at which all non-late final
fields have been definitely assigned.

TODO: example

TODO: make an issue to discuss alternatives

TODO: specify fully

### Interaction with `this.` and `super.` parameters

Today, Dart allows a constructor parameter to use the syntax `this.NAME` to
implicitly initialize a field, and the syntax `super.NAME` to implicitly pass a
parameter to the super constructor.

These features are fully supported by enhanced constructors. For example, the
following code is valid:

```dart
class B {
  final int i;
  B({required this.i});
}

class C extends B {
  final int j;
  C({required super.i, required this.j}) {
    // this.j has been initialized here
    super(); // Implicitly passes `i`
  }
}
```

### Scoping differences with `this.`

Today, Dart allows an initializer list to refer to a `this.NAME` parameter,
through some special scoping magic: A `this.NAME` parameter is considered to
introduce a final variable named `NAME` into the formal parameter initializer
scope, but not into the constructor body. Most of the time this leads to
intuitive behaviors, for example:

```dart
class C {
  final int i;
  final int j;
  C(this.i)
    : j = i // `i` refers to the parameter passed to `C()`
  {
    print(i); // `i` refers to `this.i`, which has the same value.
  }
}
```

But occasionally the difference can show up in surprising ways:

```dart
class C {
  int i;
  final void Function() f;
  late final void Function() g;
  C(this.i)
    : f = (() { print(i); }) // prints the value passed to `C()`
  {
    g = () { print(i); }; // prints the current vlaue of `this.i`
  }
}

main() {
  var c = C(1);
  c.i = 2;
  c.f(); // prints `1`
  c.g(); // prints `2`
}
```

If the constructor for `C` is converted into an enhanced constructor in the
obvious way, `i` will refer to `this.i`, so the behavior will change:

```dart
class C {
  int i;
  final void Function() f;
  late final void Function() g;
  C(this.i)
  {
    f = () { print(i); }; // prints the current value of `this.i`
    g = () { print(i); }; // prints the current vlaue of `this.i`
  }
}

main() {
  var c = C(1);
  c.i = 2;
  c.f(); // prints `2`
  c.g(); // prints `2`
}
```

TODO: back-end consequences: it must be possible to access `this` on an
incomplete object. E.g. prior to the call to `super()`, a closure could be
created that reads from a variable in `this`.

### Scoping differences with `super.`

As with `this.NAME.`, a `super.NAME` parameter is considered to introduce a
final variable named `NAME` into the formal parameter initializer scope, but not
into the constructor body. This leads to the somewhat counterintuitive situation
wherein a super parameter that can be referred to from an initializer list can't
be referred to from a constructor body. For example:

```dart
class B {
  final int x;
  B(this.x)
}

class C extends B {
  final int j;
  late final int k;
  C(super.i)
    : j = i // `i` refers to the parameter passed to `C()`
  {
    k = i; // ERROR: `i` is not defined
  }
}
```

As a consequence of this, a user trying to rewrite a constructor from "old
style" to "new style" may need to reduce their use of the `super.` parameter
feature. For example, consider this code:

```dart
class B {
  final int i;
  B({required this.i});
}

class C extends B {
  final int j;
  C({required super.i}) : j = i; // ok; `i` is in scope
}
```

To change the constructor for `C` into the new style, the `super.i` parameter
needs to be changed into an ordinary parameter:

```dart
class B {
  final int i;
  B({required this.i});
}

class C extends B {
  final int j;
  C({required int i}) {
    j = i; // ok; `i` is in scope
    super(i);
  }
}
```

TODO(paulberry): would it be better to change the scoping rules to make super
parameters in scope for the whole constructor body?

TODO: fully specify `super.` behvaior.

### Interaction with augmentations

TODO(paulberry): spell out details here

## Details

### Parser support

No additional parser support is needed to support this feature, since the two
new pieces of syntax (writes to final fields and super constructor invocations)
are already accepted by the parser.

### Flow analysis enhancements

When flow analysis is used on a generative constructor, it tracks the following
additional pieces of boolean state, for every control flow path:

TODO: explanatory text saying the effect of each.

- For each final field in the containing class, a boolean indicating whether the
  field is definitely assigned (initial state: `true` if the field is
  initialized at the site of its declaration or via a `this.` parameter;
  otherwise `false`). _These booleans are used to ensure that no control flow
  path calls a super constructor before all non-late final fields have been
  initialized._

- For each final field in the containing class, whether the field is definitely
  unassigned (initial state: `false` if the field is initialized at the site of
  its declaration or in the initializer list, otherwise `true`). _These booleans
  are used to ensure that no control flow path attempts to write to a particular
  non-late final field more than once._

- Whether a constructor invocation has definitely occurred (initial state:
  `true` if the initializer list contains a super constructor invocation,
  otherwise `false`). _This boolean is used to ensure that no reference to
  `this` occurs before the super constructor has been invoked._

- Whether a constructor invocation has definitely _not_ occurred (initial state:
  `false` if the initializer list contains a super constructor invocation,
  otherwise `true`). _This boolean is used to ensure that no control flow path
  attempts to call a super constructor more than once._

The behavior of all these boolean variables in the presence of a flow analysis
`join` operation is the same as it is for the other boolean variables tracked by
flow analysis, namely:

- When joining two reachable control flow paths `A` and `B` to form a joined
  control flow path `C`, any given boolean variable is true in `C` if and only
  if it is true in both `A` and `B`.

- When joining a reachable control flow path `A` with an unreachable control
  flow path `B` to form a joined control flow path `C`, all boolean variables
  take on the same values in `C` as they do in `A`. (And vice versa with the
  roles of `A` and `B` reversed.)

- When joining two unreachable control flow paths `A` and `B` to form a joined
  control flow path `C`, if there exists a split point from which `A` is
  reachable but `B` is not, all boolean variables take on the same values in `C`
  as they do in `A`. (And vice versa with the roles of `A` and `B` reversed.)

- When joining two unreachable control flow paths `A` and `B` to form a joined
  control flow path `C`, if there is no difference in the reachability of `A`
  and `B` from prior split points, then any given boolean variable is true in
  `C` if and only if it is true in both `A` and `B`.

_Note that only the first two bullet items are necessary for soundness, since
they are the only two bullet items that deal with reachable control flow
paths. The remaining two bullet points exist solely to help avoid spurious
errors from occurring in unreachable code._

### Insertion of implicit super constructor invocations

Prior to type inference of a constructor, the constructor's initializer list and
body are scanned to determine whether they already contain at least one of the
following:

- An initializer or an expression of the form `this(ARGUMENTS)`, where the
  current class contains an unnamed constructor, or of the form
  `this.NAME(ARGUMENTS)`, where the current class contains a constructor with a
  name matching `NAME`.

- An initializer or an expression of the form `super(ARGUMENTS)`, where the
  superclass contains an unnamed constructor, or of the form
  `super.NAME(ARGUMENTS)`, where the superclass contains a constructor with a
  name matching `NAME`.

If none of these forms is found, an implicit super constructor invocation needs
to be inserted.

_The precise rules for when to insert an implicit super constructor invocation
are specified below. Informally, the super constructor invocation will be
inserted at the earliest point or points in the constructor body at which all
non-late final fields have been definitely assigned._

### Semantic analysis of field writes

Expression inference of `this.f = e_1` (where `f` is the name of a final field
in the containing class), in context `K`, produces an elaborated expression `m`
with static type `T`, where `m` and `T` are determined as follows:

- If the field is non-late, then:

  - It is a compile time error if the expression is not contained within the
    body of a generative constructor. _Non-late final fields can only be set at
    construction time._

  - It is a compile time error if the expression is contained within a function
    expression or a local function. _Flow analysis conservatively assumes that
    any given function expression or local function might be invoked any number
    of times (including zero) any time after it is created. Under this
    assumption there is no way to prove that the field will be initialized
    exactly once._

- Let `T_1` be the static type of the field `f`.

- Let `m_1` be the result of performing expression inference on `e_1`, in
  context `T_1`, and coercing the result to type `T_1`. _This mimics the
  existing semantics of field initializers, as well as the semantics of a write
  to a field that is either non-final or late._

- If `f` is definitely assigned at the point in control flow after execution of
  `m_1`, then it is a compile time error. _This mimics the existing semantics of
  writes to final local variables._

- If `f` is not a late field, and `f` is not definitely unassigned at the point
  in control flow after execution of `e_1`, then it is a compile-time
  error. _This mimics the existing semantics of writes to non-late final local
  variables._

- Let `m` be `this.f = m_1`, and let `T` be the static type of `m_1`.

- In the control flow path leaving `m`, set `f`'s "definitely assigned" boolean
  to `true` and set `f`'s "definitely unassigned" boolean to `false`.

- If it was previously determined (TODO: link) that an implicit super
  constructor needs to be inserted, and `f` not a late field, and all non-late
  fields are definitely assigned in the control path leaving `m`, and the
  expression is inside the constructor body (rather than the initializer list),
  then an implicit invocation of `super()` is inserted after `m`. _This does not
  change the fact that `m` evaluates to the same value as `m_1`._

It is a compile-time error for the target of a compound assignment or pre/post
increment/decrement to take the form `this.f`, where `f` is the name of a final
field in the containing class. _This was previously allowed if the field was
late, but it was guaranteed to fail at runtime, so it seems sensible to prohibit
it._

The same error applies if the target of a compound assignment or pre/post
increment/decrement takes the form `f`, where scope resolution rules resolve `f`
to a final field in the containing class.

It is a compile-time error for the target of an if-null assignment (`??=`) to
take the form `this.f`, where `f` is the name of a final field in the containing
class. _This was previously allowed if the field was late, but it was not
useful, since it would either fail at runtime or have no effect, so it seems
sensible to prohibit it._

The same error applies if the target of a compound assignment or pre/post
increment/decrement takes the form `f`, where scope resolution rules resolve `f`
to a final field in the containing class.

An expression or initializer of the form `f = e_1` (where scope resolution rules
resolve `f` to a final field in the containing class) is treated as equivalent
to the expression `this.f = e_1`.

### Semantic analysis at the end of a constructor initializer list

When type inference reaches the end of a generative constructor's initializer
list, the following check is made: If the flow analysis state indicates that all
of the class's final fields are definitely assigned, and if it was previously
determined (TODO: link) that an implicit super constructor needs to be inserted,
then an implicit invocation of `super()` is inserted just before the top of the
constructor body.

If the generative constructor has no initializer list, this check is performed
at the beginning of type inference of the constructor, before visiting the
constructor body (if any).

### Disambiguation of super constructor invocations from super method invocations

In a generative constructor, the following expressions are now potentially
ambiguous:

- `super(ARGUMENTS)` could be either an invocation of an unnamed constructor in
  the superclass, or the invocation of an instance method `call` in the
  superclass or one of its ancestors.

- `super.NAME(ARGUMENTS)` could be either an invocation of an accessible
  constructor named `NAME` in the superclass, or the invocation of an instance
  method or getter named `NAME` in the superclass or one of its ancestors.

- `this(ARGUMENTS)` could be either an invocation of an unnamed constructor in
  the current class, or the invocation of an instance method `call` in the
  interface of the current class.

- `this.NAME(ARGUMENTS)` could be either an invocation of an accessible
  constructor named `NAME` in the current class, or the invocation of an
  instance method or getter named `NAME` in the interface of the current class.

If one of these forms is found during type inference, then before any of the
`ARGUMENTS` are visited, the expression is disambiguated using the following
algorithm.

- The appropriate named or unnamed constructor is looked up, in either the
  current class or the superclass.

- The appropriate instance method or getter is looked up, in either the
  superclass or one of its ancestors, or in the interface of the current
  class. For this lookup, the forms `super(ARGUMENTS)` and `this(ARGUMENTS)` are
  only considered to match a method named `call`; they do not match a getter
  named `call`.

- If a constructor was found but an instance method or getter was not, then the
  expression is disambiguated to a constructor invocation.

- If an instance method or getter was found but a constructor was not, then the
  expression is disambiguated to an instance method or getter invocation, and is
  handled as it would have been prior to the introduction of enhanced
  constructors.

- If neither a constructor nor an instance method or getter was found, then it
  is a compile-time error. _This is consistent with the behavior of Dart in the
  absence of enhanced constructors._

- If both a constructor _and_ an instance method or getter were found, then the
  ambiguity is resolved according to whether a constructor has definitely been
  invoked at the current point in the flow control path. If it has, then the
  expression is disambiguated to an instance method or getter invocation;
  otherwise it is disambiguated to a constructor invocation.

_In principle, it would be better to perform this disambiguation after visiting
`ARGUMENTS`, but this is not possible, because in order to visit `ARGUMENTS`,
the target of the invocation must be known, so that the appropriate context
schemas can be computed._

_Since it's a compile-time error to call a constructor twice in the same control
flow path, and it's a compile-time error to reference `this` before a
constructor has been called, only one of the two possible interpretations can
possibly be correct. These heuristics will find the correct interpretation
nearly all the time. The two circumstances in which they won't are as follows:_

- _Nested ambiguous invocations. If one ambiguous invocation appears inside
  another, e.g. `super(super())`, then a valid interpretation might be that the
  inner invocation is a super constructor invocation, and the outer invocation
  is an instance method or getter invocation. But these heuristics won't find
  that interpretation, because they are run prior to visiting arguments, so they
  will consider both invocations to be super constructor invocations. This is
  unlikely to crop up in practice, because a constructor invocation has static
  type `void`, and hence is unlikely to be nested inside another invocation._

- _Implicit `super()`. If the user intends to take advantage of an implicit call
  to `super()`, but the constructor body contains an ambiguous invocation that
  looks like it could be a super-constructor invocation, or a call to a
  constructor in the current class, then the algorithm in (TODO: reference) will
  have already decided that no implicit super constructor invocation should be
  inserted, and so the ambiguous invocation will be interpreted as a
  super-constructor invocation. In the rare event that this happens, the user
  can work around it by adding an explicit call to `super()` at the top of the
  constructor body._

TODO: implicit `this` calls can still be virtually dispatched.

, an expression of the form `super(arguments)` could
be either an invocation of an unnamed super constructor or an invocation of the
instance method `call` (defined somewhere in the superclass chain). Similarly,
an expression of the form `this(arguments)` could be either an invocation of the
unnamed constructor of the current class or an invocation of the instance method
`call` (defined in the class itself or in the superclass chain).

By the same token, an expression of the form `super.name(arguments)` could be
either an invocation of a named super constructor or an invocation of an
instance method (or getter) named `name` in the superclass chain; and an
expression of the form `this.name(arguments)` could be either an invocation of a
named constructor in the current class or an invocation of an instance method
(or getter) named `name` in the class itself or in the superclass chain.

A two-step process is used to resolve such ambiguities:

- First, an attempt is made to locate an accessible constructor with the appropriate name in the appropriate class. In the case of `super.name(arguments)` and `this.name(arguments)`

The following heuristics are used to resolve any such ambiguities:

- If an accessible constructor with the appropriate name can be found in the
  appropriate class, and there is no matching instance method (or getter, if
  applicable), then the ambiguity is resolved in favor of the constructor. _(For
  example, if the superclass is `Object`, then `super()` always refers to the
  unnamed constructor of `Object`, since `Object` has no instance method
  `call`.)_

- If an accessible instance method (or getter, if applicable) with the
  appropriate name can be found in the superclass chain (or in the class itself,
  in the case of `this(arguments)` or `this.name(arguments)`), and there is no
  matching constructor, then the ambiguity is resolved in favor of the instance
  method or getter. _(For example, if the superclass is `Object`, then
  `super.noSuchMethod(...)` always refers to the instance method
  `Object.noSuchMethod`, since `Object` has no constructor `noSuchMethod`.)_

- If neither an accessible constructor with the appropriate name _nor_ an instance method (or getter, if applicable) can be found, then 

TODO: explain about noSuchMethod calls

TODO: rewrite with justification first.

If an expression of the form `super(arguments)` appears inside a generative
constructor, it is disambiguated during type inference, just prior to visiting
any arguments, using the first of the following heuristics that applies:

- If the superclass does not contain an unnamed constructor, and no class in the
  superclass chain defines an instance method named `call`, then it is a
  compile-time error.

- If the superclass contains an unnamed constructor, and no class in the
  superclass chain defines an instance method named `call`, then the expression
  is considered an invocation of the unnamed super constructor.

- If a class in the superclass chain defines an instance method named `call`,
  and the superclass does not contain an unnamed constructor, then the
  expression is considered an invocation of the instance method `super.call`.

- If a super constructor invocation has definitely occurred, then the expression
  is considered an invocation of the instance method `super.call`.

- Otherwise, the expression is considered an invocation of the unnamed
  super constructor.

If an expression of the form `super.name(arguments)` appears inside a generative
constructor, it is disambiguated during type inference, just prior to visiting
any arguments, using the first of the following heuristics that applies:

- If the superclass does not contain an accessible constructor named `name`, and
  no class in the superclass chain defines an accessible instance method named
  `name`, then it is a compile-time error.

- If the superclass contains an accessible constructor named `name`, and no
  class in the superclass chain defines an accessible instance method named
  `name`, then the expression is considered an invocation of the
  super constructor named `name`.

- If a class in the superclass chain defines an accessible instance method named
  `name`, and the superclass does not contain an accessible constructor named
  `name`, then the expression is considered an invocation of the instance method
  `super.name`.

- If a super constructor invocation has definitely occurred, then the expression
  is considered an invocation of the instance method `super.name`.

- Otherwise, the expression is considered an invocation of the super constructor
  named `name`.

_These ambiguities should be pretty rare, since most classes don't contain a
`call` method, and users don't typically give the constructor the same name as
an instance method. However, when they occur, these heuristics should still be
fairly reliable at determining what the user means, since it's illegal for a
code path to contain multiple super constructor invocations, and it's illegal
for a code path to invoke an instance method before a super constructor
invocation. The only places the heuristics might fail are as follows:_

- _TODO: `class B { void call() {} } class C { C() { super(); } }`. Is this an
  explicit super constructor call? Or is the super constructor call implicit and
  it's a call to `call`?_

- _TODO: `class B { void call(void v) {} } class C { C() { super(super()); }
  }`. The outer super will be mis-classified as a constructor call._

### Semantic analysis of super constructor invocations

Expression inference of a super `super(arguments)` or `super.name(arguments)` is
performed as follows:

TODO: write

TODO: explain that it's void.

TODO: it can't be invoked from a callback

### Soundness

To preserve the soundness guarantees that were previously 

### Mixed style and backward compatibility

To avoid a "syntactic cliff" between the new style 

To minimize breakage of existing Dart programs, any constructor that does not contain an expression of the form `super(arguments)` or `super.name(arguments)` (where `name` matches the name of an accessible super constructor) 

### Ambiguities

#### Method/constructor ambiguity

Currently, it is allowed for a class to declare an instance method and a
constructor with the same name. 

### Ambiguity with `call`

Previously, if the superclass declared a `call` method, the syntax
`super(arguments)` would refer implicitly to `super.call`. For example:

```dart
class B {
  void call(int i) {
    print('B.call($i)');
  }
}

class C extends B {
  C() {
    super(123); // Prints `B.call(123)`
  }
}
```

Under this proposal, the syntax `super(arguments)`, if it appears inside a generative constructor, is always interpreted to 

### Flow analysis

To ensure soundness, flow analysis is extended to enforce following
restrictions:

- No code path may write to a non-late final field more than once.

- No code path may invoke a super constructor more than once.

- No code path 

- No code path may refer to `this`, either implicitly or explicitly, 

## Grammar

Note ambiguity between super instructor invocation and `super.call` invocation.

## Semantics

## Consts

## CFE implementation details

What happens during phase 1? Do we need to know what exists on super before
running flow analysis? Before running the body builder?

## Analysis server consequences

Extract method should determine whether to extract a static method or not

## Backend consequences

- Need to be able to insert calls to `super` after any expression
