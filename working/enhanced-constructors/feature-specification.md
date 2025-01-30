# Enhanced Constructors Feature Specification

Author: Paul Berry

Status: Under review

Version 1.0 (see [CHANGELOG](#CHANGELOG) at end)

## Summary

This proposal extends the set of actions that can be performed in the body of a
non-redirecting generative constructor to include writing to non-late final
fields, and explicitly invoking super constructors.

This makes constructors more flexible, avoids the need for constructor
initializer lists, and simplifies the interaction between augmentations and
constructors (TODO: talk about augmentations).

To preserve soundness, flow analysis is enhanced to ensure that a reference to
`this` cannot escape from a constructor body before the object has been
completely constructed.

## Background

Dart follows the tradition of C++ and similar languages in requiring super
constructor invocations and final field assignments to occur prior to the
constructor body, in a so-called "initializer list". For example, in the code
below, the constructor for class `C` performs three actions: the assignment `j =
x + 1`, the super constructor invocation `super(x * 2)`, and the ordinary method
invocation `m()`. The first two of those actions are done using initializer list
syntax, prior to the `{` that begins the constructor body, and the third action
is an ordinary statement, inside the constructor body.

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

The reason is because if we allowed arbitrary super calls and final field
assignments in a constructor body, the user could break the language's soundness
guarantees by doing one of the following things:

- Reading from a field beore its initial value has been written.

- Calling a superclass method, getter, or setter before calling a super
  constructor (this could break soundness by causing the superclass to read from
  a field before its initial value has been written).

- Writing to a non-late final field more than once.

- Calling a super constructor more than once on the same object (this could
  break soundness by causing the base class to write to a non-late final field
  more than once).

However, there is another way we could guarantee soundness, without forcing the
user to use a different syntax for initializers and statements: by using flow
analysis to track the progress of initialization through the constructor
body. That's what this proposal aims to do.

## Proposal

The following kinds of expressions will become legal within the body of a
non-redirecting generative constructor:

- A write to a non-late final field, either via an explicit `this` reference
  (`this.FIELDNAME = VALUE`) or an implicit `this` reference (`FIELDNAME =
  VALUE`). _Note that in this document, all-caps names are metasyntactic
  variables._

  - These are the only two syntaxes that are recognized as a valid write to a
    non-late final field. Other syntaxes that are semantically equivalent
    (e.g. `(this).FIELDNAME = VALUE`) are not permitted.

- A call to a super constructor, using the syntax `super(ARGUMENTS)` (for an
  unnamed constructor) or `super.NAME(ARGUMENTS)` (for a named constructor). For
  the rest of this document, such an expression is called a "`super` constructor
  invocation expression".

With the restriction that `super` constructor invocation expressions may only
appear as the top level expression within an expression statement. _Rationale:
this simplifies ambiguity resolution (see TODO), and doesn't significantly
reduce expressive power. It may also simplify the implementation._

To ensure soundness, flow analysis will be modified to ensure, at compile time,
that all reachable control flow paths through a generative constructor:

- Contain exactly one invocation of either another generative constructor or of
  a super constructor.

- Write to every non-late final field exactly once prior to invoking a super
  constructor.

- Do not write to any non-late final field after invoking a super constructor.

- Do not explicitly or implicitly access `this` in any way prior to invoking a
  super constructor, except:

  - To perform the required writes to non-late final fields prior to invoking a
    super constructor.

  - To read from fields that have already been written to.

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

can now be rewritten to:

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
to non-late final fields, or `super` constructor invocation expressions.

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
below (TODO: link), but in a nutshell, if neither the body nor the initializer
list of a generative constructor contains an explicit `super` constructor
invocation expression, then an implicit call to `super()` is considered to occur
at the earliest point(s) in the constructor body at which it would be sound to
do so.

For example, this constructor from the analyzer's `AwaitExpressionImpl` class:

```dart
  AwaitExpressionImpl({
    required this.awaitKeyword,
    required ExpressionImpl expression,
  }) : _expression = expression {
    _becomeParentOf(_expression);
  }
```

could be rewritten to:

```dart
  AwaitExpressionImpl({
    required this.awaitKeyword,
    required ExpressionImpl expression,
  }) {
    _expression = expression;
    _becomeParentOf(_expression);
  }
```

With the implicit call to `super()` occurring right after the assignment
`_expression = expression;`.

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
    g = () { print(i); }; // prints the current value of `this.i`
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

## Details

### Parser support

No additional parser support is needed to support this feature, since the two
new pieces of syntax (writes to final fields and super/this constructor
invocations) are already accepted by the parser.

### Flow analysis enhancements

#### New boolean state

When flow analysis is used on a non-redirecting generative constructor, it
tracks the following additional pieces of boolean state, for every control flow
path:

- For each non-late field in the containing class, an `assigned` boolean that, if true,
  indicates that the field is definitely assigned.

- For each non-late final field in the containing class, an `unassigned` boolean
  that, if true, indicates that the field is definitely unassigned.

- A single `constructed` boolean that, if true, indicates that a constructor
  invocation has definitely occurred.

- A single `unconstructed` boolean that, if true, indicates that a constructor
  invocation has definitely _not_ occurred.

The behavior of all these boolean variables in the presence of a flow analysis
`join` operation is the same as it is for the other boolean variables tracked by
flow analysis. _These rules are:_

- _When joining two reachable control flow paths `A` and `B` to form a joined
  control flow path `C`, any given boolean variable is true in `C` if and only
  if it is true in both `A` and `B`._

- _When joining a reachable control flow path `A` with an unreachable control
  flow path `B` to form a joined control flow path `C`, all boolean variables
  take on the same values in `C` as they do in `A`. (And vice versa with the
  roles of `A` and `B` reversed.)_

- _When joining two unreachable control flow paths `A` and `B` to form a joined
  control flow path `C`, if there exists a split point from which `A` is
  reachable but `B` is not, all boolean variables take on the same values in `C`
  as they do in `A`. (And vice versa with the roles of `A` and `B` reversed.)_

- _When joining two unreachable control flow paths `A` and `B` to form a joined
  control flow path `C`, if there is no difference in the reachability of `A`
  and `B` from prior split points, then any given boolean variable is true in
  `C` if and only if it is true in both `A` and `B`._

_Note that it's possible for a field's `unassigned` and `assigned` booleans to
both be `false`; this indicates that control flow has reached a point where flow
analysis cannot tell whether the field has been assigned. This is no different
from how local variables are handled. Similarly, it's possible for the
`constructed` and `unconstructed` booleans to both be `false`; this indicates
that control flow has reached a point where flow analysis cannot tell whether a
constructor invocation has occurred._

#### New state initialization

At the start of analyzing a constructor (prior to analyzing the initializer
list, if there is one), these new state variables are initialized as follows:

- `constructed` is initialized to `false`.

- `unconstructed` is initialized to `true`.

- For each non-late field in the class:

  - If the field's declaration has an initializer, then the field's `assigned`
    boolean is initialized to `true` and its `unassigned` boolean is initialized
    to `false`.

  - Otherwise, if the constructor has a `this.NAME` parameter corresponding to
    the field, then the field's `assigned` boolean is initialized to `true` and
    its `unassigned` boolean is initialized to `false`.

  - Otherwise, if the field is non-final and has a nullable type, then the
    field's `assigned` boolean is initialized to `true` and its `unassigned`
    boolean is initialized to `false`, and the field is considered to take on an
    initial value of `null`.

  - Otherwise, the field's `assigned` boolean is initialized to `false` and its
    `unassigned` boolean is initialized to `true`.

#### New state updates

When flow analysis encounters a write to a non-final field (either in an
initializer or in the constructor body), it updates the field's `assigned`
boolean to `true` and its `unassigned` boolean to `false`, and updates the
`thisUnused` boolean to `false`.

When flow analysis encounters a `super` initializer or a `super` constructor
invocation expression, or it inserts an implicit `super` constructor invocation
expression (see TODO: link), after processing the arguments, it updates the
`constructed` boolean to `true`, the `unconstructed` boolean to `false`, and the
`thisUnused` boolean to `false`.

#### New flow analysis errors

If a write to a non-late final field occurs at a point in control flow where the
field's `unassigned` boolean is `false`, there is a compile-time error (_final
field possibly initialized twice_).

If a write to a non-late final field occurs inside a nested function or closure,
there is a compile-time error (_final field cannot be initialized inside a
nested function or closure_).

If a read of a non-late field occurs at a point in control flow where the
field's `assigned` boolean is `false`, there is a compile-time error (_read of
possibly uninitialized field_).

If a `super` constructor invocation expression occurs at a point in control flow
where any non-late field's `assigned` boolean is `false`, there is a
compile-time error (_field uninitialized at time of super call_).

If a `super` constructor invocation expression occurs at a point in control flow
where the `unconstructed` boolean is `false`, there is a compile-time error
(_super constructor possibly called twice_).

If a `super` constructor invocation expression occurs inside a nested function
or closure, there is a compile-time error (_super constructor invocation
expression cannot occur inside a nested function or closure_).

If the `constructed` boolean is `false` at the point where control flow reaches
the end of the constructor body, there is a compile-time error (_a control path
failed to invoke a super constructor_).

If any explicit or implicit use of `this` is made that is not a read or write of
a field declared in the class itself, at a point in control flow where the
`constructed` boolean is `false`, then there is a compile-time error (_instance
is not fully constructed yet_). _Examples include:_

- _A method or operator invocation on `this`._

- _A call to an explicitly declared getter, setter, or method (possibly
  abstract) either in the class or one of its superclasses._

- _A read or write of a field declared in a superclass._

- _A read or write of an abstract field._

- _A call to a setter, getter, or method that is part of the class's interface
  due to the presence of an `implements` clause, and not backed by a field
  declared in the class.

- _Any other use of `this` that is not syntactically part of a read or write of
  a field._

If any explicit or implicit use of `this` is made that does not resolve to an
invocation of a super constructor, at a point in control flow where the
`constructed` boolean is `false`, then there is a compile-time error (_instance
is not fully constructed yet_).

### Insertion of implicit super constructor invocations

Prior to type inference of a constructor, the constructor's initializer list and
body are scanned to determine whether they already contain an initializer or an
expression statement of the form `super(ARGUMENTS)`, where the superclass
contains an unnamed constructor, or of the form `super.NAME(ARGUMENTS)`, where
the superclass contains a constructor with a name matching `NAME`.

If neither of these forms is found, an implicit super constructor invocation
will be inserted at the first statement boundary in any control flow path which
(a) is inside the constructor body, and (b) has a `true` value for the
`assigned` booleans of all non-late fields. (_This is the earliest point at
which the user could have written the super constructor invocation explicitly._)

_Note that expressions of the above forms that do not constitute a complete
initializer or the top level expression in an expression statement do not
prevent an implicit super constructor invocation from being inserted, because
they cannot represent super constructor invocations._

_Note that the only points where a super constructor invocation might be
inserted are at the top of the constructor body, and immediately after a
statement that includes an assignment to a non-late field._

### Disambiguation of super constructor invocations from super method invocations

In a generative constructor, the following expressions are now potentially
ambiguous:

- `super(ARGUMENTS)` could be either an invocation of an unnamed constructor in
  the superclass, or the invocation of an instance method `call` in the
  superclass or one of its ancestors.

- `super.NAME(ARGUMENTS)` could be either an invocation of an accessible
  constructor named `NAME` in the superclass, or the invocation of an instance
  method or getter named `NAME` in the superclass or one of its ancestors.

These forms are all disambiguated as follows:

- If the expression is the top level expression in an expression statement, and
  the `constructed` boolean maintained by flow analysis is `false` at the point
  in control flow where the expression appears, it is treated as a constructor
  invocation.

- Otherwise it is treated as a method or getter invocation.

_To see why this disambiguation rule makes sense, consider the fact that a
`super` constructor invocation expression can only legally occur when the
`constructed` boolean is `false`, whereas an invocation of an instance method or
getter in the superclass can only legally occur when the `constructed` boolean
is `true`. Therefore, if there is an interpretation in which the program is
legal, this disambiguation rule is sufficient to find it._

_Implementation note: it is likely that the analyzer will want to adopt a more
complex disambiguation rule in the case of erroneous code, so that the resulting
error messages are more meaningful. For example, if `NAME` is the name of a
superclass constructor, and not the name of a superclass getter or method, then
it would be beneficial for the analyzer to interpret `super.NAME(ARGUMENTS)` as
a super-constructor invocation even if the `constructed` boolean is `true`; that
way, the error message will be "super constructor called twice" rather than "no
such method"._

_Note that this disambiguation process needs to occur before any of the
`ARGUMENTS` are visited, since the type of the constructor, method, or function
object being invoked affects the downward inference contexts that will be
supplied when analyzing `ARGUMENTS`. But the point at which the "super
constructor called twice" error is detected is after visiting `ARGUMENTS`. This
is the reason for the restriction that `super` and `this` constructor invocation
expressions may only appear as the top level expression within an expression
statement; it ensures that the `constructed` and `unconstructed` booleans won't
change state between the point of disambiguation and the point of error
reporting, which could create a lot of user confusion._

## Const constructors

To allow const constructors to be written in the new style, the restriction that
a const constructor must not have a body is dropped. Instead, a const
constructor is allowed to have a block body, but all statements in the block
must take one of the following forms, or there is a compile-time error:

- A write to a non-late final field (`this.FIELDNAME = VALUE` or `FIELDNAME =
  VALUE`), where `VALUE` is a potentially constant expression.

- A call to a super constructor (`super(ARGUMENTS)` or `super.NAME(ARGUMENTS)`),
  where all the expressions in `ARGUMENTS` are potentially constant expressions.

- An assert statement (`assert(CONDITION)` or `assert(CONDITION, MESSAGE)`),
  where `CONDITION` and `MESSAGE` are potentially constant expressions.

These conditions ensure that it will still be tractable for the constant
evaluator to analyze constants that invoke const constructors.

## Backward compatibility

If a constructor is written in the "old style" (that is, it would be accepted
by the current Dart compiler and analyzer), then I believe it is is fairly
straightforward to show that none of the new flow analysis errors will fire,
with one exception: if there is no explicit `super` initializer, and there is a
failure in the heuristic for determining whether a super constructor invocation
needs to be inserted, then the constructor might have an unintended change in
meaning. This could happen either because the constructor contains a call to a
`call` method defined in the superclass, for example:

```dart
class B {
  void call() { ... }
}

class C {
  C() {
    // Today this is interpreted as a call to `B.call`; with enhanced
    // constructors it will be interpreted as a call to the unnamed constructor
    // of `B`.
    super();
  }
}
```

Or because the constructor contains a call to a superclass method that shares
its name with a superclass constructor, for example:

```dart
class B {
  B();
  B.m();
  void m() { ... }
}

class C {
  C() {
    // Today this is interpreted as a call to the `B.m()` method; with enhanced
    // constructors it will be interpreted as a call to the `B.m()` constructor.
    super.m();
  }
}
```

These backward incompatibilities should be exceptionally rare.

## Back-end consequences

### Constructors are less tightly bound to super constructors

With today's dart, each non-redirecting generative constructor is statically
bound to a single super constructor. With enhanced constructors, it is possible
for a generative constructor to choose at runtime which super constructor to
invoke. For example:

```dart
class C {
  C(bool b) {
    if (b) {
      super.foo();
    } else {
      super.bar();
    }
  }
}
```

TODO I AM HERE

## CFE implementation details

What happens during phase 1? Do we need to know what exists on super before
running flow analysis? Before running the body builder?

## Analysis server consequences

Extract method should determine whether to extract a static method or not

## Backend consequences

- Need to be able to insert calls to `super` after any expression

- Need to be able to access partially initialized objects

- Talk about strategies for when the allocation happens (at the beginning of the
  constructor call, if unsafely writing to fields is permissible, or at the
  point of the super call, if we need to compile to a lower lever representation
  with its own soundness requirements).

TODO: back-end consequences: it must be possible to access `this` on an
incomplete object. E.g. prior to the call to `super()`, a closure could be
created that reads from a variable in `this`.

## Breakingness

- Breaking if `this(ARGUMENTS)` or `this.NAME(ARGUMENTS)` exists in a
  constructor that the user intends to be old-style.

- Ambiguity with `super.NAME`.

TODO: what about const constructors?

TODO: document how implicit super constructor invocations might be added inside
loops.

TODO: document that one of the consequences of the flow analysis rules is that
super constructor invocations can't be added inside loops (and verify that this
is in fact the case).

TODO: _Implicit `super()`. If the user intends to take advantage of an implicit
call to `super()`, but the constructor body contains an ambiguous invocation
that looks like it could be a super-constructor invocation, or a call to a
constructor in the current class, then the algorithm in (TODO: reference) will
have already decided that no implicit super constructor invocation should be
inserted, and so the ambiguous invocation will be interpreted as a
super-constructor invocation. In the rare event that this happens, the user can
work around it by adding an explicit call to `super()` at the top of the
constructor body._
