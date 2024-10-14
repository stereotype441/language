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
`this` cannot "escape" from a constructor body before the object has been
completely constructed.

## Background

Dart follows the tradition of C++ and similar languages in requiring super
constructor invocations and final field assignments to occur prior to the
constructor body, in a so-called "initializer list". For example, in the code
below, the constructor for class `C` performs three actions: the assignment `j =
x + 1`, the super-constructor invocation `super(x * 2)`, and the ordinary method
invocation `f(this)`. But the first two of those actions must be performed using
initializer list syntax, prior to the `{` that begins the constructor body,
whereas the third action can be written as an ordinary statement, inside the
constructor body (indeed, it must, since it refers to `this`).

```dart
class B {
  final int i;
  B(this.i);
}

class C extends B {
  final int j;
  C(int x)
      : j = x + 1,
        super(x * 2) {
    f(this);
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
    f(this);
  }
}
```

The reason we require the user to use an initializer list to initialize `j` and
to call the super-constructor is because initializer lists are restricted in a
way that ensures soundness. In particular, in an initializer list:

- It is not permissible to refer to `this` either explicitly or implicitly,

- And all final fields in the class must be initialized prior to invoking the
  super-constructor. (If there is no explicit super-constructor invocation in
  the initializer list, an implicit `super()` invocation is appended to the
  initializer list.)

These two restrictions together ensure that it is not possible for any
constructor in the super-class chain to refer to `this` before _all_ fields have
been initialized. Therefore, even though object construction can be a multi-step
process, it's never possible for a program to try to read from an uninitialized
field.

However, these restrictions come at a cost, both in terms of making the language
less approachable (since they require the user to learn a special syntax that's
used only in constructors), and in terms of flexibility, since they require any
given constructor to always initialize fields in the same order, and always call
the same super-constructor. Also, these restrictions have complicate our efforts
to allow augmentations to apply to constructors.

## Proposal

This proposal addresses these costs by allowing the following kinds of
expressions to appear within the body of a generative constructor:

- A write to a non-late final field, either via an implicit `this` reference
  (`this.fieldName = value`) or an implicit `this` reference (`fieldName =
  value`).

- A call to a super-constructor, using the syntax `super(arguments)` (for an
  unnamed constructor) or `super.name(arguments)` (for a named constructor).

- A call to another generative constructor in the same class, using the syntax
  `this(arguments)` (for an unnamed constructor) or `this.name(arguments)` (for
  a named constructor).

To ensure soundness, flow analysis will be modified in order to ensure, at
compile time, that all control flow paths either:

- Invoke another generative constructor exactly once, prior to accessing `this`,

- Or invoke a super constructor exactly once, after writing to every non-late
  final field exactly once, and prior to accessing `this` in any way that might
  lead to unsoundness (precise details below).

This allows the vast majority of constructor initializer lists to be converted
into statements in the constructor body in a straightforward way. For example,
this constructor from the analyzer's `VariableDeclarationImpl` class:

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

### Scoping differences

TODO

### Mixed style

To avoid a "syntactic cliff" between the old and new styles of coding generative
constructors, it is allowed to mix the two styles. That is, a generative
constructor with an initializer list is allowed to contain, in its body, a write
to a non-late final field, or an invocation of a super-constructor.

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
below, but in a nutshell, if neither the body nor the initializer list of a
generative constructor contains an explicit super-constructor invocation, then
an implicit call to `super()` is considered to occur just before execution of
the body.

### Interaction with `this.` and `super.` parameters

Today, Dart allows a constructor parameter to use the syntax `this.` to
implicitly initialize a field, and the syntax `super.` to implicitly pass a
parameter to the super-constructor.

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

TODO: fully specify super. behvaior.

### Redirecting generative constructors



### Interaction with augmentations

## Details

### Parser support

No additional parser support is needed to support this feature, since the two
new pieces of syntax (writes to final fields and super-constructor invocations)
are already accepted by the parser.

### Insertion of implicit super-constructor invocations

TODO

### Flow analysis enhancements

When flow analysis is used on a generative constructor, it tracks the following
additional pieces of boolean state, for every control flow path:

TODO: explanatory text saying the effect of each.

- For each final field in the containing class, whether the field is definitely
  assigned (initial state: `true` if the field is initialized at the site of its
  declaration or in the initializer list, otherwise `false`).

- For each final field in the containing class, whether the field is definitely
  unassigned (initial state: `false` if the field is initialized at the site of
  its declaration or in the initializer list, otherwise `true`).

- Whether a super-constructor invocation has definitely occurred (initial state:
  `true` if the initializer list contains a super-constructor invocation,
  otherwise `false`).

- Whether a super-constructor invocation has definitely _not_ occurred (initial
  state: `false` if the initializer list contains a super-constructor
  invocation, otherwise `true`).

### Semantic analysis of field writes

Expression inference of `this.f = e_1` (where `f` is the name of a final field
in the containing class), in context `K`, produces an elaborated expression `m`
with static type `T`, where `m` and `T` are determined as follows:

- If the expression is not contained within the body of a generative
  constructor, it is a compile time error.

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

- Let `f` be definitely assigned, and not definitely unassigned, at the point in
  control flow after execution of `m`.

It is a compile-time error for the target of a compound assignment or pre/post
increment/decrement to take the form `this.f`, where `f` is the name of a final
field in the containing class. _This was previously allowed if the field was
late, but it was guaranteed to fail at runtime._

The same error applies if the target of a compound assignment or pre/post
increment/decrement takes the form `f`, where scope resolution rules resolve `f`
to a final field in the containing class.

It is a compile-time error for the target of an if-null assignment (`??=`) to
take the form `this.f`, where `f` is the name of a final field in the containing
class. _This was previously allowed if the field was late, but it was not
useful, since it would either fail at runtime or have no effect._

The same error applies if the target of a compound assignment or pre/post
increment/decrement takes the form `f`, where scope resolution rules resolve `f`
to a final field in the containing class.

An expression of the form `f = e_1` (where scope resolution rules resolve `f` to
a final field in the containing class) is treated as equivalent to `this.f =
e_1`.

### Disambiguation of super constructor invocations from super method invocations

TODO: rewrite with justification first.

If an expression of the form `super(arguments)` appears inside a generative
constructor, it is disambiguated during type inference, just prior to visiting
any arguments, using the first of the following heuristics that applies:

- If the superclass does not contain an unnamed constructor, and no class in the
  superclass chain defines an instance method named `call`, then it is a
  compile-time error.

- If the superclass contains an unnamed constructor, and no class in the
  superclass chain defines an instance method named `call`, then the expression
  is considered an invocation of the unnamed super-constructor.

- If a class in the superclass chain defines an instance method named `call`,
  and the superclass does not contain an unnamed constructor, then the
  expression is considered an invocation of the instance method `super.call`.

- If a super-constructor invocation has definitely occurred, then the expression
  is considered an invocation of the instance method `super.call`.

- Otherwise, the expression is considered an invocation of the unnamed
  super-constructor.

If an expression of the form `super.name(arguments)` appears inside a generative
constructor, it is disambiguated during type inference, just prior to visiting
any arguments, using the first of the following heuristics that applies:

- If the superclass does not contain an accessible constructor named `name`, and
  no class in the superclass chain defines an accessible instance method named
  `name`, then it is a compile-time error.

- If the superclass contains an accessible constructor named `name`, and no
  class in the superclass chain defines an accessible instance method named
  `name`, then the expression is considered an invocation of the
  super-constructor named `name`.

- If a class in the superclass chain defines an accessible instance method named
  `name`, and the superclass does not contain an accessible constructor named
  `name`, then the expression is considered an invocation of the instance method
  `super.name`.

- If a super-constructor invocation has definitely occurred, then the expression
  is considered an invocation of the instance method `super.name`.

- Otherwise, the expression is considered an invocation of the super-constructor
  named `name`.

_These ambiguities should be pretty rare, since most classes don't contain a
`call` method, and users don't typically give the constructor the same name as
an instance method. However, when they occur, these heuristics should still be
fairly reliable at determining what the user means, since it's illegal for a
code path to contain multiple super-constructor invocations, and it's illegal
for a code path to invoke an instance method before a super-constructor
invocation. The only places the heuristics might fail are as follows:_

- _TODO: `class B { void call() {} } class C { C() { super(); } }`. Is this an
  explicit super-constructor call? Or is the super-constructor call implicit and
  it's a call to `call`?_

- _TODO: `class B { void call(void v) {} } class C { C() { super(super()); }
  }`. The outer super will be mis-classified as a constructor call._

### Semantic analysis of super constructor invocations

Expression inference of a super `super(arguments)` or `super.name(arguments)` is
performed as follows:

TODO: write

TODO: explain that it's void.

### Soundness

To preserve the soundness guarantees that were previously 

### Mixed style and backward compatibility

To avoid a "syntactic cliff" between the new style 

To minimize breakage of existing Dart programs, any constructor that does not contain an expression of the form `super(arguments)` or `super.name(arguments)` (where `name` matches the name of an accessible super-constructor) 

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

- No code path may invoke a super-constructor more than once.

- No code path 

- No code path may refer to `this`, either implicitly or explicitly, 

## Grammar

Note ambiguity between super-instructor invocation and `super.call` invocation.

## Semantics

## Consts

## CFE implementation details

What happens during phase 1? Do we need to know what exists on super before
running flow analysis? Before running the body builder?

## Analysis server consequences

Extract method should determine whether to extract a static method or not
