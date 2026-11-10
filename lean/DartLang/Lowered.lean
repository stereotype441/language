module
public import DartLang.Elements
public import DartLang.Loc
public import DartLang.Types

namespace DartLang

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)

/--
The kinds of dynamic error (in the specification's sense) that can occur in the subset of Dart
modeled so far.

This is a placeholder. The language specification says that when a dynamic error occurs, a
corresponding error object is thrown; for a dynamic type error, the thrown object implements
`TypeError`. Once the semantics can allocate objects of core library classes, a dynamic error
will throw such an object, and this type (with `Value.error`) will go away.
-/
public inductive DynamicError where
  /--
  A dynamic type error: a failed type check at run time, such as a null check (`e!`) finding the
  null object, or a failed cast (`e as T`).
  -/
  | typeError
  /--
  A failed intrinsic check (`LoweredExpr.check` or `LoweredExpr.checkEq`), which the translator
  produces for an `Expect` assertion from the language tests. In Dart, a failed `Expect` throws an
  `ExpectException`; this placeholder stands for it.
  -/
  | expectFailed
  /--
  A failed assertion (`LoweredExpr.assert`, when assertions are enabled). In Dart, a failed
  assertion throws an `AssertionError`, carrying the assertion's message, if any; this placeholder
  stands for it (the message is evaluated, but its value isn't kept).
  -/
  | assertionFailed
  deriving Repr, BEq, DecidableEq

/-- The kinds of intrinsic check (`LoweredExpr.check`) on one value, for `Expect` assertions. -/
public inductive CheckKind where
  /-- `Expect.isTrue(v)`: `v` is `true`. -/
  | isTrue
  /-- `Expect.isFalse(v)`: `v` is `false`. -/
  | isFalse
  /-- `Expect.isNull(v)`: `v` is the null object. -/
  | isNull
  /-- `Expect.isNotNull(v)`: `v` isn't the null object. -/
  | isNotNull
  deriving Repr, BEq, DecidableEq

/--
An *integer mode*: how the arithmetic of a function treats results that don't fit in 64 bits.

Every Dart `int` is represented by its mathematical value, a Lean `Int` (`Value.int`). On the
native platforms, Dart's integers are 64-bit two's complement numbers, and arithmetic wraps
around; on the web, they're JavaScript numbers. A proof about code that is only correct because of
wrapping (such as a hash function) needs to know that it wraps, but most code never overflows, and
a proof about it shouldn't depend on how overflow behaves. So each function's arithmetic runs in
one of three modes, chosen per function (`SemanticParams.intModeOf`):
- `wrap64`: results wrap around into 64-bit two's complement, as the VM does;
- `checked`: a result that doesn't fit in 64 bits gets stuck. A program that runs safely in this
  mode never overflows, so it behaves the same in `wrap64` mode; and
- `unbounded`: results are exact mathematical integers. A proof in this mode shows that the code
  would be correct if integers were unbounded.

Integer literals are always in 64-bit range, whatever the mode.
-/
public inductive IntMode where
  /-- Results wrap around into 64-bit two's complement. -/
  | wrap64
  /-- A result that doesn't fit in 64 bits gets stuck. -/
  | checked
  /-- Results are exact mathematical integers. -/
  | unbounded
  deriving Repr, BEq, DecidableEq

/--
The result of an arithmetic operation whose exact result is `n`, in integer mode `mode` (see
`IntMode`): `none` if the operation gets stuck.
-/
@[expose]
public def IntMode.arith : IntMode → Int → Option Int
  | .wrap64, n => some (n.bmod (2 ^ 64))
  | .checked, n => if -2 ^ 63 ≤ n ∧ n < 2 ^ 63 then some n else none
  | .unbounded, n => some n

/-- The binary operators on integers: arithmetic (`+`, `-`, `*`) and comparisons. -/
public inductive IntBinOp where
  /-- `+` -/
  | add
  /-- `-` -/
  | sub
  /-- `*` -/
  | mul
  /-- `<` -/
  | lt
  /-- `<=` -/
  | le
  /-- `>` -/
  | gt
  /-- `>=` -/
  | ge
  deriving Repr, BEq, DecidableEq

/-- Whether binary operator `op` is a comparison (producing a `bool`, not an `int`). -/
@[expose]
public def IntBinOp.isComparison : IntBinOp → Bool
  | .lt | .le | .gt | .ge => true
  | .add | .sub | .mul => false

/--
The UTF-16 code units of a Lean string: how a Dart string with the same characters is stored (see
`ConstValue.string`). A character outside the Basic Multilingual Plane becomes a surrogate pair.
(A Dart string can also hold unpaired surrogates, which a Lean string can't; this is for writing
strings that don't.)
-/
@[expose]
public def DartString.ofString (s : String) : List UInt16 :=
  s.toList.flatMap fun c =>
    let n := c.toNat
    if n < 0x10000 then [n.toUInt16]
    else
      let m := n - 0x10000
      [(0xD800 + m / 0x400).toUInt16, (0xDC00 + m % 0x400).toUInt16]

/--
A structural description of a constant value: two evaluations of equal descriptions give the same
object (see `LoweredExpr.constant`). So far, only the null object, booleans, integers and strings
can be described; constant lists, maps, sets and instances of classes will describe their
components as `ConstValue`s too.
-/
public inductive ConstValue where
  /-- The null object. -/
  | null
  /-- The boolean `b`. -/
  | bool (b : Bool)
  /-- The integer `n`. -/
  | int (n : Int)
  /--
  The string whose UTF-16 code units are `cu`. A Dart string is a sequence of UTF-16 code units,
  which needn't be valid UTF-16 (it can hold unpaired surrogates).
  -/
  | string (cu : List UInt16)
  deriving Repr, DecidableEq

/-
`Value`, `LoweredExpr` and `EctxItem` are mutually inductive: a value may hold a captured
continuation (a list of evaluation context items), and evaluation context items hold the
expressions still to be evaluated.
-/
mutual

/--
A run-time value: in the specification's terms, an object. The null object, booleans, integers
and error objects are represented directly; other objects live in the heap and are referred to by
location.
-/
public inductive Value where
  /-- The null object. -/
  | null
  /-- The object `true` or `false`. -/
  | bool (b : Bool)
  /--
  An integer: an instance of `int`. Every Dart `int` is represented by its mathematical value, a
  Lean `Int` (which is unbounded). Integer literals are always in 64-bit range; what arithmetic
  does with a result outside that range depends on the integer mode of the function it's in (see
  `IntMode`).
  -/
  | int (n : Int)
  /-- A reference to the object stored at location `ℓ`. -/
  | obj (ℓ : Loc)
  /-- The object thrown when dynamic error `e` occurs. -/
  | error (e : DynamicError)
  /--
  A captured continuation: the evaluation context items around a suspended computation,
  innermost first. Reserved for constructs that capture continuations (such as `await`); nothing
  creates one yet.
  -/
  | cont (k : List EctxItem)

/--
Lowered, fully type-checked AST form.

Note that we make no distinction between statements and expressions. This is for future
compatibility with the Iris framework.
-/
public inductive LoweredExpr where
  /--
  A reference to local variable or formal parameter `v`, whose static type (after any promotion)
  is `T`.
  -/
  | var (v : Variable) (T : τ)
  /-- An application of the null check operator, `m!`. -/
  | nullCheck (m : LoweredExpr)
  /-- A cast expression, `m as T`. -/
  | as (m : LoweredExpr) (T : τ)
  /-- An is-expression (a type test), `m is T`. -/
  | is (m : LoweredExpr) (T : τ)
  /-- The null literal, `null`. -/
  | null
  /-- A boolean literal, `true` or `false`. -/
  | bool (b : Bool)
  /-- An integer literal. -/
  | int (n : Int)
  /--
  A local variable declaration of `v`, with type `T`. Its scope is the rest of the enclosing
  `block`.

  `startsNull` says whether the variable starts out holding the null object. Otherwise, it starts
  out unassigned, and it is an error to read it before it is assigned. Flow analysis sets
  `startsNull` based on whether `v` is final and whether `T` is nullable, as Dart requires.
  -/
  | declare (v : Variable) (T : τ) (startsNull : Bool)
  /--
  A conditional: evaluates `m₂` if `m₁` evaluates to `true`, and `m₃` otherwise. Its static type
  is `T`.
  -/
  | cond (m₁ m₂ m₃ : LoweredExpr) (T : τ)
  /--
  A block statement, `{ m₁ … mₙ }`, which executes its elements in order. Since `LoweredExpr`
  doesn't distinguish statements from expressions, its value is the null object.
  -/
  | block (exprs : List LoweredExpr)
  /--
  A property extraction, `m.p`: a read of property `p` of the value of `m`, whose static type
  (after any promotion) is `T`.
  -/
  | propertyGet (m : LoweredExpr) (p : Property) (T : τ)
  /--
  An assignment to local variable or formal parameter `v`, `v = m`: evaluates `m`, stores its
  value in `v`, and evaluates to that value. (Kernel calls this a `VariableSet`.) If `v` is
  `final`, it must still be unassigned.
  -/
  | variableSet (v : Variable) (m : LoweredExpr)
  /--
  A placeholder for a construct that the translator from Kernel doesn't support yet, of static
  type `T`. `kind` names the construct (for example, the Kernel node's class), so that a program
  that gets stuck on it says why. It has no head step: running it gets stuck.
  -/
  | unsupported (kind : String) (T : τ)
  /--
  A call of the top-level function whose key is `f`, with arguments `args`, evaluated left to
  right. The static type of the call expression is `T`. The function's declaration is looked up in
  the program's function table (`SemanticParams.functions`). A function's key identifies it
  uniquely in the program (for example, its library's URI together with its name); it isn't
  necessarily the function's name, so functions with the same name in different libraries have
  different keys.

  TODO(paulberry): So far all arguments are positional. Named arguments are meant to be added as a
  separate list giving each argument's name, if any, so that they can be intermixed with positional
  arguments and evaluated in source order; only binding arguments to formal parameters will depend
  on names.
  -/
  | call (f : String) (args : List LoweredExpr) (T : τ)
  /-- A return statement, `return m;`. (`return;` is `ret null`.) -/
  | ret (m : LoweredExpr)
  /--
  An intrinsic check of the value of `m`, for an `Expect` assertion of kind `kind` (such as
  `Expect.isTrue(m)`): completes normally with the null object if the check holds, and otherwise
  throws.
  -/
  | check (kind : CheckKind) (m : LoweredExpr)
  /--
  An intrinsic check that the values of `m₁` and `m₂` are equal, for `Expect.equals(m₁, m₂)`:
  completes normally with the null object if they are, and otherwise throws. Only the null object,
  booleans and integers can be compared; comparing anything else gets stuck.
  -/
  | checkEq (m₁ m₂ : LoweredExpr)
  /--
  A loop that runs `m` over and over, forever, until `m` completes abruptly (typically by a
  `break` out of an enclosing labeled statement, `labeled`). Its static type is `Null`, as for any
  statement.

  Dart's loops are expressed with `loop`, `labeled` and `brk`, where `L` is the loop's break label
  and `C` its continue label:
  - `while (c) b` is `labeled L (loop (cond c (labeled C b) (brk L)))`;
  - `do b while (c)` is `labeled L (loop (seq (labeled C b) (cond c null (brk L))))`; and
  - `for (init; c; upd) b` is `block [init…, labeled L (loop (cond c (seq (labeled C b) upd…)
    (brk L)))]`.

  So `break` is `brk L`, and `continue` is `brk C`: it ends the current iteration's body, as Kernel
  expresses it too. Declarations in the body are inside the body's block, so each iteration gets
  fresh cells for them. A `for` loop's own variables are declared once, outside the loop, whereas
  Dart gives each iteration its own copies of them; the difference can only be observed by a
  closure that captures one, and closures aren't modeled yet.
  -/
  | loop (m : LoweredExpr)
  /--
  A labeled statement, `l: m`: runs `m`, and completes normally (with the null object, as a
  statement) when `m` completes normally, or when a `break l` inside `m` breaks out of it. Labels
  are unique within a function.
  -/
  | labeled (l : String) (m : LoweredExpr)
  /-- A break statement, `break l;`, which breaks out of the enclosing labeled statement `l`. -/
  | brk (l : String)
  /--
  A binary operator on integers, `m₁ op m₂`, which evaluates `m₁` and then `m₂`. An arithmetic
  operator computes its result in integer mode `mode` (see `IntMode`). Its static type is `int` for
  an arithmetic operator, and `bool` for a comparison.

  The mode is the mode of the function that the operator is in. Since a step can't see which
  function it's running in, the mode is recorded here: the translator leaves it `none`, and calling
  the function fills it in (`LoweredExpr.withIntMode`). An operator whose mode is `none` gets stuck,
  so a program's entry point (`main`) has to be run as a call.
  -/
  | intBin (op : IntBinOp) (mode : Option IntMode) (m₁ m₂ : LoweredExpr)
  /--
  Unary minus on an integer, `-m`, computed in integer mode `mode`, which is filled in as for
  `intBin`.
  -/
  | intNeg (mode : Option IntMode) (m : LoweredExpr)
  /--
  Equality, `m₁ == m₂`, of values that are each the null object, a boolean or an integer: evaluates
  `m₁` and then `m₂`, and evaluates to whether they're the same value. Comparing anything else gets
  stuck, since `==` on other objects runs user code (an `operator ==` method). The translator uses
  it only when both operands' static types are `Null`, `bool` or `int`, or nullable versions of
  them.
  -/
  | primEq (m₁ m₂ : LoweredExpr)
  /--
  An instance creation, `C(args)`, by the generative constructor whose key is `k` (see
  `SemanticParams.constructors`), with arguments `args`, evaluated left to right. Its static type
  is `T`. It allocates a new object of the constructor's class, whose instance variables all start
  out uninitialized, runs the constructor on it (`ctorRun`), and evaluates to the object. (A factory
  constructor is an ordinary function, called with `call`.)
  -/
  | new (k : String) (args : List LoweredExpr) (T : τ)
  /--
  A `super(args)` or `this(args)` call in a constructor's initializer list: runs the generative
  constructor whose key is `k` on the object that `m` (which is `this`) refers to, with arguments
  `args`. `m` is evaluated first, then `args`, left to right.
  -/
  | initCtor (m : LoweredExpr) (k : String) (args : List LoweredExpr)
  /--
  An initializer of the instance variable whose key is `name` (see `ClassDecl.instanceVariables`;
  the key, not the instance variable's name) of the object that `m` (which is `this`) refers to,
  `x = m₂`: evaluates `m` and then `m₂`, and stores the value in the instance variable's cell,
  directly (an overriding setter isn't run, and a `final` instance variable can be initialized).
  It completes normally with the null object.

  A constructor's initializers run after the initializers in the instance variables' declarations,
  so a non-`final` instance variable can be initialized twice: once by its declaration, and then by
  the constructor's initializer list, which overwrites the first value. Dart rejects a program that
  initializes a `final` instance variable twice, or one instance variable twice in one initializer
  list, so no check is needed at run time.
  -/
  | initField (m : LoweredExpr) (name : String) (m₂ : LoweredExpr)
  /--
  An assignment to property `name` of the value of `m`, `m.name = m₂`: evaluates `m` and then
  `m₂`, runs the setter named `name=` of the object that `m` refers to (the implicit setter of an
  instance variable stores the value in the instance variable's cell), and evaluates to the value
  of `m₂`.
  -/
  | propertySet (m : LoweredExpr) (name : String) (m₂ : LoweredExpr)
  /--
  A method call, `m.name(args)`, whose static type is `T`: evaluates `m` and then `args`, left to
  right, and calls the method named `name` of the object that `m` refers to, as its class's
  dispatch table gives it (*dynamic dispatch*; see `ClassDecl.dispatch`).

  The translator expresses `==` on objects as a call of the method named `==`, with Dart's handling
  of `null` written out: `a == b` is `a.==(b)` if `a` can't be `null`.
  -/
  | methodCall (m : LoweredExpr) (name : String) (args : List LoweredExpr) (T : τ)
  /--
  A super method call, `super.name(args)`, whose static type is `T`, on the receiver `m` (which is
  `this`): evaluates `m` and then `args`, left to right, and calls the method named `name` in the
  dispatch table of the class whose key is `slot`.

  A `super` access is resolved in the superclass of the class whose declaration provides the member
  it's in (see `Member.proc`), which a step can't see. So the translator leaves `slot` as `none`,
  and running the member's body fills it in (`LoweredExpr.withSuperclass`), as for integer modes.
  An access whose `slot` is `none` gets stuck.
  -/
  | superCall (m : LoweredExpr) (name : String) (slot : Option String) (args : List LoweredExpr)
      (T : τ)
  /--
  A super property extraction, `super.name`, whose static type (after any promotion) is `T`, on
  the receiver `m` (which is `this`): reads property `name` as the dispatch table of the class
  whose key is `slot` gives it (see `superCall` for `slot`).
  -/
  | superGet (m : LoweredExpr) (name : String) (slot : Option String) (T : τ)
  /--
  A super property assignment, `super.name = m₂`, on the receiver `m` (which is `this`): evaluates
  `m` and then `m₂`, runs the setter `name=` as the dispatch table of the class whose key is `slot`
  gives it (see `superCall` for `slot`), and evaluates to the value of `m₂`.
  -/
  | superSet (m : LoweredExpr) (name : String) (slot : Option String) (m₂ : LoweredExpr)
  /--
  Dart's `identical(m₁, m₂)`: evaluates `m₁` and then `m₂`, and evaluates to whether they're the
  same object: the same location, or the same null object, boolean or integer.
  -/
  | identical (m₁ m₂ : LoweredExpr)
  /--
  A let expression, `let v = m₁ in m₂` (Kernel's `Let`): evaluates `m₁`, allocates a new cell for
  local variable `v` holding its value, and then evaluates `m₂`, in which `v` refers to that cell.
  Its value, and its static type, are `m₂`'s. `v`'s scope is `m₂`: a declaration of a variable
  with the same name in an enclosing scope is shadowed there.

  The CFE lowers several constructs into let expressions, so that a subexpression is evaluated only
  once: for example, a postfix increment `x++` whose value is used is
  `letIn t (var x int) (seq (variableSet x (t + 1)) (var t int))`, and `a?.m()` is
  `letIn t a (cond (identical (var t) null) null (methodCall (var t) "m" …))`. Each time a let
  expression runs, it gets a new cell, so one inside a loop doesn't share its variable between
  iterations. The variable can be assigned in `m₂` if it isn't `final`, as for any local variable.
  -/
  | letIn (v : Variable) (m₁ m₂ : LoweredExpr)
  /--
  A constant, described structurally by `c` (for example, a string literal, or Kernel's
  `ConstantExpression` of a string constant). The null object, booleans and integers evaluate to
  themselves. Any other constant evaluates to its *canonical* object: the first evaluation of a
  constant described by `c` allocates the object, and records it in the state's table of constants
  (`State.constants`); every later evaluation of a constant described by `c`, anywhere in the
  program, evaluates to the same object. So equal constants are identical (`identical`), as Dart
  requires.

  Only what Kernel presents as a constant is canonicalized: the result of concatenating strings
  (`concat`) is a new object, even if its contents equal a constant's. (The language specification
  says that equal "constant strings" are identical without defining the term; see
  dart-lang/language#4843.)
  -/
  | constant (c : ConstValue)
  /--
  A string concatenation (Kernel's `StringConcatenation`, for a string interpolation such as
  `"n = $n"`, and also `a + b` on strings): evaluates `parts`, left to right, converts each value
  to its string form, and evaluates to a new string object holding their concatenation. A string
  is itself, `null` is `"null"`, a boolean is `"true"` or `"false"`, and an integer is its decimal
  form. Any other part gets stuck, since its `toString` would run user code; the translator uses
  `concat` only when every part's static type is `String`, `Null`, `bool` or `int` (or nullable
  versions of them).
  -/
  | concat (parts : List LoweredExpr)
  /--
  An assertion, `assert(c)` (`msg` is `none`) or `assert(c, msg)`, as a statement or as an
  initializer in a constructor's initializer list (Kernel's `AssertStatement` and
  `AssertInitializer`). Whether assertions are checked is a parameter of the semantics
  (`SemanticParams.assertsEnabled`). If they aren't, the assertion completes normally with the
  null object, evaluating neither `c` nor `msg`. If they are, it evaluates `c`, which must be a
  boolean (anything else gets stuck, as in `cond`): if it's `true`, the assertion completes
  normally with the null object; if it's `false`, it evaluates `msg`, if there is one, and throws
  (see `assertFail`).
  -/
  | assert (c : LoweredExpr) (msg : Option LoweredExpr)
  /--
  A block with a value (Kernel's `BlockExpression`): runs `stmts` in order, as a block does, and
  then evaluates `m`, whose value and static type are the block's. A declaration among `stmts`
  scopes over the rest of `stmts` and over `m`. (The CFE lowers a cascade `e..m()..x = 1` to
  `let t = e in { t.m(); t.x = 1; } => t`.)
  -/
  | blockExpr (stmts : List LoweredExpr) (m : LoweredExpr)
  /-
  The remaining constructors are *run-time-only* forms: flow analysis never produces them. They
  appear only as a program runs.
  -/
  /-- An expression that has completed normally, evaluating to `v`. -/
  | val (v : Value)
  /-- An expression that has thrown exception object `v`, propagating outward. -/
  | throwing (v : Value)
  /--
  An expression that has returned `v` (by a return statement), propagating outward to the body of
  the function that is returning (`frame`).
  -/
  | returning (v : Value)
  /--
  An expression that has broken out of labeled statement `l` (by a break statement), propagating
  outward to that labeled statement (`labeled l`).
  -/
  | breaking (l : String)
  /--
  The body `m` of a running call of a function, whose result has static type `T`. It turns a
  return of `v` into completing normally with `v`, and it turns completing normally (falling off
  the end of the body) into completing normally with the null object.
  -/
  | frame (m : LoweredExpr) (T : τ)
  /--
  A reference to local variable or formal parameter `v`, whose static type (after any promotion)
  is `T`, resolved to the heap cell at `ℓ`. Declaring a variable resolves each `var v T` in its
  scope to `varAt v T ℓ`.
  -/
  | varAt (v : Variable) (T : τ) (ℓ : Loc)
  /-- Evaluate `m₁`, discard its value, then evaluate `m₂`. A block runs as a sequence. -/
  | seq (m₁ m₂ : LoweredExpr)
  /--
  An assignment to local variable or formal parameter `v`, resolved to the heap cell at `ℓ`.
  Declaring a variable resolves each `variableSet v m` in its scope to `variableSetAt v ℓ m`.
  -/
  | variableSetAt (v : Variable) (ℓ : Loc) (m : LoweredExpr)
  /--
  The generative constructor whose key is `k`, about to run on the object at `ℓ`, with argument
  values `vs`. Running it binds `this` and the constructor's formal parameters, and runs its
  initializers and then its body, as the body of a running constructor (`ctorFrame`).
  -/
  | ctorRun (ℓ : Loc) (k : String) (vs : List Value)
  /--
  The initializers and body `m` of a running constructor. Like the body of a running call
  (`frame`), it turns a return (`return;`) into completing normally; either way, it completes with
  the null object, since an instance creation's value is the object (see `new`).
  -/
  | ctorFrame (m : LoweredExpr)
  /--
  The promotion check of the result of `m`, the body of a running getter, against `T`, the
  (possibly promoted) static type of the property read that ran the getter: once `m` completes
  normally with `w`, `checkPromotion` does too, if `w` passes the check.
  -/
  | checkPromotion (T : τ) (m : LoweredExpr)
  /--
  A failing assertion, with its message `msg`, if any (see `assert`): evaluates `msg`, discards
  its value, and throws (`DynamicError.assertionFailed`).
  -/
  | assertFail (msg : Option LoweredExpr)

/--
An evaluation context item: an expression with a hole in the position that evaluates next. See
`EctxItem.fill`.
-/
public inductive EctxItem where
  /-- `□!` -/
  | nullCheck
  /-- `□ as T` -/
  | as (T : τ)
  /-- `□ is T` -/
  | is (T : τ)
  /-- `cond(□, m₂, m₃)` (of type `T`) -/
  | cond (m₂ m₃ : LoweredExpr) (T : τ)
  /-- `□.p` (of type `T`) -/
  | propertyGet (p : Property) (T : τ)
  /-- `seq(□, m₂)` -/
  | seq (m₂ : LoweredExpr)
  /-- `v = □`, with `v` resolved to the heap cell at `ℓ` -/
  | variableSetAt (v : Variable) (ℓ : Loc)
  /--
  `f(v₁, …, vₙ, □, m₁, …, mₖ)` (of type `T`): a call whose arguments before the hole have
  evaluated to `vs`, and whose arguments after it, `ms`, are still to be evaluated
  -/
  | call (f : String) (vs : List Value) (ms : List LoweredExpr) (T : τ)
  /-- `return □;` -/
  | ret
  /-- `check(kind, □)` -/
  | check (kind : CheckKind)
  /-- `checkEq(□, m₂)` -/
  | checkEqL (m₂ : LoweredExpr)
  /-- `checkEq(v₁, □)`, where the first operand has evaluated to `v₁` -/
  | checkEqR (v₁ : Value)
  /-- `l: □`: the body of a labeled statement -/
  | labeled (l : String)
  /-- `□ op m₂`, computed in mode `mode` -/
  | intBinL (op : IntBinOp) (mode : Option IntMode) (m₂ : LoweredExpr)
  /-- `v₁ op □`, computed in mode `mode`, where the first operand has evaluated to `v₁` -/
  | intBinR (op : IntBinOp) (mode : Option IntMode) (v₁ : Value)
  /-- `-□`, computed in mode `mode` -/
  | intNeg (mode : Option IntMode)
  /-- `□ == m₂` -/
  | primEqL (m₂ : LoweredExpr)
  /-- `v₁ == □`, where the first operand has evaluated to `v₁` -/
  | primEqR (v₁ : Value)
  /-- `frame(□)` (of type `T`): the body of a running call -/
  | frame (T : τ)
  /--
  `C(v₁, …, vₙ, □, m₁, …, mₖ)` (of type `T`): an instance creation by constructor `k`, whose
  arguments before the hole have evaluated to `vs`, and whose arguments after it, `ms`, are still to
  be evaluated
  -/
  | new (k : String) (vs : List Value) (ms : List LoweredExpr) (T : τ)
  /-- `initCtor(□, k, args)`: the receiver of a `super(args)` or `this(args)` call -/
  | initCtorRecv (k : String) (args : List LoweredExpr)
  /--
  `initCtor(v, k, (v₁, …, vₙ, □, m₁, …, mₖ))`: an argument of a `super(args)` or `this(args)`
  call, whose receiver has evaluated to `v`
  -/
  | initCtorArgs (v : Value) (k : String) (vs : List Value) (ms : List LoweredExpr)
  /-- `initField(□, name, m₂)` -/
  | initFieldL (name : String) (m₂ : LoweredExpr)
  /-- `initField(v₁, name, □)`, where the receiver has evaluated to `v₁` -/
  | initFieldR (v₁ : Value) (name : String)
  /-- `□.name = m₂` -/
  | propertySetL (name : String) (m₂ : LoweredExpr)
  /-- `v₁.name = □`, where the receiver has evaluated to `v₁` -/
  | propertySetR (v₁ : Value) (name : String)
  /-- `ctorFrame(□)`: the initializers and body of a running constructor -/
  | ctorFrame
  /-- `□.name(args)` (of type `T`) -/
  | methodCallRecv (name : String) (args : List LoweredExpr) (T : τ)
  /--
  `v.name(v₁, …, vₙ, □, m₁, …, mₖ)` (of type `T`): an argument of a method call, whose receiver has
  evaluated to `v`
  -/
  | methodCallArgs (v : Value) (name : String) (vs : List Value) (ms : List LoweredExpr) (T : τ)
  /-- `superCall(□, name, slot, args)` (of type `T`): the receiver of a super method call -/
  | superCallRecv (name : String) (slot : Option String) (args : List LoweredExpr) (T : τ)
  /--
  `superCall(v, name, slot, (v₁, …, vₙ, □, m₁, …, mₖ))` (of type `T`): an argument of a super
  method call, whose receiver has evaluated to `v`
  -/
  | superCallArgs (v : Value) (name : String) (slot : Option String) (vs : List Value)
      (ms : List LoweredExpr) (T : τ)
  /-- `superGet(□, name, slot)` (of type `T`) -/
  | superGet (name : String) (slot : Option String) (T : τ)
  /-- `superSet(□, name, slot, m₂)` -/
  | superSetL (name : String) (slot : Option String) (m₂ : LoweredExpr)
  /-- `superSet(v₁, name, slot, □)`, where the receiver has evaluated to `v₁` -/
  | superSetR (v₁ : Value) (name : String) (slot : Option String)
  /-- `checkPromotion(T, □)`: the body of a running getter -/
  | checkPromotion (T : τ)
  /-- `identical(□, m₂)` -/
  | identicalL (m₂ : LoweredExpr)
  /-- `identical(v₁, □)`, where the first operand has evaluated to `v₁` -/
  | identicalR (v₁ : Value)
  /-- `let v = □ in m₂` -/
  | letIn (v : Variable) (m₂ : LoweredExpr)
  /--
  `concat(v₁, …, vₙ, □, m₁, …, mₖ)`: a part of a string concatenation, whose parts before the hole
  have evaluated to `vs`, and whose parts after it, `ms`, are still to be evaluated
  -/
  | concat (vs : List Value) (ms : List LoweredExpr)
  /-- `assertFail(□)`: the message of a failing assertion -/
  | assertFail

end

deriving instance Repr for Value, LoweredExpr, EctxItem
deriving instance BEq for Value, LoweredExpr, EctxItem

local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)

/--
A static type for a value, for `LoweredExpr.typeOf`: the most precise type that doesn't depend
on the heap. (An object's class is in the heap, so an object reference just gets `Object`.)
-/
@[expose]
public def Value.typeOf : Value → τ
  | .null => Γ.Null
  | .bool _ => Γ.bool
  | .int _ => Γ.int
  | .obj _ => Γ.Object
  | .error _ => Γ.Object
  | .cont _ => Γ.ObjectQ

omit Γ in
/-- Whether the intrinsic check of kind `kind` holds of value `v`. -/
@[expose]
public def CheckKind.holds : CheckKind → Value → Bool
  | .isTrue, .bool true => true
  | .isFalse, .bool false => true
  | .isNull, .null => true
  | .isNotNull, .null => false
  | .isNotNull, _ => true
  | _, _ => false

omit Γ in
/--
Whether two values are equal, for the intrinsic check `LoweredExpr.checkEq` and for equality
`LoweredExpr.primEq`, if they can be
compared: two values that are each the null object, a boolean or an integer are equal if they're
the same value. Any other value can't be compared (`none`): `==` on objects runs user code (a call
of the method named `==`; see `LoweredExpr.methodCall`).
-/
@[expose]
public def Value.primEq? : Value → Value → Option Bool
  | .null, .null => some true
  | .bool b₁, .bool b₂ => some (b₁ == b₂)
  | .int n₁, .int n₂ => some (n₁ == n₂)
  | .null, .bool _ | .null, .int _ | .bool _, .null | .bool _, .int _ | .int _, .null
  | .int _, .bool _ => some false
  | _, _ => none

omit Γ in
/--
Whether two values are the same object, for `LoweredExpr.identical`: references to objects in the
heap are the same if they refer to the same location, and are never the same as the null object, a
boolean or an integer, which are compared as by `primEq?`. Exception objects and captured
continuations can't be compared (`none`).
-/
@[expose]
public def Value.identical? : Value → Value → Option Bool
  | .obj ℓ₁, .obj ℓ₂ => some (ℓ₁ == ℓ₂)
  | .obj _, .null | .obj _, .bool _ | .obj _, .int _ | .null, .obj _ | .bool _, .obj _
  | .int _, .obj _ => some false
  | v₁, v₂ => Value.primEq? v₁ v₂

omit Γ in
/--
The result of binary operator `op` on integers `n₁` and `n₂`, with arithmetic in integer mode
`mode` (see `IntMode.arith`): `none` if the operation gets stuck. A comparison doesn't depend on
the mode.
-/
@[expose]
public def IntBinOp.eval : IntBinOp → IntMode → Int → Int → Option Value
  | .add, mode, n₁, n₂ => (mode.arith (n₁ + n₂)).map .int
  | .sub, mode, n₁, n₂ => (mode.arith (n₁ - n₂)).map .int
  | .mul, mode, n₁, n₂ => (mode.arith (n₁ * n₂)).map .int
  | .lt, _, n₁, n₂ => some (.bool (decide (n₁ < n₂)))
  | .le, _, n₁, n₂ => some (.bool (decide (n₁ ≤ n₂)))
  | .gt, _, n₁, n₂ => some (.bool (decide (n₁ > n₂)))
  | .ge, _, n₁, n₂ => some (.bool (decide (n₁ ≥ n₂)))

omit Γ in
/--
In mode `checked`, an arithmetic operator `op` gives its exact result `n` (the result in mode
`unbounded`; `hn`), if `n` is in 64-bit range (`hr`): `op.eval .checked n₁ n₂ = some (.int n)`.
-/
public theorem IntBinOp.eval_checked_of_range {op : IntBinOp} {n₁ n₂ n : Int}
    (hn : op.eval (τ := τ) .unbounded n₁ n₂ = some (.int n)) (hr : -2 ^ 63 ≤ n ∧ n < 2 ^ 63) :
    op.eval (τ := τ) .checked n₁ n₂ = some (.int n) := by
  cases op <;> simp only [IntBinOp.eval, IntMode.arith, Option.map_some] at hn ⊢ <;> simp_all

/-- The static type of a constant described by `c`: its dynamic type. -/
@[expose]
public def ConstValue.typeOf : ConstValue → τ
  | .null => Γ.Null
  | .bool _ => Γ.bool
  | .int _ => Γ.int
  | .string _ => Γ.String

omit Γ in
/--
The value of a constant described by `c`, if it's a value that isn't in the heap (the null
object, a boolean or an integer): `none` if the constant's value is an object in the heap, which
is canonicalized (see `LoweredExpr.constant`).
-/
@[expose]
public def ConstValue.prim? : ConstValue → Option Value
  | .null => some .null
  | .bool b => some (.bool b)
  | .int n => some (.int n)
  | .string _ => none

/--
The static type of an expression.

For the run-time-only forms, which flow analysis never sees, the types are chosen only to make
this function total, and no proof relies on them. In particular, `throwing`, `returning` and `ret`
would best be typed `Never`, which `DartTypeRepr` doesn't have; they get the top type `Object?`
instead.
-/
@[expose]
public def LoweredExpr.typeOf :
    LoweredExpr → τ
  | var _ T => T
  | nullCheck m => NonNull m.typeOf
  | as _ T => T
  | is _ _ => Γ.bool
  | null => Γ.Null
  | bool _ => Γ.bool
  | int _ => Γ.int
  | declare _ _ _ => Γ.Null
  | cond _ _ _ T => T
  | block _ => Γ.Null
  | propertyGet _ _ T => T
  | variableSet _ m => m.typeOf
  | unsupported _ T => T
  | call _ _ T => T
  | ret _ => Γ.ObjectQ
  | check _ _ => Γ.Null
  | checkEq _ _ => Γ.Null
  | loop _ => Γ.Null
  | labeled _ _ => Γ.Null
  | brk _ => Γ.Null
  | intBin op _ _ _ => if op.isComparison then Γ.bool else Γ.int
  | intNeg _ _ => Γ.int
  | primEq _ _ => Γ.bool
  | new _ _ T => T
  | initCtor _ _ _ => Γ.Null
  | initField _ _ _ => Γ.Null
  | propertySet _ _ m₂ => m₂.typeOf
  | methodCall _ _ _ T => T
  | superCall _ _ _ _ T => T
  | superGet _ _ _ T => T
  | superSet _ _ _ m₂ => m₂.typeOf
  | identical _ _ => Γ.bool
  | letIn _ _ m₂ => m₂.typeOf
  | constant c => c.typeOf
  | concat _ => Γ.String
  | assert _ _ => Γ.Null
  | blockExpr _ m => m.typeOf
  | val v => v.typeOf
  | throwing _ => Γ.ObjectQ
  | returning _ => Γ.ObjectQ
  | breaking _ => Γ.Null
  | frame _ T => T
  | varAt _ T _ => T
  | seq _ m₂ => m₂.typeOf
  | variableSetAt _ _ m => m.typeOf
  | ctorRun _ _ _ => Γ.Null
  | ctorFrame _ => Γ.Null
  | checkPromotion T _ => T
  | assertFail _ => Γ.Null

mutual

/--
Set the integer mode of every integer operator in `m` (`intBin` and `intNeg`) to `mode`. Calling a
function runs its body with every operator's mode set to the function's mode, since the function
an operator is in can't be seen from the operator (see `LoweredExpr.intBin`).

A call in `m` (of a function, or of a constructor) is left alone, apart from its arguments: the
callee's body is in the program's tables, and gets its own mode when it's called. Values (in
`val`, `throwing` and `returning`) are left alone too.
-/
@[expose]
public def LoweredExpr.withIntMode (mode : IntMode) : LoweredExpr → LoweredExpr
  | .var v T => .var v T
  | .nullCheck m => .nullCheck (m.withIntMode mode)
  | .as m T => .as (m.withIntMode mode) T
  | .is m T => .is (m.withIntMode mode) T
  | .null => .null
  | .bool b => .bool b
  | .int n => .int n
  | .declare v T startsNull => .declare v T startsNull
  | .cond m₁ m₂ m₃ T => .cond (m₁.withIntMode mode) (m₂.withIntMode mode) (m₃.withIntMode mode) T
  | .block ms => .block (LoweredExpr.withIntModeList mode ms)
  | .propertyGet m p T => .propertyGet (m.withIntMode mode) p T
  | .variableSet v m => .variableSet v (m.withIntMode mode)
  | .unsupported kind T => .unsupported kind T
  | .call f args T => .call f (LoweredExpr.withIntModeList mode args) T
  | .ret m => .ret (m.withIntMode mode)
  | .check kind m => .check kind (m.withIntMode mode)
  | .checkEq m₁ m₂ => .checkEq (m₁.withIntMode mode) (m₂.withIntMode mode)
  | .loop m => .loop (m.withIntMode mode)
  | .labeled l m => .labeled l (m.withIntMode mode)
  | .brk l => .brk l
  | .intBin op _ m₁ m₂ => .intBin op (some mode) (m₁.withIntMode mode) (m₂.withIntMode mode)
  | .intNeg _ m => .intNeg (some mode) (m.withIntMode mode)
  | .primEq m₁ m₂ => .primEq (m₁.withIntMode mode) (m₂.withIntMode mode)
  | .new k args T => .new k (LoweredExpr.withIntModeList mode args) T
  | .initCtor m k args => .initCtor (m.withIntMode mode) k (LoweredExpr.withIntModeList mode args)
  | .initField m name m₂ => .initField (m.withIntMode mode) name (m₂.withIntMode mode)
  | .propertySet m name m₂ => .propertySet (m.withIntMode mode) name (m₂.withIntMode mode)
  | .methodCall m name args T =>
    .methodCall (m.withIntMode mode) name (LoweredExpr.withIntModeList mode args) T
  | .superCall m name slot args T =>
    .superCall (m.withIntMode mode) name slot (LoweredExpr.withIntModeList mode args) T
  | .superGet m name slot T => .superGet (m.withIntMode mode) name slot T
  | .superSet m name slot m₂ => .superSet (m.withIntMode mode) name slot (m₂.withIntMode mode)
  | .identical m₁ m₂ => .identical (m₁.withIntMode mode) (m₂.withIntMode mode)
  | .letIn v m₁ m₂ => .letIn v (m₁.withIntMode mode) (m₂.withIntMode mode)
  | .constant c => .constant c
  | .concat parts => .concat (LoweredExpr.withIntModeList mode parts)
  | .assert c msg =>
    .assert (c.withIntMode mode)
      (match msg with | none => none | some m => some (m.withIntMode mode))
  | .blockExpr stmts m => .blockExpr (LoweredExpr.withIntModeList mode stmts) (m.withIntMode mode)
  | .val v => .val v
  | .throwing v => .throwing v
  | .returning v => .returning v
  | .breaking l => .breaking l
  | .frame m T => .frame (m.withIntMode mode) T
  | .varAt v T ℓ => .varAt v T ℓ
  | .seq m₁ m₂ => .seq (m₁.withIntMode mode) (m₂.withIntMode mode)
  | .variableSetAt v ℓ m => .variableSetAt v ℓ (m.withIntMode mode)
  | .ctorRun ℓ k vs => .ctorRun ℓ k vs
  | .ctorFrame m => .ctorFrame (m.withIntMode mode)
  | .checkPromotion T m => .checkPromotion T (m.withIntMode mode)
  | .assertFail msg =>
    .assertFail (match msg with | none => none | some m => some (m.withIntMode mode))

/-- Set the integer mode of every integer operator in each of `ms`, as `withIntMode` does. -/
@[expose]
public def LoweredExpr.withIntModeList (mode : IntMode) :
    List LoweredExpr → List LoweredExpr
  | [] => []
  | m :: ms => m.withIntMode mode :: withIntModeList mode ms

end

mutual

/--
Fill every `super` slot in `m` (of `superCall`, `superGet` and `superSet`) with `s`. Running a
member's body fills them with the superclass of the class that provides the member, since that
class can't be seen from the `super` access (see `LoweredExpr.superCall`). Calls and values are
treated as by `withIntMode`.
-/
@[expose]
public def LoweredExpr.withSuperclass (s : Option String) : LoweredExpr → LoweredExpr
  | .var v T => .var v T
  | .nullCheck m => .nullCheck (m.withSuperclass s)
  | .as m T => .as (m.withSuperclass s) T
  | .is m T => .is (m.withSuperclass s) T
  | .null => .null
  | .bool b => .bool b
  | .int n => .int n
  | .declare v T startsNull => .declare v T startsNull
  | .cond m₁ m₂ m₃ T => .cond (m₁.withSuperclass s) (m₂.withSuperclass s) (m₃.withSuperclass s) T
  | .block ms => .block (LoweredExpr.withSuperclassList s ms)
  | .propertyGet m p T => .propertyGet (m.withSuperclass s) p T
  | .variableSet v m => .variableSet v (m.withSuperclass s)
  | .unsupported kind T => .unsupported kind T
  | .call f args T => .call f (LoweredExpr.withSuperclassList s args) T
  | .ret m => .ret (m.withSuperclass s)
  | .check kind m => .check kind (m.withSuperclass s)
  | .checkEq m₁ m₂ => .checkEq (m₁.withSuperclass s) (m₂.withSuperclass s)
  | .loop m => .loop (m.withSuperclass s)
  | .labeled l m => .labeled l (m.withSuperclass s)
  | .brk l => .brk l
  | .intBin op mode m₁ m₂ => .intBin op mode (m₁.withSuperclass s) (m₂.withSuperclass s)
  | .intNeg mode m => .intNeg mode (m.withSuperclass s)
  | .primEq m₁ m₂ => .primEq (m₁.withSuperclass s) (m₂.withSuperclass s)
  | .new k args T => .new k (LoweredExpr.withSuperclassList s args) T
  | .initCtor m k args => .initCtor (m.withSuperclass s) k (LoweredExpr.withSuperclassList s args)
  | .initField m name m₂ => .initField (m.withSuperclass s) name (m₂.withSuperclass s)
  | .propertySet m name m₂ => .propertySet (m.withSuperclass s) name (m₂.withSuperclass s)
  | .methodCall m name args T =>
    .methodCall (m.withSuperclass s) name (LoweredExpr.withSuperclassList s args) T
  | .superCall m name _ args T =>
    .superCall (m.withSuperclass s) name s (LoweredExpr.withSuperclassList s args) T
  | .superGet m name _ T => .superGet (m.withSuperclass s) name s T
  | .superSet m name _ m₂ => .superSet (m.withSuperclass s) name s (m₂.withSuperclass s)
  | .identical m₁ m₂ => .identical (m₁.withSuperclass s) (m₂.withSuperclass s)
  | .letIn v m₁ m₂ => .letIn v (m₁.withSuperclass s) (m₂.withSuperclass s)
  | .constant c => .constant c
  | .concat parts => .concat (LoweredExpr.withSuperclassList s parts)
  | .assert c msg =>
    .assert (c.withSuperclass s)
      (match msg with | none => none | some m => some (m.withSuperclass s))
  | .blockExpr stmts m =>
    .blockExpr (LoweredExpr.withSuperclassList s stmts) (m.withSuperclass s)
  | .val v => .val v
  | .throwing v => .throwing v
  | .returning v => .returning v
  | .breaking l => .breaking l
  | .frame m T => .frame (m.withSuperclass s) T
  | .varAt v T ℓ => .varAt v T ℓ
  | .seq m₁ m₂ => .seq (m₁.withSuperclass s) (m₂.withSuperclass s)
  | .variableSetAt v ℓ m => .variableSetAt v ℓ (m.withSuperclass s)
  | .ctorRun ℓ k vs => .ctorRun ℓ k vs
  | .ctorFrame m => .ctorFrame (m.withSuperclass s)
  | .checkPromotion T m => .checkPromotion T (m.withSuperclass s)
  | .assertFail msg =>
    .assertFail (match msg with | none => none | some m => some (m.withSuperclass s))

/-- Fill every `super` slot in each of `ms` with `s`, as `withSuperclass` does. -/
@[expose]
public def LoweredExpr.withSuperclassList (s : Option String) :
    List LoweredExpr → List LoweredExpr
  | [] => []
  | m :: ms => m.withSuperclass s :: withSuperclassList s ms

end

/--
The declaration of a top-level function: its formal parameters `params`, in order, and its body
`body`. The program's function table (`SemanticParams.functions`) maps each function's key (see
`LoweredExpr.call`) to its declaration.
-/
public structure FunctionDecl where
  /-- The function's formal parameters, in order. -/
  params : List Variable
  /-- The function's body, in which the formal parameters are free variables. -/
  body : LoweredExpr

/--
What a class's instances have under a member name (see `ClassDecl.dispatch`): either the implicit
getter or setter of an instance variable, or a method, getter or setter that is user code.
-/
public inductive Member where
  /--
  The implicit getter (under the instance variable's name `x`) or setter (under `x=`) of the
  instance variable whose key is `iv` (see `ClassDecl.instanceVariables`): the object's cell for
  that key holds the instance variable's value.

  An instance variable that shadows one with the same name in a superclass is a different instance
  variable, with its own key, so its instances have two cells. The subclass's dispatch table sends
  `x` to the subclass's instance variable; `super.x` in the subclass looks `x` up in the
  superclass's dispatch table, which sends it to the superclass's instance variable, and so to the
  other cell.
  -/
  | field (iv : String)
  /--
  The method, getter or setter whose declaration is `SemanticParams.members key`, provided by the
  declaration of the class whose key is `holder` (the class itself, or a superclass). A `super`
  access in its body is resolved in `holder`'s superclass (see `LoweredExpr.superCall`).
  -/
  | proc (key holder : String)
  deriving Repr, BEq, DecidableEq

/--
The declaration of a (non-generic) class, as the semantics needs it. The program's class table
(`SemanticParams.classes`) maps each class's key to its declaration. Like a function's key, a
class's key identifies it uniquely in the program.
-/
public structure ClassDecl where
  /-- The class's instance type: the dynamic type of its instances. -/
  type : τ
  /--
  The keys of all the instance variables of the class's instances, including the ones declared in
  its superclasses. Each instance has one cell per instance variable, found by its key (see
  `Cell.object`), so the keys must be unique for each instance, even when instance variables have
  the same name (a private name in different libraries, or an instance variable shadowing one in a
  superclass). For example, a translator can key each instance variable by the class in the
  superclass chain that holds its storage, as `"<library URI>::C::x"` (for an instance variable
  declared in a mixin, the class that holds its storage is the mixin application). The dispatch
  table maps each implicit getter and setter to its instance variable's key (see `Member.field`).
  -/
  instanceVariables : List String
  /--
  The *dispatch table*: for each member name, what the class's instances have under that name
  (`none` if nothing). Getters and methods are named by their names, and setters by their names
  followed by `=` (so a property `x` can have both a getter `"x"` and a setter `"x="`). The table is
  flattened: it includes the members inherited from superclasses, and accounts for overriding, as
  a class hierarchy computes it.
  -/
  dispatch : String → Option Member
  /-- The key of the class's superclass, if it has one (every class but `Object` does). -/
  superclass : Option String

/--
The declaration of a method, getter or setter (in the program's member table,
`SemanticParams.members`): a variable `this`, bound to the receiver when the body runs, its formal
parameters `params` (none for a getter, one for a setter), and its body.
-/
public structure MemberDecl where
  /-- The variable that refers to the receiver (`this`) in the body. -/
  this : Variable
  /-- The member's formal parameters, in order. -/
  params : List Variable
  /--
  The member's body, in which `this` and the formal parameters are free variables. A getter's
  result is what its body returns (`ret`), and a setter's body's result is discarded.
  -/
  body : LoweredExpr

/--
The declaration of a generative constructor (in the program's constructor table,
`SemanticParams.constructors`).
-/
public structure ConstructorDecl where
  /-- The key of the constructor's class. -/
  cls : String
  /-- The variable that refers to the object being constructed (`this`). -/
  this : Variable
  /-- The constructor's formal parameters, in order. -/
  params : List Variable
  /--
  The constructor's initializers, in the order Dart runs them: the initializers of the class's
  instance variables (from their declarations), then the constructor's initializer list
  (`initField`), then the superclass constructor call, or the redirecting constructor call
  (`initCtor`). A redirecting constructor has only the redirecting call. `this` and the formal
  parameters are free variables in them.

  An instance variable that nothing initializes stays uninitialized, and reading it gets stuck.
  So the initializers of a non-redirecting constructor must initialize each instance variable
  declared in its class, even a nullable one that Dart implicitly initializes to `null`. Kernel
  already provides these: the front end gives each non-`late` instance variable an initializer in
  every non-redirecting constructor, adding an explicit `= null` where Dart's initialization to
  `null` is implicit.
  -/
  initializers : List LoweredExpr
  /-- The constructor's body, in which `this` and the formal parameters are free variables. -/
  body : LoweredExpr

local notation "EctxItem" => EctxItem (τ := τ)

/--
How an expression's evaluation (or a statement's execution) *completes*, in the sense of the
language specification's "Statement Completion" section: normally, evaluating to an object, by
throwing an exception object, by returning an object, or by breaking out of a labeled statement.
Stack traces aren't modeled.

The specification has one more kind of completion: continuing (with or without a label). A
`continue` in a loop is expressed as a break out of a labeled statement around the loop's body
(see `LoweredExpr.loop`), so it needs no completion of its own; continuing to a `switch` case isn't
modeled yet.
-/
public inductive Outcome where
  /-- Completes normally, evaluating to `v`. -/
  | normal (v : Value)
  /-- Throws exception object `v`. -/
  | throwing (v : Value)
  /-- Returns `v` (by a return statement), from the function whose body is running. -/
  | returning (v : Value)
  /-- Breaks out of the labeled statement `l` (by a break statement). -/
  | breaking (l : String)
  deriving Repr, BEq

local notation "Outcome" => Outcome (τ := τ)

/-- The expression that has completed with outcome `o`. -/
@[expose]
public def Outcome.toExpr : Outcome → LoweredExpr
  | .normal v => .val v
  | .throwing v => .throwing v
  | .returning v => .returning v
  | .breaking l => .breaking l

/-- How `m` completed, if it has. -/
@[expose]
public def LoweredExpr.toOutcome? : LoweredExpr → Option Outcome
  | .val v => some (.normal v)
  | .throwing v => some (.throwing v)
  | .returning v => some (.returning v)
  | .breaking l => some (.breaking l)
  | _ => none

omit Γ in
/-- Converting an outcome `o` to an expression and back gives `o`. -/
public theorem Outcome.toOutcome?_toExpr (o : Outcome) : o.toExpr.toOutcome? = some o := by
  cases o <;> rfl

omit Γ in
/-- An expression `m` that has completed with outcome `o` (`h`) is that outcome as an expression. -/
public theorem LoweredExpr.toExpr_of_toOutcome? {m : LoweredExpr} {o : Outcome}
    (h : m.toOutcome? = some o) : o.toExpr = m := by
  cases m <;> simp only [toOutcome?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

/-- Plug `m` into the hole of context item `Ki`. -/
@[expose]
public def EctxItem.fill : EctxItem → LoweredExpr → LoweredExpr
  | .nullCheck, m => .nullCheck m
  | .as T, m => .as m T
  | .is T, m => .is m T
  | .cond m₂ m₃ T, m => .cond m m₂ m₃ T
  | .propertyGet p T, m => .propertyGet m p T
  | .seq m₂, m => .seq m m₂
  | .variableSetAt v ℓ, m => .variableSetAt v ℓ m
  | .call f vs ms T, m => .call f (vs.map .val ++ m :: ms) T
  | .ret, m => .ret m
  | .check kind, m => .check kind m
  | .checkEqL m₂, m => .checkEq m m₂
  | .checkEqR v₁, m => .checkEq (.val v₁) m
  | .labeled l, m => .labeled l m
  | .intBinL op mode m₂, m => .intBin op mode m m₂
  | .intBinR op mode v₁, m => .intBin op mode (.val v₁) m
  | .intNeg mode, m => .intNeg mode m
  | .primEqL m₂, m => .primEq m m₂
  | .primEqR v₁, m => .primEq (.val v₁) m
  | .frame T, m => .frame m T
  | .new k vs ms T, m => .new k (vs.map .val ++ m :: ms) T
  | .initCtorRecv k args, m => .initCtor m k args
  | .initCtorArgs v k vs ms, m => .initCtor (.val v) k (vs.map .val ++ m :: ms)
  | .initFieldL name m₂, m => .initField m name m₂
  | .initFieldR v₁ name, m => .initField (.val v₁) name m
  | .propertySetL name m₂, m => .propertySet m name m₂
  | .propertySetR v₁ name, m => .propertySet (.val v₁) name m
  | .ctorFrame, m => .ctorFrame m
  | .methodCallRecv name args T, m => .methodCall m name args T
  | .methodCallArgs v name vs ms T, m => .methodCall (.val v) name (vs.map .val ++ m :: ms) T
  | .superCallRecv name slot args T, m => .superCall m name slot args T
  | .superCallArgs v name slot vs ms T, m =>
    .superCall (.val v) name slot (vs.map .val ++ m :: ms) T
  | .superGet name slot T, m => .superGet m name slot T
  | .superSetL name slot m₂, m => .superSet m name slot m₂
  | .superSetR v₁ name slot, m => .superSet (.val v₁) name slot m
  | .checkPromotion T, m => .checkPromotion T m
  | .identicalL m₂, m => .identical m m₂
  | .identicalR v₁, m => .identical (.val v₁) m
  | .letIn v m₂, m => .letIn v m m₂
  | .concat vs ms, m => .concat (vs.map .val ++ m :: ms)
  | .assertFail, m => .assertFail (some m)

/--
Whether context item `Ki` handles a return (`returning`) in its hole, rather than propagating it
outward: only the body of a running call (`frame`) or constructor (`ctorFrame`) does.
-/
@[expose]
public def EctxItem.handlesReturn : EctxItem → Bool
  | .frame _ => true
  | .ctorFrame => true
  | _ => false

omit Γ in
/--
Whether context item `Ki` handles a break out of labeled statement `l` (`breaking l`) in its hole,
rather than propagating it outward: only the body of the labeled statement `l` (`labeled l`) does.
-/
@[expose]
public def EctxItem.handlesBreak (l : String) : EctxItem → Bool
  | .labeled l' => l' == l
  | _ => false

omit Γ in
/-- An expression with a hole plugged (`Ki.fill m`) hasn't completed (`toOutcome? = none`). -/
public theorem EctxItem.toOutcome?_fill (Ki : EctxItem) (m : LoweredExpr) :
    (Ki.fill m).toOutcome? = none := by
  cases Ki <;> rfl

/--
Split a list of expressions (such as a call's arguments) into the values that it starts with, and
the rest, which starts with the first expression that isn't a value (if any).
-/
@[expose]
public def LoweredExpr.splitVals : List LoweredExpr → List Value × List LoweredExpr
  | .val v :: ms => let r := splitVals ms; (v :: r.1, r.2)
  | ms => ([], ms)

omit Γ in
/--
Splitting a list of expressions `ms` into its leading values and the rest loses nothing: the
values, as expressions, followed by the rest, are `ms`
(`(splitVals ms).1.map .val ++ (splitVals ms).2 = ms`).
-/
public theorem LoweredExpr.splitVals_append (ms : List LoweredExpr) :
    (splitVals ms).1.map .val ++ (splitVals ms).2 = ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    cases m <;> simp only [splitVals, List.map_nil, List.nil_append, List.map_cons,
      List.cons_append, ih]

omit Γ in
/--
The values `vs` followed by expressions `ms` that don't start with a value (`h`) split into `vs`
and `ms` (`splitVals (vs.map .val ++ ms) = (vs, ms)`).
-/
public theorem LoweredExpr.splitVals_map_val_append (vs : List Value) {ms : List LoweredExpr}
    (h : ∀ v ms', ms ≠ .val v :: ms') : splitVals (vs.map .val ++ ms) = (vs, ms) := by
  induction vs with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    cases ms with
    | nil => rfl
    | cons m ms =>
      cases m
      case val v => exact absurd rfl (h v ms)
      all_goals rfl
  | cons v vs ih => simp [splitVals, ih]

omit Γ in
/--
A list of values followed by an expression `m` (`vs.map .val ++ m :: ms`) is never a list of values
(`ws.map .val`) unless `m` is itself a value (`∃ v, m = .val v`).
-/
public theorem LoweredExpr.eq_val_of_map_val_append {vs ws : List Value} {m : LoweredExpr}
    {ms : List LoweredExpr} (h : vs.map .val ++ m :: ms = ws.map .val) : ∃ v, m = .val v := by
  have hm : m ∈ ws.map LoweredExpr.val := h ▸ List.mem_append_right _ List.mem_cons_self
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hm
  exact ⟨v, rfl⟩

omit Γ in
/--
A list of expressions splits in at most one way into values followed by an expression that isn't
a value, followed by the rest: if `vs₁.map .val ++ m₁ :: ms₁ = vs₂.map .val ++ m₂ :: ms₂` (`h`),
where neither `m₁` (`h₁`) nor `m₂` (`h₂`) is a value, then the two splits are the same
(`vs₁ = vs₂`, `m₁ = m₂` and `ms₁ = ms₂`).
-/
public theorem LoweredExpr.map_val_append_inj {vs₁ vs₂ : List Value} {m₁ m₂ : LoweredExpr}
    {ms₁ ms₂ : List LoweredExpr} (h₁ : ∀ v, m₁ ≠ .val v) (h₂ : ∀ v, m₂ ≠ .val v)
    (h : vs₁.map .val ++ m₁ :: ms₁ = vs₂.map .val ++ m₂ :: ms₂) :
    vs₁ = vs₂ ∧ m₁ = m₂ ∧ ms₁ = ms₂ := by
  induction vs₁ generalizing vs₂ with
  | nil =>
    cases vs₂ with
    | nil => simpa using h
    | cons v vs₂ =>
      simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append,
        List.cons.injEq] at h
      exact absurd h.1 (h₁ v)
  | cons v vs₁ ih =>
    cases vs₂ with
    | nil =>
      simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append,
        List.cons.injEq] at h
      exact absurd h.1.symm (h₂ v)
    | cons w vs₂ =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, LoweredExpr.val.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl, rfl⟩

omit Γ in
/-- Two lists of values are the same as expressions exactly when they're the same lists. -/
@[simp]
public theorem LoweredExpr.map_val_inj {vs₁ vs₂ : List Value} :
    vs₁.map LoweredExpr.val = vs₂.map .val ↔ vs₁ = vs₂ :=
  List.map_inj_right fun _ _ h => LoweredExpr.val.inj h

omit Γ in
/--
The `simp` form of `map_val_append_inj`: if neither `m₁` (`h₁`) nor `m₂` (`h₂`) is a value, then
`vs₁.map .val ++ m₁ :: ms₁ = vs₂.map .val ++ m₂ :: ms₂` exactly when `vs₁ = vs₂`, `m₁ = m₂` and
`ms₁ = ms₂`.
-/
@[simp]
public theorem LoweredExpr.map_val_append_cons_inj {vs₁ vs₂ : List Value} {m₁ m₂ : LoweredExpr}
    {ms₁ ms₂ : List LoweredExpr} (h₁ : ∀ v, m₁ ≠ .val v) (h₂ : ∀ v, m₂ ≠ .val v) :
    vs₁.map .val ++ m₁ :: ms₁ = vs₂.map .val ++ m₂ :: ms₂ ↔ vs₁ = vs₂ ∧ m₁ = m₂ ∧ ms₁ = ms₂ := by
  constructor
  · exact map_val_append_inj h₁ h₂
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

omit Γ in
/--
A list of values (`ws.map .val`) is never values followed by an expression `m` that isn't a value
(`h`), then the rest (`vs.map .val ++ m :: ms`).
-/
@[simp]
public theorem LoweredExpr.map_val_append_cons_ne {vs ws : List Value} {m : LoweredExpr}
    {ms : List LoweredExpr} (h : ∀ v, m ≠ .val v) :
    (vs.map .val ++ m :: ms = ws.map .val) = False := by
  refine eq_false fun he => ?_
  obtain ⟨v, rfl⟩ := eq_val_of_map_val_append he
  exact h v rfl

omit Γ in
/-- The symmetric form of `map_val_append_cons_ne`. -/
@[simp]
public theorem LoweredExpr.map_val_ne_append_cons {vs ws : List Value} {m : LoweredExpr}
    {ms : List LoweredExpr} (h : ∀ v, m ≠ .val v) :
    (ws.map .val = vs.map .val ++ m :: ms) = False := by
  refine eq_false fun he => ?_
  obtain ⟨v, rfl⟩ := eq_val_of_map_val_append he.symm
  exact h v rfl

omit Γ in
/-- A list of values splits into itself and nothing else (`splitVals (vs.map .val) = (vs, [])`). -/
@[simp]
public theorem LoweredExpr.splitVals_map_val (vs : List Value) :
    splitVals (vs.map .val) = (vs, []) := by
  simpa using splitVals_map_val_append vs (ms := []) (by simp)

omit Γ in
/--
An expression splits into an evaluation context item and an expression in its hole that isn't a
value in at most one way: if `Ki₁.fill e₁ = Ki₂.fill e₂` (`h`), where neither `e₁` (`h₁`) nor `e₂`
(`h₂`) is a value, then `Ki₁ = Ki₂` and `e₁ = e₂`. (The only items for which this isn't immediate
are those of calls and instance creations, whose hole can be at any argument after the ones that
are values.)
-/
public theorem EctxItem.fill_inj {Ki₁ Ki₂ : EctxItem} {e₁ e₂ : LoweredExpr}
    (h₁ : ∀ v, e₁ ≠ .val v) (h₂ : ∀ v, e₂ ≠ .val v) (h : Ki₁.fill e₁ = Ki₂.fill e₂) :
    Ki₁ = Ki₂ ∧ e₁ = e₂ := by
  cases Ki₁ <;> cases Ki₂ <;> simp only [EctxItem.fill, reduceCtorEq] at h
  case call.call f vs ms T f' vs' ms' T' =>
    simp only [LoweredExpr.call.injEq] at h
    obtain ⟨rfl, hl, rfl⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := LoweredExpr.map_val_append_inj h₁ h₂ hl
    exact ⟨rfl, rfl⟩
  case checkEqL.checkEqR => exact absurd (LoweredExpr.checkEq.inj h).1 (h₁ _)
  case checkEqR.checkEqL => exact absurd (LoweredExpr.checkEq.inj h).1.symm (h₂ _)
  case intBinL.intBinR =>
    simp only [LoweredExpr.intBin.injEq] at h
    exact absurd h.2.2.1 (h₁ _)
  case intBinR.intBinL =>
    simp only [LoweredExpr.intBin.injEq] at h
    exact absurd h.2.2.1.symm (h₂ _)
  case primEqL.primEqR => exact absurd (LoweredExpr.primEq.inj h).1 (h₁ _)
  case primEqR.primEqL => exact absurd (LoweredExpr.primEq.inj h).1.symm (h₂ _)
  case new.new k vs ms T k' vs' ms' T' =>
    simp only [LoweredExpr.new.injEq] at h
    obtain ⟨rfl, hl, rfl⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := LoweredExpr.map_val_append_inj h₁ h₂ hl
    exact ⟨rfl, rfl⟩
  case initCtorArgs.initCtorArgs v k vs ms v' k' vs' ms' =>
    simp only [LoweredExpr.initCtor.injEq, LoweredExpr.val.injEq] at h
    obtain ⟨rfl, rfl, hl⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := LoweredExpr.map_val_append_inj h₁ h₂ hl
    exact ⟨rfl, rfl⟩
  case initCtorRecv.initCtorArgs => exact absurd (LoweredExpr.initCtor.inj h).1 (h₁ _)
  case initCtorArgs.initCtorRecv => exact absurd (LoweredExpr.initCtor.inj h).1.symm (h₂ _)
  case initFieldL.initFieldR => exact absurd (LoweredExpr.initField.inj h).1 (h₁ _)
  case initFieldR.initFieldL => exact absurd (LoweredExpr.initField.inj h).1.symm (h₂ _)
  case propertySetL.propertySetR => exact absurd (LoweredExpr.propertySet.inj h).1 (h₁ _)
  case propertySetR.propertySetL => exact absurd (LoweredExpr.propertySet.inj h).1.symm (h₂ _)
  case methodCallArgs.methodCallArgs v name vs ms T v' name' vs' ms' T' =>
    simp only [LoweredExpr.methodCall.injEq, LoweredExpr.val.injEq] at h
    obtain ⟨rfl, rfl, hl, rfl⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := LoweredExpr.map_val_append_inj h₁ h₂ hl
    exact ⟨rfl, rfl⟩
  case methodCallRecv.methodCallArgs => exact absurd (LoweredExpr.methodCall.inj h).1 (h₁ _)
  case methodCallArgs.methodCallRecv => exact absurd (LoweredExpr.methodCall.inj h).1.symm (h₂ _)
  case superCallArgs.superCallArgs v name slot vs ms T v' name' slot' vs' ms' T' =>
    simp only [LoweredExpr.superCall.injEq, LoweredExpr.val.injEq] at h
    obtain ⟨rfl, rfl, rfl, hl, rfl⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := LoweredExpr.map_val_append_inj h₁ h₂ hl
    exact ⟨rfl, rfl⟩
  case superCallRecv.superCallArgs => exact absurd (LoweredExpr.superCall.inj h).1 (h₁ _)
  case superCallArgs.superCallRecv => exact absurd (LoweredExpr.superCall.inj h).1.symm (h₂ _)
  case superSetL.superSetR => exact absurd (LoweredExpr.superSet.inj h).1 (h₁ _)
  case superSetR.superSetL => exact absurd (LoweredExpr.superSet.inj h).1.symm (h₂ _)
  case identicalL.identicalR => exact absurd (LoweredExpr.identical.inj h).1 (h₁ _)
  case identicalR.identicalL => exact absurd (LoweredExpr.identical.inj h).1.symm (h₂ _)
  case concat.concat vs ms vs' ms' =>
    simp only [LoweredExpr.concat.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := LoweredExpr.map_val_append_inj h₁ h₂ h
    exact ⟨rfl, rfl⟩
  all_goals simp_all

/--
Plug `m` into the hole of the evaluation context `k`, a list of context items, innermost first.
-/
@[expose]
public def fillCtx (k : List EctxItem) (m : LoweredExpr) : LoweredExpr :=
  k.foldl (fun m Ki => Ki.fill m) m

end DartLang
