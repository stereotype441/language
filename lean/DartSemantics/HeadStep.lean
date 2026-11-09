module
public import DartLang.RuntimeTypes
public import DartSemantics.Resolve
public import DartSemantics.State

/-!
# The head-step relation

The small-step semantics of `LoweredExpr`. A *step* takes an expression `e`, in state `σ`, to an
expression `e'`, leaving state `σ'`. Each step does its work on one subexpression of `e`, the
*redex*: the part of `e` that evaluates next. The rest of `e`, the *evaluation context*, is left
alone. For example, in `(x as int)!`, the redex is `x`, and the evaluation context is `(□ as int)!`.
A step of an expression that is itself the redex (with an empty evaluation context) is a
*head step*.

This file defines head steps, as the relation `HeadStep e σ e' σ'`. That's all that's needed to
define the semantics: every step is a head step of the redex, inside its evaluation context.
iris-lean derives the steps from the head steps and evaluation context items (`EctxItem`); see
`Language.lean`. The interpreter (`Interp.primStep`) is proved to agree with the semantics.

## Run-time subtype checks

Is-expressions and cast expressions check at run time whether a value satisfies a type (whether its
dynamic type is a subtype of the type). The check is specified by the relation `RtSub` (see
`RuntimeTypes.lean`), which may give no answer, meaning that the check doesn't terminate. To model
a check that doesn't terminate as a computation that doesn't terminate, an expression whose check
gives no answer steps to itself, forever.

## Promotion checks

When flow analysis promotes a variable, it records the promoted type in each `var v T` that reads
the variable, and likewise for a promoted property in `propertyGet m p T`. The semantics can
check, as it reads any variable or property, that the value really has its recorded type `T`.
These *promotion checks* aren't part of Dart: they are how the semantics expresses that flow
analysis is sound. (The semantics doesn't know which properties flow analysis may promote, so it
checks every property read, as it checks every variable read.) When
`SemanticParams.promotionChecks` is `PromotionChecks.verify`, a read whose promotion check fails
gets stuck, so a proof that well-typed programs don't get stuck includes a proof that flow
analysis only promotes soundly. When `SemanticParams.promotionChecks` is `PromotionChecks.trust`,
there are no promotion checks, as in Dart implementations.

The program logic, and proofs of soundness built on it, are meant to hold for every setting of
`SemanticParams.promotionChecks`: whatever the setting, such a proof must show that each promoted
read produces a value of the promoted type. The setting only changes what the resulting safety
theorem (that well-typed programs don't get stuck) says on its own: with `PromotionChecks.verify`,
it expresses that flow analysis only promotes soundly, without reference to the program logic.

A promotion check that gives no answer gets stuck, rather than stepping to itself, so that an
unsound promotion can't be hidden by a check that doesn't terminate. A sound promotion always
passes its promotion check: the value satisfies the promoted type, and the
run-time subtype check always terminates when the answer is yes
(`DartRuntimeTypeRepr.rtSub_of_le`; see `PassesPromotionCheck.of_le`).
-/

namespace DartSemantics

open DartLang

/-- Whether the semantics performs promotion checks (see the module documentation). -/
public inductive PromotionChecks where
  /-- Perform promotion checks: a read whose promotion check fails gets stuck. -/
  | verify
  /--
  Don't perform promotion checks, but trust flow analysis's promotions, as the implementations do.
  -/
  | trust
  deriving Repr, BEq, DecidableEq

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Property" => Property (τ := τ)
local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "EctxItem" => EctxItem (τ := τ)
local notation "Cell" => Cell (τ := τ)
local notation "State" => State (τ := τ)

variable (τ) in
/--
The parameters of the semantics: choices that a theorem may make, or quantify over.

This is a class so that the semantics can be an instance of iris-lean's language classes, which
must be found by instance resolution.
-/
public class SemanticParams where
  /-- Whether the semantics performs promotion checks. -/
  promotionChecks : PromotionChecks
  /--
  The program's function table: the declaration of each top-level function, by key (`none` for a
  key that isn't declared). A function's key identifies it uniquely in the program, so it isn't
  necessarily the function's name (see `LoweredExpr.call`). The program (this table and the ones
  below) is a parameter of the semantics, so that a theorem can be about one program, or quantify
  over programs. Functions may call each other, and themselves, in any way.
  -/
  functions : String → Option (FunctionDecl (τ := τ))
  /--
  The program's class table: the declaration of each class, by key (`none` for a key that isn't
  declared). A class's key identifies it uniquely in the program, as a function's does.
  -/
  classes : String → Option (ClassDecl (τ := τ))
  /--
  The program's member table: the declaration of each method, getter and setter, by key (`none`
  for a key that isn't declared). Classes' dispatch tables refer to members by these keys (see
  `ClassDecl.dispatch`), so one declaration can be shared by several classes.
  -/
  members : String → Option (MemberDecl (τ := τ))
  /--
  The program's constructor table: the declaration of each generative constructor, by key (`none`
  for a key that isn't declared).
  -/
  constructors : String → Option (ConstructorDecl (τ := τ))
  /--
  The integer mode of each top-level function, method, getter, setter and constructor, by key (as
  for `functions`, `members` and `constructors`, whose keys are all distinct): how the integer
  arithmetic in its body treats results that don't fit in 64 bits (see `IntMode`). A theorem can
  choose a mode for each function, or quantify over modes.
  -/
  intModeOf : String → IntMode

variable [P : SemanticParams τ]

/--
What instances of the class whose key is `cls` have under member name `name` (see
`ClassDecl.dispatch`): `none` if the class isn't declared, or has nothing under that name.
-/
@[expose]
public def SemanticParams.dispatch (P : SemanticParams τ) (cls name : String) : Option Member :=
  (P.classes cls).bind (·.dispatch name)

/--
The key of the superclass of the class whose key is `cls`, if it's declared and has a superclass:
the class in which a `super` access in a member that `cls` provides is resolved.
-/
@[expose]
public def SemanticParams.superclassOf (P : SemanticParams τ) (cls : String) : Option String :=
  (P.classes cls).bind (·.superclass)

/--
`body`, the body of the member or constructor whose key is `key`, provided by the class whose key
is `holder`, ready to run with `this` and the formal parameters (`xs`) bound to the cells `ℓs`:
with every integer operator's mode set to the member's integer mode, every `super` slot filled with
`holder`'s superclass, and the variables bound.
-/
@[expose]
public def SemanticParams.memberBody (P : SemanticParams τ) (key holder : String)
    (xs : List (Variable (τ := τ))) (body : LoweredExpr) (ℓs : List Loc) : LoweredExpr :=
  ((body.withIntMode (P.intModeOf key)).withSuperclass (P.superclassOf holder)).bindVariables
    (xs.zip ℓs)

/--
`PassesPromotionCheck σ v T` says that in state `σ`, value `v` passes the promotion check against
type `T` (see the module documentation). When `SemanticParams.promotionChecks` is
`PromotionChecks.trust`, every value passes.
-/
public inductive PassesPromotionCheck (σ : State) (v : Value) (T : τ) : Prop where
  /-- Without promotion checks, every value passes. -/
  | trust (h : P.promotionChecks = .trust)
  /-- With promotion checks, a value passes if it satisfies `T`. -/
  | verify {S : τ} (h : P.promotionChecks = .verify) (hS : σ.dynamicType v = some S)
      (hT : RtSub S T true)

/--
A value `v` that satisfies `T`, in that its dynamic type is `S` (`hS`), a subtype of `T` (`hT`),
passes the promotion check against `T`.
-/
public theorem PassesPromotionCheck.of_le {σ : State} {v : Value} {S T : τ}
    (hS : σ.dynamicType v = some S) (hT : S ≤ T) : PassesPromotionCheck σ v T := by
  cases h : P.promotionChecks
  · exact .verify h hS (DartRuntimeTypeRepr.rtSub_of_le hT)
  · exact .trust h

/--
`HeadStep e σ e' σ'` says that expression `e`, in state `σ`, takes a head step to `e'`, leaving
state `σ'`.

Every step is deterministic (`HeadStep.deterministic`). An expression that has completed (`val`
or `throwing`) takes no step. Any other expression with no step is *stuck*. An expression gets
stuck only when something that Dart's static checks (including flow analysis) are meant to
guarantee has failed, such as reading a variable that hasn't been assigned, or a value failing its
promotion check. Giving such an expression no step makes the failure loud: the interpreter reports
it, and the safety theorem (that well-typed programs don't get stuck) rules it out, so proving that
theorem proves the guarantee. Until the semantics covers more of Dart, an expression can also get
stuck because it uses something that isn't modeled yet: in particular, `unsupported`, the
translator's placeholder for an unsupported construct, has no head step.
-/
public inductive HeadStep : LoweredExpr → State → LoweredExpr → State → Prop where
  /-- The null literal evaluates to the null object. -/
  | null {σ : State} : HeadStep .null σ (.val .null) σ
  /-- A boolean literal evaluates to its boolean. -/
  | bool {b : Bool} {σ : State} : HeadStep (.bool b) σ (.val (.bool b)) σ
  /-- An integer literal evaluates to its integer. -/
  | int {n : Int} {σ : State} : HeadStep (.int n) σ (.val (.int n)) σ
  /--
  A local variable declaration outside a block is converted to a block containing just that
  declaration.
  -/
  | declare {v : Variable (τ := τ)} {T : τ} {startsNull : Bool} {σ : State} :
      HeadStep (.declare v T startsNull) σ (.block [.declare v T startsNull]) σ
  /-- An empty block completes normally. Its value is the null object. -/
  | blockNil {σ : State} : HeadStep (.block []) σ (.val .null) σ
  /--
  A block that starts with a declaration of local variable `v` allocates a cell for `v`, and
  resolves the references to `v` in the rest of the block to it. The cell starts out holding the
  null object if the declaration says so (which flow analysis sets it to do if `v` isn't `final`
  and its type is nullable), and uninitialized otherwise.
  -/
  | blockDeclare {v : Variable (τ := τ)} {T : τ} {startsNull : Bool} {ms : List LoweredExpr}
      {σ : State} :
      HeadStep (.block (.declare v T startsNull :: ms)) σ
        (.block (LoweredExpr.resolveBlock v σ.fresh ms))
        (σ.alloc (if startsNull then .val .null else .uninit))
  /-- A block that starts with anything else runs it, and then the rest of the block. -/
  | blockCons {m : LoweredExpr} {ms : List LoweredExpr} {σ : State}
      (h : ∀ v T startsNull, m ≠ .declare v T startsNull) :
      HeadStep (.block (m :: ms)) σ (.seq m (.block ms)) σ
  /-- Once the first part of a sequence completes normally, its value is discarded. -/
  | seq {v : Value} {m : LoweredExpr} {σ : State} : HeadStep (.seq (.val v) m) σ m σ
  /--
  Once the initializer of a let expression has evaluated to `w`, the let expression allocates a
  cell for its variable `v`, holding `w`, and continues with its body, with the references to `v`
  in it resolved to the new cell (as for a declaration; see `blockDeclare`).
  -/
  | letIn {v : Variable (τ := τ)} {w : Value} {m₂ : LoweredExpr} {σ : State} :
      HeadStep (.letIn v (.val w) m₂) σ (m₂.resolve v σ.fresh) (σ.alloc (.val w))
  /--
  A reference to a local variable evaluates to the value in its cell, if the value passes the
  promotion check against the variable's (possibly promoted) static type. Reading a variable that
  hasn't been assigned gets stuck.
  -/
  | varAt {x : Variable (τ := τ)} {T : τ} {ℓ : Loc} {v : Value} {σ : State}
      (hℓ : σ.lookup ℓ = some (.val v)) (hv : PassesPromotionCheck σ v T) :
      HeadStep (.varAt x T ℓ) σ (.val v) σ
  /--
  An assignment to a local variable stores the value in the variable's cell, and evaluates to
  that value. The cell must be a variable's cell (holding a value or uninitialized; `hc`), not an
  object's own cell. If the variable is `final`, the cell must be uninitialized: assigning to a
  `final` variable that has already been assigned gets stuck. (Dart reports a compile-time error
  for such an assignment, so implementations don't check this at run time; getting stuck makes the
  safety theorem cover flow analysis's definite unassignment check.)
  -/
  | variableSetAt {x : Variable (τ := τ)} {ℓ : Loc} {w : Value} {c : Cell} {σ : State}
      (hℓ : σ.lookup ℓ = some c) (hc : c.isVar = true)
      (hfin : x.isFinal = true → c = .uninit) :
      HeadStep (.variableSetAt x ℓ (.val w)) σ (.val w) (σ.update ℓ (.val w))
  /-- A null check on the null object is a dynamic type error. -/
  | nullCheckNull {σ : State} :
      HeadStep (.nullCheck (.val .null)) σ (.throwing (.error .typeError)) σ
  /-- A null check on any other object evaluates to that object. -/
  | nullCheck {v : Value} {σ : State} (h : v ≠ .null) : HeadStep (.nullCheck (.val v)) σ (.val v) σ
  /-- A cast evaluates to its operand if the operand satisfies `T`. -/
  | asTrue {v : Value} {S T : τ} {σ : State} (hS : σ.dynamicType v = some S)
      (h : RtSub S T true) : HeadStep (.as (.val v) T) σ (.val v) σ
  /-- A cast whose operand doesn't satisfy `T` is a dynamic type error. -/
  | asFalse {v : Value} {S T : τ} {σ : State} (hS : σ.dynamicType v = some S)
      (h : RtSub S T false) : HeadStep (.as (.val v) T) σ (.throwing (.error .typeError)) σ
  /-- If a cast's subtype check doesn't terminate, neither does the cast. -/
  | asDiverge {v : Value} {S T : τ} {σ : State} (hS : σ.dynamicType v = some S)
      (h : ∀ b, ¬ RtSub S T b) : HeadStep (.as (.val v) T) σ (.as (.val v) T) σ
  /-- An is-expression evaluates to whether its operand satisfies `T`. -/
  | is {v : Value} {S T : τ} {σ : State} {b : Bool} (hS : σ.dynamicType v = some S)
      (h : RtSub S T b) : HeadStep (.is (.val v) T) σ (.val (.bool b)) σ
  /-- If an is-expression's subtype check doesn't terminate, neither does the is-expression. -/
  | isDiverge {v : Value} {S T : τ} {σ : State} (hS : σ.dynamicType v = some S)
      (h : ∀ b, ¬ RtSub S T b) : HeadStep (.is (.val v) T) σ (.is (.val v) T) σ
  /-- A conditional whose condition is `true` evaluates its first branch. -/
  | condTrue {m₂ m₃ : LoweredExpr} {T : τ} {σ : State} :
      HeadStep (.cond (.val (.bool true)) m₂ m₃ T) σ m₂ σ
  /-- A conditional whose condition is `false` evaluates its second branch. -/
  | condFalse {m₂ m₃ : LoweredExpr} {T : τ} {σ : State} :
      HeadStep (.cond (.val (.bool false)) m₂ m₃ T) σ m₃ σ
  /--
  Reading a property of an object (`ho`) whose class dispatches the property's name to the
  implicit getter of the instance variable whose key is `iv` (`hd`) reads that instance variable's
  cell (`hf`, `hw`), if the value passes the promotion check against the property's (possibly
  promoted) static type (`hc`).
  -/
  | propertyGetField {v w : Value} {p : Property} {T : τ} {k iv : String}
      {fs : List (String × Loc)} {ℓf : Loc} {σ : State} (ho : σ.object? v = some (k, fs))
      (hd : P.dispatch k p.name = some (.field iv)) (hf : fs.lookup iv = some ℓf)
      (hw : σ.lookup ℓf = some (.val w)) (hc : PassesPromotionCheck σ w T) :
      HeadStep (.propertyGet (.val v) p T) σ (.val w) σ
  /--
  Reading a property of an object (`ho`) whose class dispatches the property's name to a getter
  that is user code (`hd`, `hm`, with no formal parameters: `hlen`) runs the getter's body, with
  `this` bound to a new cell holding the object (see `SemanticParams.memberBody`), as the body of a
  running call (`frame`). The result is then checked against the property's (possibly promoted)
  static type (`checkPromotion`).
  -/
  | propertyGetGetter {v : Value} {p : Property} {T : τ} {k key holder : String}
      {fs : List (String × Loc)} {d : MemberDecl (τ := τ)} {σ : State}
      (ho : σ.object? v = some (k, fs)) (hd : P.dispatch k p.name = some (.proc key holder))
      (hm : P.members key = some d) (hlen : d.params.length = 0) :
      HeadStep (.propertyGet (.val v) p T) σ
        (.checkPromotion T (.frame (P.memberBody key holder (d.this :: d.params) d.body
          (σ.allocAll ([v].map Cell.val)).1) T))
        (σ.allocAll ([v].map Cell.val)).2
  /--
  Once every argument of a call has been evaluated (to `vs`), the call looks up the function in the
  function table (`hf`), and checks that it has one formal parameter per argument (`hlen`). It
  allocates one cell per formal parameter, holding its argument, and runs the function's body, with
  every integer operator's mode set to the function's integer mode (`SemanticParams.intModeOf`), and
  the formal parameters bound to their cells, as the body of a running call (`frame`).

  So far, every formal parameter is a required positional parameter, and every call is a static
  call of a top-level function, so a call must pass exactly one argument per formal parameter. A
  call of a function that isn't declared, or with a different number of arguments, gets stuck;
  with these restrictions, that can't happen in a program that Dart accepts. Optional parameters
  (positional or named), which allow some arguments to be omitted, and dynamic calls, whose
  arguments are checked at run time (throwing `NoSuchMethodError` on a mismatch), aren't modeled
  yet.
  -/
  | call {f : String} {d : FunctionDecl (τ := τ)} {vs : List Value} {T : τ} {σ : State}
      (hf : P.functions f = some d) (hlen : d.params.length = vs.length) :
      HeadStep (.call f (vs.map .val) T) σ
        (.frame ((d.body.withIntMode (P.intModeOf f)).bindVariables
          (d.params.zip (σ.allocAll (vs.map Cell.val)).1)) T)
        (σ.allocAll (vs.map Cell.val)).2
  /-- A return statement, once its operand has evaluated to `v`, starts returning `v`. -/
  | ret {v : Value} {σ : State} : HeadStep (.ret (.val v)) σ (.returning v) σ
  /-- When the body of a running call returns `v`, the call completes normally with `v`. -/
  | frameReturning {v : Value} {T : τ} {σ : State} :
      HeadStep (.frame (.returning v) T) σ (.val v) σ
  /--
  When the body of a running call completes normally (falling off the end of the body), the call
  completes normally with the null object.
  -/
  | frameVal {v : Value} {T : τ} {σ : State} : HeadStep (.frame (.val v) T) σ (.val .null) σ
  /-- An intrinsic check that holds of its operand (`h`) completes normally. -/
  | checkPass {kind : CheckKind} {v : Value} {σ : State} (h : kind.holds v = true) :
      HeadStep (.check kind (.val v)) σ (.val .null) σ
  /-- An intrinsic check that doesn't hold of its operand (`h`) throws. -/
  | checkFail {kind : CheckKind} {v : Value} {σ : State} (h : kind.holds v = false) :
      HeadStep (.check kind (.val v)) σ (.throwing (.error .expectFailed)) σ
  /-- An intrinsic equality check whose operands are equal (`h`) completes normally. -/
  | checkEqPass {v₁ v₂ : Value} {σ : State} (h : σ.primEq? v₁ v₂ = some true) :
      HeadStep (.checkEq (.val v₁) (.val v₂)) σ (.val .null) σ
  /--
  An intrinsic equality check whose operands are different (`h`) throws. (One whose operands
  can't be compared gets stuck.)
  -/
  | checkEqFail {v₁ v₂ : Value} {σ : State} (h : σ.primEq? v₁ v₂ = some false) :
      HeadStep (.checkEq (.val v₁) (.val v₂)) σ (.throwing (.error .expectFailed)) σ
  /--
  A loop runs its body once, and then the loop again. (So each iteration takes at least one step,
  which is what lets the program logic reason about a loop by induction.)
  -/
  | loop {m : LoweredExpr} {σ : State} : HeadStep (.loop m) σ (.seq m (.loop m)) σ
  /--
  A labeled statement whose body completes normally completes normally too, with the null object.
  -/
  | labeledVal {l : String} {v : Value} {σ : State} :
      HeadStep (.labeled l (.val v)) σ (.val .null) σ
  /--
  A labeled statement `l` whose body breaks out of it (`breaking l`) completes normally, with the
  null object. (A break out of any other labeled statement propagates by `bubbleBreak`.)
  -/
  | labeledBreak {l : String} {σ : State} :
      HeadStep (.labeled l (.breaking l)) σ (.val .null) σ
  /-- A break statement `break l` starts breaking out of the labeled statement `l`. -/
  | brk {l : String} {σ : State} : HeadStep (.brk l) σ (.breaking l) σ
  /--
  A binary operator on integers whose operands have evaluated to `n₁` and `n₂`, and whose integer
  mode has been filled in (`mode`), evaluates to its result `v` (`h`). An arithmetic operator whose
  result doesn't fit in 64 bits, in mode `checked`, has no result, so it gets stuck; so does an
  operator whose mode hasn't been filled in, or whose operands aren't integers (which can't happen
  in a program that Dart accepts).
  -/
  | intBin {op : IntBinOp} {mode : IntMode} {n₁ n₂ : Int} {v : Value} {σ : State}
      (h : op.eval mode n₁ n₂ = some v) :
      HeadStep (.intBin op (some mode) (.val (.int n₁)) (.val (.int n₂))) σ (.val v) σ
  /--
  Unary minus on an integer `n`, whose integer mode has been filled in (`mode`), evaluates to `k`,
  the result of `-n` in that mode (`h`).
  -/
  | intNeg {mode : IntMode} {n k : Int} {σ : State} (h : mode.arith (-n) = some k) :
      HeadStep (.intNeg (some mode) (.val (.int n))) σ (.val (.int k)) σ
  /--
  Equality of values `v₁` and `v₂` that can be compared without running user code (see
  `State.primEq?`: the null object, booleans, integers and strings) evaluates to whether they're
  equal (`h`). Comparing any other values gets stuck.
  -/
  | primEq {v₁ v₂ : Value} {b : Bool} {σ : State} (h : σ.primEq? v₁ v₂ = some b) :
      HeadStep (.primEq (.val v₁) (.val v₂)) σ (.val (.bool b)) σ
  /--
  Once every argument of an instance creation has been evaluated (to `vs`), it looks up the
  constructor in the constructor table (`hk`), and the constructor's class in the class table
  (`hc`). It allocates a new object of that class (see `State.allocObject`), whose instance
  variables all start out uninitialized, runs the constructor on it (`ctorRun`), and then evaluates
  to the object.
  -/
  | new {k : String} {d : ConstructorDecl (τ := τ)} {c : ClassDecl (τ := τ)} {vs : List Value}
      {T : τ} {σ : State} (hk : P.constructors k = some d) (hc : P.classes d.cls = some c) :
      HeadStep (.new k (vs.map .val) T) σ
        (.seq (.ctorRun (σ.allocObject d.cls c.type c.instanceVariables).1 k vs)
          (.val (.obj (σ.allocObject d.cls c.type c.instanceVariables).1)))
        (σ.allocObject d.cls c.type c.instanceVariables).2
  /--
  Running a generative constructor on the object at `ℓ` looks it up in the constructor table
  (`hk`), and checks that it has one formal parameter per argument (`hlen`), as a call does. It
  allocates a cell for `this`, holding the object, and one cell per formal parameter, holding its
  argument. Then it runs the constructor's initializers and body, with `this` and the formal
  parameters bound to their cells (see `SemanticParams.memberBody`, with the constructor's class
  providing it), as the body of a running constructor (`ctorFrame`).
  -/
  | ctorRun {ℓ : Loc} {k : String} {d : ConstructorDecl (τ := τ)} {vs : List Value} {σ : State}
      (hk : P.constructors k = some d) (hlen : d.params.length = vs.length) :
      HeadStep (.ctorRun ℓ k vs) σ
        (.ctorFrame (P.memberBody k d.cls (d.this :: d.params)
          (.block (d.initializers ++ [d.body])) (σ.allocAll ((Value.obj ℓ :: vs).map Cell.val)).1))
        (σ.allocAll ((Value.obj ℓ :: vs).map Cell.val)).2
  /--
  Once its receiver and arguments have been evaluated, a `super(args)` or `this(args)` call in an
  initializer list runs the constructor on the receiver, which is the object being constructed.
  -/
  | initCtor {ℓ : Loc} {k : String} {vs : List Value} {σ : State} :
      HeadStep (.initCtor (.val (.obj ℓ)) k (vs.map .val)) σ (.ctorRun ℓ k vs) σ
  /--
  An initializer of an instance variable stores the value in the cell of the instance variable
  whose key (see `ClassDecl.instanceVariables`) is `name` (`hf`) of the object that the receiver
  refers to (`ho`). The cell must be an instance variable's (holding a value or uninitialized; `hℓf`
  and `hc`).
  -/
  | initField {v w : Value} {name k : String} {fs : List (String × Loc)} {ℓf : Loc} {c : Cell}
      {σ : State} (ho : σ.object? v = some (k, fs)) (hf : fs.lookup name = some ℓf)
      (hℓf : σ.lookup ℓf = some c) (hc : c.isVar = true) :
      HeadStep (.initField (.val v) name (.val w)) σ (.val .null) (σ.update ℓf (.val w))
  /--
  An assignment to a property whose setter is the implicit setter of an instance variable (the
  receiver's class dispatches `name=` to `Member.field iv`; `hd`) stores the value in the cell of
  the instance variable whose key is `iv` (`hf`), and evaluates to the value.
  -/
  | propertySetField {v w : Value} {name k iv : String} {fs : List (String × Loc)} {ℓf : Loc}
      {c : Cell} {σ : State} (ho : σ.object? v = some (k, fs))
      (hd : P.dispatch k (name ++ "=") = some (.field iv)) (hf : fs.lookup iv = some ℓf)
      (hℓf : σ.lookup ℓf = some c) (hc : c.isVar = true) :
      HeadStep (.propertySet (.val v) name (.val w)) σ (.val w) (σ.update ℓf (.val w))
  /--
  When the body of a running constructor returns (by `return;`), the constructor completes
  normally, with the null object.
  -/
  | ctorFrameReturning {v : Value} {σ : State} :
      HeadStep (.ctorFrame (.returning v)) σ (.val .null) σ
  /-- When the body of a running constructor completes normally, so does the constructor. -/
  | ctorFrameVal {v : Value} {σ : State} : HeadStep (.ctorFrame (.val v)) σ (.val .null) σ
  /--
  An assignment to a property of an object (`ho`) whose class dispatches the setter `name=` to a
  setter that is user code (`hd`, `hm`, with one formal parameter: `hlen`) runs the setter's body,
  with `this` and the formal parameter bound to new cells holding the object and the value (see
  `SemanticParams.memberBody`), as the body of a running call (`frame`), and then evaluates to the
  value.
  -/
  | propertySetSetter {v w : Value} {name k key holder : String} {fs : List (String × Loc)}
      {d : MemberDecl (τ := τ)} {σ : State} (ho : σ.object? v = some (k, fs))
      (hd : P.dispatch k (name ++ "=") = some (.proc key holder)) (hm : P.members key = some d)
      (hlen : d.params.length = 1) :
      HeadStep (.propertySet (.val v) name (.val w)) σ
        (.seq (.frame (P.memberBody key holder (d.this :: d.params) d.body
          (σ.allocAll ([v, w].map Cell.val)).1) Γ.Null) (.val w))
        (σ.allocAll ([v, w].map Cell.val)).2
  /--
  Once its receiver and arguments have been evaluated (to `v` and `vs`), a method call on an
  object (`ho`) whose class dispatches the method's name to a method (`hd`, `hm`) with one formal
  parameter per argument (`hlen`) runs the method's body, with `this` and the formal parameters
  bound to new cells holding the receiver and the arguments (see `SemanticParams.memberBody`), as
  the body of a running call (`frame`).

  A method call on anything else gets stuck: on the null object, a boolean or an integer, or with a
  member name that the class doesn't dispatch to a method, or with the wrong number of arguments.
  None of these can happen in a program that Dart accepts, since the subset of Dart modeled so far
  has no dynamic calls, and no members of core library classes.
  -/
  | methodCall {v : Value} {name k key holder : String} {fs : List (String × Loc)}
      {d : MemberDecl (τ := τ)} {vs : List Value} {T : τ} {σ : State}
      (ho : σ.object? v = some (k, fs)) (hd : P.dispatch k name = some (.proc key holder))
      (hm : P.members key = some d) (hlen : d.params.length = vs.length) :
      HeadStep (.methodCall (.val v) name (vs.map .val) T) σ
        (.frame (P.memberBody key holder (d.this :: d.params) d.body
          (σ.allocAll ((v :: vs).map Cell.val)).1) T)
        (σ.allocAll ((v :: vs).map Cell.val)).2
  /--
  Once its receiver and arguments have been evaluated (to `v` and `vs`), a super method call whose
  slot has been filled in with `s` looks the method's name up in `s`'s dispatch table (`hd`, `hm`),
  and runs the method as `methodCall` does, with the receiver `v` as `this`.
  -/
  | superCall {v : Value} {name s key holder : String} {d : MemberDecl (τ := τ)} {vs : List Value}
      {T : τ} {σ : State} (hd : P.dispatch s name = some (.proc key holder))
      (hm : P.members key = some d) (hlen : d.params.length = vs.length) :
      HeadStep (.superCall (.val v) name (some s) (vs.map .val) T) σ
        (.frame (P.memberBody key holder (d.this :: d.params) d.body
          (σ.allocAll ((v :: vs).map Cell.val)).1) T)
        (σ.allocAll ((v :: vs).map Cell.val)).2
  /--
  A super property extraction whose slot has been filled in with `s`, where `s`'s dispatch table
  gives the property's name to the implicit getter of the instance variable whose key is `iv`
  (`hd`), reads that instance variable (`hf`, `hw`) of the object that the receiver refers to
  (`ho`), as `propertyGetField` does. If the receiver's class has an instance variable with the same
  name that shadows it, that's a different instance variable, with a different key, so this reads
  the superclass's one.
  -/
  | superGetField {v w : Value} {name s k iv : String} {T : τ} {fs : List (String × Loc)}
      {ℓf : Loc} {σ : State} (hd : P.dispatch s name = some (.field iv))
      (ho : σ.object? v = some (k, fs)) (hf : fs.lookup iv = some ℓf)
      (hw : σ.lookup ℓf = some (.val w)) (hc : PassesPromotionCheck σ w T) :
      HeadStep (.superGet (.val v) name (some s) T) σ (.val w) σ
  /--
  A super property extraction whose slot has been filled in with `s`, where `s`'s dispatch table
  gives the property's name to a getter that is user code (`hd`, `hm`, `hlen`), runs the getter
  with the receiver as `this`, as `propertyGetGetter` does.
  -/
  | superGetGetter {v : Value} {name s key holder : String} {T : τ} {d : MemberDecl (τ := τ)}
      {σ : State} (hd : P.dispatch s name = some (.proc key holder)) (hm : P.members key = some d)
      (hlen : d.params.length = 0) :
      HeadStep (.superGet (.val v) name (some s) T) σ
        (.checkPromotion T (.frame (P.memberBody key holder (d.this :: d.params) d.body
          (σ.allocAll ([v].map Cell.val)).1) T))
        (σ.allocAll ([v].map Cell.val)).2
  /--
  A super property assignment whose slot has been filled in with `s`, where `s`'s dispatch table
  gives the setter `name=` to the implicit setter of the instance variable whose key is `iv`
  (`hd`), stores the value in that instance variable (`hf`) of the object that the receiver refers
  to (`ho`), as `propertySetField` does.
  -/
  | superSetField {v w : Value} {name s k iv : String} {fs : List (String × Loc)} {ℓf : Loc}
      {c : Cell} {σ : State} (hd : P.dispatch s (name ++ "=") = some (.field iv))
      (ho : σ.object? v = some (k, fs)) (hf : fs.lookup iv = some ℓf)
      (hℓf : σ.lookup ℓf = some c) (hc : c.isVar = true) :
      HeadStep (.superSet (.val v) name (some s) (.val w)) σ (.val w) (σ.update ℓf (.val w))
  /--
  A super property assignment whose slot has been filled in with `s`, where `s`'s dispatch table
  gives the setter `name=` to a setter that is user code (`hd`, `hm`, `hlen`), runs the setter with
  the receiver as `this`, as `propertySetSetter` does.
  -/
  | superSetSetter {v w : Value} {name s key holder : String} {d : MemberDecl (τ := τ)}
      {σ : State} (hd : P.dispatch s (name ++ "=") = some (.proc key holder))
      (hm : P.members key = some d) (hlen : d.params.length = 1) :
      HeadStep (.superSet (.val v) name (some s) (.val w)) σ
        (.seq (.frame (P.memberBody key holder (d.this :: d.params) d.body
          (σ.allocAll ([v, w].map Cell.val)).1) Γ.Null) (.val w))
        (σ.allocAll ([v, w].map Cell.val)).2
  /--
  Once the body of a running getter has completed normally with `w`, the result passes on, if it
  passes the promotion check against the property's (possibly promoted) static type (`hc`).
  -/
  | checkPromotion {w : Value} {T : τ} {σ : State} (hc : PassesPromotionCheck σ w T) :
      HeadStep (.checkPromotion T (.val w)) σ (.val w) σ
  /--
  `identical` of values `v₁` and `v₂` that can be compared (anything but exception objects and
  captured continuations) evaluates to whether they're the same object (`h`).
  -/
  | identical {v₁ v₂ : Value} {b : Bool} {σ : State} (h : Value.identical? v₁ v₂ = some b) :
      HeadStep (.identical (.val v₁) (.val v₂)) σ (.val (.bool b)) σ
  /--
  A constant evaluates to its value, which `State.constant?` gives (`h`): the null object, a
  boolean or an integer is the value itself; any other constant evaluates to its canonical object,
  which is allocated (and recorded in the table of constants) by the constant's first evaluation.
  -/
  | constant {c : ConstValue} {v : Value} {σ σ' : State} (h : σ.constant? c = some (v, σ')) :
      HeadStep (.constant c) σ (.val v) σ'
  /--
  Once every part of a string concatenation has been evaluated (to `vs`), and each has a string
  form (`h`; see `State.stringPart?`), the concatenation allocates a new string object holding
  their concatenation, and evaluates to it. The new object is never a constant's canonical object.
  -/
  | concat {vs : List Value} {cus : List (List UInt16)} {σ : State}
      (h : vs.mapM σ.stringPart? = some cus) :
      HeadStep (.concat (vs.map .val)) σ (.val (.obj σ.fresh)) (σ.alloc (.string cus.flatten))
  /--
  An exception propagates outward one evaluation context item per step: whatever was to be done
  with the value of the hole is abandoned.

  Every evaluation context item so far propagates exceptions, including the body of a running call
  (`frame`), so an exception propagates out of the call. Once the semantics has `try`
  statements, their context items will handle exceptions instead (running the matching `catch`
  clause, or the `finally` clause), so this rule will gain a hypothesis that `Ki` isn't one of
  them.
  -/
  | bubbleException {Ki : EctxItem} {v : Value} {σ : State} :
      HeadStep (Ki.fill (.throwing v)) σ (.throwing v) σ
  /--
  A return propagates outward in the same way, through every evaluation context item that doesn't
  handle it (`hKi`): that is, up to the body of the running call (`frame`) or constructor
  (`ctorFrame`).
  -/
  | bubbleReturn {Ki : EctxItem} {v : Value} {σ : State} (hKi : Ki.handlesReturn = false) :
      HeadStep (Ki.fill (.returning v)) σ (.returning v) σ
  /--
  A break out of labeled statement `l` propagates outward in the same way, through every
  evaluation context item that doesn't handle it (`hKi`): that is, up to the labeled statement `l`.

  A break doesn't propagate out of the body of a running call or constructor (`frame` and
  `ctorFrame`, the items that handle returns; `hret`): labels are local to a function, so a break
  can't target a labeled statement in a caller. A break that reaches the body of a running call or
  constructor gets stuck, which can't happen in a program that Dart accepts.
  -/
  | bubbleBreak {Ki : EctxItem} {l : String} {σ : State} (hKi : Ki.handlesBreak l = false)
      (hret : Ki.handlesReturn = false) :
      HeadStep (Ki.fill (.breaking l)) σ (.breaking l) σ

/--
A head step of an expression whose hole holds `m`, which isn't a value (`hm`), propagates `m`: if
`Ki.fill m` takes a head step to `e'` in state `σ'` (`h`), then `e' = m` and `σ' = σ`. Here `m`
must not be a return that `Ki` handles (`hret`), or a break out of a labeled statement that `Ki`
handles (`hbrk`). (Only `throwing`, `returning` and `breaking` expressions propagate; with
anything else in the hole, `Ki.fill m` takes no head step at all.)
-/
public theorem HeadStep.fill_propagates {Ki : EctxItem} {m e' : LoweredExpr} {σ σ' : State}
    (hm : ∀ v, m ≠ .val v) (hret : ∀ v, m = .returning v → Ki.handlesReturn = false)
    (hbrk : ∀ l, m = .breaking l → Ki.handlesBreak l = false)
    (h : HeadStep (Ki.fill m) σ e' σ') : e' = m ∧ σ' = σ := by
  generalize hE : Ki.fill m = E at h
  cases h
  case bubbleException | bubbleReturn | bubbleBreak =>
    obtain ⟨-, rfl⟩ := EctxItem.fill_inj hm (by simp) hE
    exact ⟨rfl, rfl⟩
  all_goals cases Ki <;> simp only [EctxItem.fill, reduceCtorEq] at hE
  all_goals simp_all [EctxItem.handlesReturn, EctxItem.handlesBreak]

/--
The semantics is deterministic: an expression takes at most one head step. If `e`, in state `σ`,
takes head steps to `e₁` in state `σ₁` (`h₁`) and to `e₂` in state `σ₂` (`h₂`), they're the same
expression (`e₁ = e₂`) and the same state (`σ₁ = σ₂`).
-/
public theorem HeadStep.deterministic {e e₁ e₂ : LoweredExpr} {σ σ₁ σ₂ : State}
    (h₁ : HeadStep e σ e₁ σ₁) (h₂ : HeadStep e σ e₂ σ₂) : e₁ = e₂ ∧ σ₁ = σ₂ := by
  have h₁' := h₁
  generalize hE : e = E at h₂
  -- When either step propagates an abrupt completion out of a context item, `fill_propagates`
  -- shows that the other step does the same, without a case split on the item.
  cases h₁
  case bubbleException | bubbleReturn | bubbleBreak =>
    subst hE
    exact And.imp Eq.symm Eq.symm (HeadStep.fill_propagates (fun _ h => by cases h)
      (fun _ h => by cases h <;> assumption) (fun _ h => by cases h <;> assumption) h₂)
  all_goals cases h₂
  all_goals first
    -- Only a propagation has a context item among its parameters.
    | (have _ : EctxItem := by assumption
       rw [hE] at h₁'
       have R := HeadStep.fill_propagates (fun _ h => by cases h)
         (fun _ h => by cases h <;> assumption) (fun _ h => by cases h <;> assumption) h₁'
       -- `rw` also rewrote the expression that `h₁'` steps to if it's the same expression (the
       -- step of a check that doesn't terminate), so `hE` is needed to undo that.
       first
         | exact R
         | exact ⟨hE.trans R.1, R.2⟩)
    | skip
  -- Otherwise neither step propagates, and both are steps of the same expression. (Or one does,
  -- but the other step's result contains the expression, which defeated the `rw` above; then a
  -- case split on the item shows that the propagation can't apply.)
  all_goals
    (try cases ‹EctxItem›) <;> (try simp only [EctxItem.fill, reduceCtorEq] at hE)
  all_goals (try simp_all)
  all_goals first
    | grind [rtSub_unique]
    | (cases ‹Bool› <;> grind)

end DartSemantics
