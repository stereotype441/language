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
  The implementation of getters that are user code (rather than the implicit getter of an instance
  variable): `getterImpl p v σ` is the result of reading property `p` of value `v` in state `σ`,
  or `none` if the read gets stuck.

  In Dart, a getter runs arbitrary code. Until the semantics has instance members (calls so far
  are only of top-level functions), a getter is modeled as a pure function of the state: it can't
  change the state, throw, or fail to terminate. Theorems quantify over all implementations that
  are well-formed, in the sense that the result (if any) has the property's static type. This
  parameter is a placeholder. Once the semantics has instance members, reading a property whose
  getter is user code will invoke the getter like any other call, and `getterImpl` will be
  removed. Theorems will then quantify over programs instead, assuming that each getter is well
  typed.
  -/
  getterImpl : Property → Value → State → Option Value
  /--
  The program's function table: the declaration of each top-level function, by key (`none` for a
  key that isn't declared). A function's key identifies it uniquely in the program, so it isn't
  necessarily the function's name (see `LoweredExpr.call`). The program is a parameter of the
  semantics, like `getterImpl`, so that a theorem can be about one program, or quantify over
  programs. Functions may call each other, and themselves, in any way.
  -/
  functions : String → Option (FunctionDecl (τ := τ))
  /--
  The integer mode of each top-level function, by key (as for `functions`): how the integer
  arithmetic in its body treats results that don't fit in 64 bits (see `IntMode`). A theorem can
  choose a mode for each function, or quantify over modes.
  -/
  intModeOf : String → IntMode

variable [P : SemanticParams τ]

/--
The location of the cell holding instance variable `name` of the object that value `v` refers
to, if `v` refers to an object that has such an instance variable. Reading property `name` of such
an object runs the instance variable's implicit getter, which reads the cell. Reading any other
property runs a getter that is user code.

This lookup has two known gaps, which will be closed when the semantics has class declarations:
- In Dart, a subclass can override an inherited instance variable with a getter. Its objects
  still have the inherited instance variable, but reading the property runs the subclass's
  getter, not the implicit getter. The class declarations, not the object's instance variables,
  should decide which getter runs.
- Instance variables are matched by name, which disregards privacy. An object can have two
  distinct instance variables named `_foo`, declared in different libraries by different classes
  in its superclass chain. Which one a property read reads depends on the library that the code
  doing the reading is in. Reading a property whose getter is user code (and, later, calling a
  setter or method) depends on the library in the same way.
-/
@[expose]
public def State.instanceVariable? (σ : State) (v : Value) (name : String) : Option Loc :=
  match v with
  | .obj ℓ =>
    match σ.lookup ℓ with
    | some (.object _ fs) => fs.lookup name
    | _ => none
  | _ => none

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
  A reference to a local variable evaluates to the value in its cell, if the value passes the
  promotion check against the variable's (possibly promoted) static type. Reading a variable that
  hasn't been assigned gets stuck.
  -/
  | varAt {x : Variable (τ := τ)} {T : τ} {ℓ : Loc} {v : Value} {σ : State}
      (hℓ : σ.lookup ℓ = some (.val v)) (hv : PassesPromotionCheck σ v T) :
      HeadStep (.varAt x T ℓ) σ (.val v) σ
  /--
  An assignment to a local variable stores the value in the variable's cell, and evaluates to
  that value. The cell must belong to a local variable (holding a value or uninitialized), not be
  an object's own cell. If the variable is `final`, the cell must be uninitialized: assigning to a
  `final` variable that has already been assigned gets stuck. (Dart reports a compile-time error
  for such an assignment, so implementations don't check this at run time; getting stuck makes the
  safety theorem cover flow analysis's definite unassignment check.)
  -/
  | variableSetAt {x : Variable (τ := τ)} {ℓ : Loc} {w : Value} {c : Cell} {σ : State}
      (hℓ : σ.lookup ℓ = some c) (hc : ∀ C fs, c ≠ .object C fs)
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
  Reading a property whose getter is the implicit getter of an instance variable (see
  `State.instanceVariable?`) reads the instance variable's cell, if the value passes the promotion
  check against the property's (possibly promoted) static type.
  -/
  | propertyGetField {v w : Value} {p : Property} {T : τ} {ℓf : Loc} {σ : State}
      (hf : σ.instanceVariable? v p.name = some ℓf) (hw : σ.lookup ℓf = some (.val w))
      (hc : PassesPromotionCheck σ w T) :
      HeadStep (.propertyGet (.val v) p T) σ (.val w) σ
  /--
  Reading any other property runs its getter, which is user code (see
  `SemanticParams.getterImpl`), if the result passes the promotion check against the property's
  (possibly promoted) static type.
  -/
  | propertyGetGetter {v w : Value} {p : Property} {T : τ} {σ : State}
      (hf : σ.instanceVariable? v p.name = none) (hg : P.getterImpl p v σ = some w)
      (hc : PassesPromotionCheck σ w T) :
      HeadStep (.propertyGet (.val v) p T) σ (.val w) σ
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
  | checkEqPass {v₁ v₂ : Value} {σ : State} (h : Value.primEq? v₁ v₂ = some true) :
      HeadStep (.checkEq (.val v₁) (.val v₂)) σ (.val .null) σ
  /--
  An intrinsic equality check whose operands are different (`h`) throws. (One whose operands
  can't be compared gets stuck.)
  -/
  | checkEqFail {v₁ v₂ : Value} {σ : State} (h : Value.primEq? v₁ v₂ = some false) :
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
  Equality of values `v₁` and `v₂` that can be compared (the null object, booleans and integers)
  evaluates to whether they're equal (`h`). Comparing any other values gets stuck.
  -/
  | primEq {v₁ v₂ : Value} {b : Bool} {σ : State} (h : Value.primEq? v₁ v₂ = some b) :
      HeadStep (.primEq (.val v₁) (.val v₂)) σ (.val (.bool b)) σ
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
  handle it (`hKi`): that is, up to the body of the running call (`frame`).
  -/
  | bubbleReturn {Ki : EctxItem} {v : Value} {σ : State} (hKi : Ki.handlesReturn = false) :
      HeadStep (Ki.fill (.returning v)) σ (.returning v) σ
  /--
  A break out of labeled statement `l` propagates outward in the same way, through every
  evaluation context item that doesn't handle it (`hKi`): that is, up to the labeled statement `l`.

  A break doesn't propagate out of the body of a running call (`frame`, the only item that handles
  returns; `hret`): labels are local to a function, so a break can't target a labeled statement in
  a caller. A break that reaches the body of a running call gets stuck, which can't happen in a
  program that Dart accepts.
  -/
  | bubbleBreak {Ki : EctxItem} {l : String} {σ : State} (hKi : Ki.handlesBreak l = false)
      (hret : Ki.handlesReturn = false) :
      HeadStep (Ki.fill (.breaking l)) σ (.breaking l) σ

/--
The semantics is deterministic: an expression takes at most one head step. If `e`, in state `σ`,
takes head steps to `e₁` in state `σ₁` (`h₁`) and to `e₂` in state `σ₂` (`h₂`), they're the same
expression (`e₁ = e₂`) and the same state (`σ₁ = σ₂`).
-/
public theorem HeadStep.deterministic {e e₁ e₂ : LoweredExpr} {σ σ₁ σ₂ : State}
    (h₁ : HeadStep e σ e₁ σ₁) (h₂ : HeadStep e σ e₂ σ₂) : e₁ = e₂ ∧ σ₁ = σ₂ := by
  generalize hE : e = E at h₂
  cases h₁ <;> cases h₂
  -- When both steps propagate an abrupt completion out of a context item, `EctxItem.fill_inj`
  -- shows that the items and the completions are the same, without a case split on both items.
  case bubbleException.bubbleException | bubbleException.bubbleReturn
      | bubbleException.bubbleBreak | bubbleReturn.bubbleException | bubbleReturn.bubbleReturn
      | bubbleReturn.bubbleBreak | bubbleBreak.bubbleException | bubbleBreak.bubbleReturn
      | bubbleBreak.bubbleBreak =>
    obtain ⟨-, he⟩ := EctxItem.fill_inj (by simp) (by simp) hE
    simp_all
  -- Otherwise at most one of the steps is a propagation, so one case split on its item suffices.
  all_goals
    (try cases ‹EctxItem›) <;> (try simp only [EctxItem.fill, reduceCtorEq] at hE)
  all_goals (try simp_all [EctxItem.handlesReturn, EctxItem.handlesBreak])
  all_goals first
    | grind [rtSub_unique]
    | (cases ‹Bool› <;> grind)

end DartSemantics
