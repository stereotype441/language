module
public import DartSemantics.PrimitiveLaws

/-!
# Proof-mode tactics

Tactics for proving weakest preconditions of `LoweredExpr`s in iris-lean's proof mode, modeled on
iris-lean's HeapLang tactics (whose own `wp_*` tactics only work for HeapLang). HeapLang is the
small example language that comes with Iris, which most Iris material uses; its tactics are the
usual way to step through a program in a proof. (The README's "Reading the Iris parts" section
explains proof mode, and weakest preconditions.)

Each tactic takes one or more steps of the program in the goal, so that a proof follows the
program's execution:

- `wp_value`: when the expression has completed, replace its weakest precondition with the
  postcondition applied to its outcome.
- `wp_pure`: take one head step that doesn't depend on, or change, the state.
- `wp_bind`: focus on the subexpression in evaluation position, if it hasn't completed, by binding
  over one evaluation context item.
- `wp_pures`: repeat the three above, stepping into the body of a running call, constructor or
  labeled statement (`dart_wp_enter`), until none applies. The goal is then either a
  postcondition, or a weakest precondition of an expression whose next step involves the state
  (or a run-time subtype check), wrapped in the evaluation context it came from.
- `wp_alloc ℓ H`: take the step of a declaration at the start of a block (or of the statements of a
  block with a value), introducing the new cell `ℓ` and its points-to `H`.
- `wp_let ℓ H`: take the step of a let expression whose initializer has evaluated, introducing the
  new cell `ℓ` of its variable and its points-to `H`.
- `wp_load H`: take the step of reading a variable or an instance variable, using the points-to
  `H` for the cell read. The value's dynamic type is proved automatically for the null object,
  booleans, integers, objects whose header is in the context, and values with a `HasDynamicType`
  hypothesis in the context. Pure side conditions (such as the subtype fact for the promotion
  check) are proved by `decide` or `rfl` when they can be, and otherwise left as goals after the
  main one.
- `wp_store H`: take the step of an assignment to a local variable, using the points-to `H` for
  the variable's cell, which afterwards holds the value assigned. If the variable may be `final`,
  the cell must be unassigned: that side condition is proved when the variable isn't `final`, or
  the cell is `.uninit`, and otherwise left as a goal after the main one.
- `wp_call hf`: take the step of a call of a top-level function whose arguments are all values,
  given the function table's declaration of it (`hf`). `dart_bind_params` then binds the formal
  parameters in the body, once their cells' locations are concrete.
- `wp_call_spec H`: take a call of a top-level function whose arguments are all values, using its
  specification `H` (a `FunSpec`).
- `wp_int_checked`: take the step of an arithmetic operator in integer mode `checked` whose result
  can't be computed by `rfl` (because its operands aren't concrete numbers), leaving the side
  condition that the result is in 64-bit range as a goal.
- `wp_loop_step`: unroll one iteration of a loop. Usually the loop invariant rule is more
  convenient: `wp_loop_inv I`.
- `wp_loop_inv I`: apply the loop invariant rule to a loop, with invariant `I`, leaving the goals
  that `I` holds before the loop, and that one iteration of the body preserves it.
- `wp_new hk hc`: take the step of an instance creation whose arguments are all values, given the
  tables' declarations of the constructor (`hk`) and its class (`hc`), introducing the new object.
  `wp_ctor_run hk` then takes the step of running the constructor.
- `wp_method hd hm`: take the step of a method call on an object whose arguments are all values,
  given its class's dispatch of the method's name (`hd`) and the member table's declaration of the
  member (`hm`). The object's header must be in the context.
- `wp_method_spec H hd hm`: take such a method call using the member's specification `H` (a
  `MemberSpec`).
- `wp_const ℓ Hl Hc`: take the step of a string constant, introducing its canonical object `ℓ`, a
  persistent points-to `Hl` for its cell, and `Hc : IsConst τ c ℓ`.
- `wp_concat cus ℓ H Hf`: take the step of a string concatenation whose parts are all values,
  given their string forms `cus`, introducing the new string `ℓ`, a persistent points-to `H` for
  its cell, and `Hf : Fresh τ ℓ`.

`wp_pures` also takes the steps of literals, constants that are the null object, booleans or
integers, returns, labeled statements and breaks (and the propagation of returns and breaks), the
body of a running call (`frame`) or constructor (`ctorFrame`) once it has completed, `super(args)`
and `this(args)` calls in initializer lists, and intrinsic checks, arithmetic, comparisons,
equality and `identical` whose answer `rfl` can compute. It takes the steps of assertions
(`assert` and `assertFail`) too, once a hypothesis in the Lean context says whether assertions are
checked (`P.assertsEnabled = true` or `= false`). It doesn't run a loop, which it would unroll
forever. It reasons about the body of a running call (`frame`) or constructor (`ctorFrame`), or of
a labeled statement, separately from the outcome of the call, constructor or labeled statement: it
steps into the body (`tac_wp_frame`, `tac_wp_ctorFrame` and `tac_wp_labeled`), and once the body
has completed, takes the step out of it.

Steps that involve a run-time subtype check (cast expressions and is-expressions), or the state in
other ways (such as assignments to instance variables, getters and setters, `super` accesses, and
comparisons of strings), are taken by applying the laws in `PrimitiveLaws.lean` directly.

Each tactic works by applying a lemma whose conclusion is a proof-mode goal `Δ ⊢ WP e {{ Φ }}`
(where `Δ` is the proof mode's context of Iris hypotheses) for a particular shape of `e`, so that
Lean's unifier, rather than iris-lean's `iapply`, matches it against the goal. (`iapply` doesn't
unfold definitions such as `EctxItem.fill`.)

These macros are deliberately simple. If their error messages or performance become a problem once
there are significant proofs, a meta-level implementation (in the style of Rocq's HeapLang
tactics, with a `PureExec` class and a tactic that finds the redex in an evaluation context, or
tactics that build proof terms directly) may be worth the extra code.
-/

namespace DartSemantics

open DartLang Iris Iris.BI Iris.ProgramLogic Iris.Std

variable {τ : Type}

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)
local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Cell" => Cell (τ := τ)

/-! Rewrite rules that `dart_wp_tidy` uses to tidy goals after a step. -/

public theorem tidy_toExpr_normal (v : Value) :
    (DartLang.Outcome.normal v).toExpr = LoweredExpr.val v := rfl
public theorem tidy_toExpr_throwing (v : Value) :
    (DartLang.Outcome.throwing v).toExpr = LoweredExpr.throwing v := rfl
public theorem tidy_fill_nullCheck (m : LoweredExpr) :
    (EctxItem.nullCheck (τ := τ)).fill m = .nullCheck m := rfl
public theorem tidy_fill_as (T : τ) (m : LoweredExpr) : (EctxItem.as T).fill m = .as m T := rfl
public theorem tidy_fill_is (T : τ) (m : LoweredExpr) : (EctxItem.is T).fill m = .is m T := rfl
public theorem tidy_fill_cond (m₂ m₃ : LoweredExpr) (T : τ) (m : LoweredExpr) :
    (EctxItem.cond m₂ m₃ T).fill m = .cond m m₂ m₃ T := rfl
public theorem tidy_fill_propertyGet (p : Property) (T : τ) (m : LoweredExpr) :
    (EctxItem.propertyGet p T).fill m = .propertyGet m p T := rfl
public theorem tidy_fill_seq (m₂ m : LoweredExpr) : (EctxItem.seq m₂).fill m = .seq m m₂ := rfl
public theorem tidy_fill_variableSetAt (x : Variable) (ℓ : Loc) (m : LoweredExpr) :
    (EctxItem.variableSetAt x ℓ).fill m = .variableSetAt x ℓ m := rfl
public theorem tidy_toExpr_returning (v : Value) :
    (DartLang.Outcome.returning v).toExpr = LoweredExpr.returning v := rfl
public theorem tidy_fill_call (f : String) (vs : List Value) (ms : List LoweredExpr) (T : τ)
    (m : LoweredExpr) : (EctxItem.call f vs ms T).fill m = .call f (vs.map .val ++ m :: ms) T :=
  rfl
public theorem tidy_fill_ret (m : LoweredExpr) : (EctxItem.ret (τ := τ)).fill m = .ret m := rfl
public theorem tidy_fill_frame (T : τ) (m : LoweredExpr) : (EctxItem.frame T).fill m = .frame m T :=
  rfl
public theorem tidy_fill_check (kind : CheckKind) (m : LoweredExpr) :
    (EctxItem.check (τ := τ) kind).fill m = .check kind m := rfl
public theorem tidy_fill_checkEqL (m₂ m : LoweredExpr) :
    (EctxItem.checkEqL m₂).fill m = .checkEq m m₂ := rfl
public theorem tidy_fill_checkEqR (v₁ : Value) (m : LoweredExpr) :
    (EctxItem.checkEqR v₁).fill m = .checkEq (.val v₁) m := rfl
public theorem tidy_toExpr_breaking (l : String) :
    (DartLang.Outcome.breaking (τ := τ) l).toExpr = LoweredExpr.breaking l := rfl
public theorem tidy_fill_labeled (l : String) (m : LoweredExpr) :
    (EctxItem.labeled (τ := τ) l).fill m = .labeled l m := rfl
public theorem tidy_fill_intBinL (op : IntBinOp) (mode : Option IntMode) (m₂ m : LoweredExpr) :
    (EctxItem.intBinL op mode m₂).fill m = .intBin op mode m m₂ := rfl
public theorem tidy_fill_intBinR (op : IntBinOp) (mode : Option IntMode) (v₁ : Value)
    (m : LoweredExpr) : (EctxItem.intBinR op mode v₁).fill m = .intBin op mode (.val v₁) m := rfl
public theorem tidy_fill_intNeg (mode : Option IntMode) (m : LoweredExpr) :
    (EctxItem.intNeg (τ := τ) mode).fill m = .intNeg mode m := rfl
public theorem tidy_fill_primEqL (m₂ m : LoweredExpr) :
    (EctxItem.primEqL m₂).fill m = .primEq m m₂ := rfl
public theorem tidy_fill_primEqR (v₁ : Value) (m : LoweredExpr) :
    (EctxItem.primEqR v₁).fill m = .primEq (.val v₁) m := rfl
public theorem tidy_fill_new (k : String) (vs : List Value) (ms : List LoweredExpr) (T : τ)
    (m : LoweredExpr) : (EctxItem.new k vs ms T).fill m = .new k (vs.map .val ++ m :: ms) T :=
  rfl
public theorem tidy_fill_initCtorRecv (k : String) (args : List LoweredExpr) (m : LoweredExpr) :
    (EctxItem.initCtorRecv k args).fill m = .initCtor m k args := rfl
public theorem tidy_fill_initCtorArgs (v : Value) (k : String) (vs : List Value)
    (ms : List LoweredExpr) (m : LoweredExpr) :
    (EctxItem.initCtorArgs v k vs ms).fill m = .initCtor (.val v) k (vs.map .val ++ m :: ms) := rfl
public theorem tidy_fill_initFieldL (name : String) (m₂ m : LoweredExpr) :
    (EctxItem.initFieldL name m₂).fill m = .initField m name m₂ := rfl
public theorem tidy_fill_initFieldR (v₁ : Value) (name : String) (m : LoweredExpr) :
    (EctxItem.initFieldR v₁ name).fill m = .initField (.val v₁) name m := rfl
public theorem tidy_fill_propertySetL (name : String) (m₂ m : LoweredExpr) :
    (EctxItem.propertySetL name m₂).fill m = .propertySet m name m₂ := rfl
public theorem tidy_fill_propertySetR (v₁ : Value) (name : String) (m : LoweredExpr) :
    (EctxItem.propertySetR v₁ name).fill m = .propertySet (.val v₁) name m := rfl
public theorem tidy_fill_ctorFrame (m : LoweredExpr) :
    (EctxItem.ctorFrame (τ := τ)).fill m = .ctorFrame m := rfl
public theorem tidy_fill_methodCallRecv (name : String) (args : List LoweredExpr) (T : τ)
    (m : LoweredExpr) : (EctxItem.methodCallRecv name args T).fill m = .methodCall m name args T :=
  rfl
public theorem tidy_fill_methodCallArgs (v : Value) (name : String) (vs : List Value)
    (ms : List LoweredExpr) (T : τ) (m : LoweredExpr) :
    (EctxItem.methodCallArgs v name vs ms T).fill m =
      .methodCall (.val v) name (vs.map .val ++ m :: ms) T := rfl
public theorem tidy_fill_superCallRecv (name : String) (slot : Option String)
    (args : List LoweredExpr) (T : τ) (m : LoweredExpr) :
    (EctxItem.superCallRecv name slot args T).fill m = .superCall m name slot args T := rfl
public theorem tidy_fill_superCallArgs (v : Value) (name : String) (slot : Option String)
    (vs : List Value) (ms : List LoweredExpr) (T : τ) (m : LoweredExpr) :
    (EctxItem.superCallArgs v name slot vs ms T).fill m =
      .superCall (.val v) name slot (vs.map .val ++ m :: ms) T := rfl
public theorem tidy_fill_superGet (name : String) (slot : Option String) (T : τ)
    (m : LoweredExpr) : (EctxItem.superGet name slot T).fill m = .superGet m name slot T := rfl
public theorem tidy_fill_superSetL (name : String) (slot : Option String) (m₂ m : LoweredExpr) :
    (EctxItem.superSetL name slot m₂).fill m = .superSet m name slot m₂ := rfl
public theorem tidy_fill_superSetR (v₁ : Value) (name : String) (slot : Option String)
    (m : LoweredExpr) :
    (EctxItem.superSetR v₁ name slot).fill m = .superSet (.val v₁) name slot m :=
  rfl
public theorem tidy_fill_checkPromotion (T : τ) (m : LoweredExpr) :
    (EctxItem.checkPromotion T).fill m = .checkPromotion T m := rfl
public theorem tidy_fill_identicalL (m₂ m : LoweredExpr) :
    (EctxItem.identicalL m₂).fill m = .identical m m₂ := rfl
public theorem tidy_fill_identicalR (v₁ : Value) (m : LoweredExpr) :
    (EctxItem.identicalR v₁).fill m = .identical (.val v₁) m := rfl
public theorem tidy_fill_letIn (v : Variable) (m₂ m : LoweredExpr) :
    (EctxItem.letIn v m₂).fill m = .letIn v m m₂ := rfl
public theorem tidy_fill_concat (vs : List Value) (ms : List LoweredExpr) (m : LoweredExpr) :
    (EctxItem.concat vs ms).fill m = .concat (vs.map .val ++ m :: ms) := rfl
public theorem tidy_fill_assertFail (m : LoweredExpr) :
    (EctxItem.assertFail (τ := τ)).fill m = .assertFail (some m) := rfl
public theorem tidy_splitVals_nil : LoweredExpr.splitVals (τ := τ) [] = ([], []) := rfl
public theorem tidy_splitVals_val (v : Value) (ms : List LoweredExpr) :
    LoweredExpr.splitVals (.val v :: ms) =
      (v :: (LoweredExpr.splitVals ms).1, (LoweredExpr.splitVals ms).2) := rfl
public theorem tidy_splitVals_cons {m : LoweredExpr} (ms : List LoweredExpr)
    (h : ∀ v, m ≠ .val v) : LoweredExpr.splitVals (m :: ms) = ([], m :: ms) := by
  cases m <;> first | rfl | exact absurd rfl (h _)

variable [Γ : DartRuntimeTypeRepr τ]

/-! Head steps that `dart_pure_head_step` uses for the arguments of a call. -/

/--
An exception thrown by an argument of a call propagates out of the call: if the arguments split
into values, then throwing `v`, then the rest (`hsplit`), the call steps to throwing `v`.
-/
public theorem HeadStep.bubbleException_call [SemanticParams τ] {f : String}
    {args : List LoweredExpr} {T : τ} {vs : List Value} {v : Value} {ms : List LoweredExpr}
    {σ : State (τ := τ)} (hsplit : LoweredExpr.splitVals args = (vs, .throwing v :: ms)) :
    HeadStep (.call f args T) σ (.throwing v) σ := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  subst h
  exact .bubbleException (Ki := .call f vs ms T)

/--
A return in an argument of a call propagates out of the call: if the arguments split into values,
then returning `v`, then the rest (`hsplit`), the call steps to returning `v`.
-/
public theorem HeadStep.bubbleReturn_call [SemanticParams τ] {f : String}
    {args : List LoweredExpr} {T : τ} {vs : List Value} {v : Value} {ms : List LoweredExpr}
    {σ : State (τ := τ)} (hsplit : LoweredExpr.splitVals args = (vs, .returning v :: ms)) :
    HeadStep (.call f args T) σ (.returning v) σ := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  subst h
  exact .bubbleReturn (Ki := .call f vs ms T) rfl

/--
A break in an argument of a call propagates out of the call: if the arguments split into values,
then breaking out of `l`, then the rest (`hsplit`), the call steps to breaking out of `l`.
-/
public theorem HeadStep.bubbleBreak_call [SemanticParams τ] {f : String}
    {args : List LoweredExpr} {T : τ} {vs : List Value} {l : String} {ms : List LoweredExpr}
    {σ : State (τ := τ)} (hsplit : LoweredExpr.splitVals args = (vs, .breaking l :: ms)) :
    HeadStep (.call f args T) σ (.breaking l) σ := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  subst h
  exact .bubbleBreak (Ki := .call f vs ms T) rfl rfl

/--
An exception thrown by an operand of an expression `F args` with a list of operands (an instance
creation, or the arguments of a call of a constructor or member) propagates out of it: if the
operands split into values, then throwing `v`, then the rest (`hsplit`), and `mk vs ms` is the
context item for that operand (`hmk`), then `F args` steps to throwing `v`.
-/
public theorem HeadStep.bubbleException_args [SemanticParams τ]
    {F : List LoweredExpr → LoweredExpr} {mk : List Value → List LoweredExpr → EctxItem (τ := τ)}
    (hmk : ∀ vs m ms, (mk vs ms).fill m = F (vs.map .val ++ m :: ms)) {args : List LoweredExpr}
    {vs : List Value} {v : Value} {ms : List LoweredExpr} {σ : State (τ := τ)}
    (hsplit : LoweredExpr.splitVals args = (vs, .throwing v :: ms)) :
    HeadStep (F args) σ (.throwing v) σ := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  rw [← h, ← hmk]
  exact .bubbleException

/--
A return in an operand of an expression with a list of operands propagates out of it, as in
`bubbleException_args`, if the context item doesn't handle returns (`hret`).
-/
public theorem HeadStep.bubbleReturn_args [SemanticParams τ]
    {F : List LoweredExpr → LoweredExpr} {mk : List Value → List LoweredExpr → EctxItem (τ := τ)}
    (hmk : ∀ vs m ms, (mk vs ms).fill m = F (vs.map .val ++ m :: ms))
    (hret : ∀ vs ms, (mk vs ms).handlesReturn = false) {args : List LoweredExpr}
    {vs : List Value} {v : Value} {ms : List LoweredExpr} {σ : State (τ := τ)}
    (hsplit : LoweredExpr.splitVals args = (vs, .returning v :: ms)) :
    HeadStep (F args) σ (.returning v) σ := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  rw [← h, ← hmk]
  exact .bubbleReturn (hret _ _)

/--
A break in an operand of an expression with a list of operands propagates out of it, as in
`bubbleException_args`, if the context item doesn't handle breaks (`hbrk`) or returns (`hret`).
-/
public theorem HeadStep.bubbleBreak_args [SemanticParams τ]
    {F : List LoweredExpr → LoweredExpr} {mk : List Value → List LoweredExpr → EctxItem (τ := τ)}
    (hmk : ∀ vs m ms, (mk vs ms).fill m = F (vs.map .val ++ m :: ms))
    (hbrk : ∀ l vs ms, (mk vs ms).handlesBreak l = false)
    (hret : ∀ vs ms, (mk vs ms).handlesReturn = false) {args : List LoweredExpr}
    {vs : List Value} {l : String} {ms : List LoweredExpr} {σ : State (τ := τ)}
    (hsplit : LoweredExpr.splitVals args = (vs, .breaking l :: ms)) :
    HeadStep (F args) σ (.breaking l) σ := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  rw [← h, ← hmk]
  exact .bubbleBreak (hbrk _ _ _) (hret _ _)
variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF] [P : SemanticParams τ]
-- (The type of `Φ` is spelled out because a local notation doesn't work in a `variable` binder; see
-- the same binder in `PrimitiveLaws.lean`.)
variable {s : Stuckness} {E : CoPset} {Φ : DartLang.Outcome (τ := τ) → IProp GF}
variable {Δ : IProp GF}

include hlc

open Iris.ProofMode (Entails')

/-! The proof-mode goal `Δ ⊢ P` is `Entails' Δ P`, so the tactic lemmas are stated with it. -/

/--
The proof-mode form of `wp_val`: to prove that `.val v` satisfies `Φ` from the hypotheses `Δ`, prove
`Φ (.normal v)` (`H`).
-/
public theorem tac_wp_val {v : Value} (H : Entails' Δ (Φ (.normal v))) :
    Entails' Δ (WP (LoweredExpr.val v) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_val v)

/--
The proof-mode form of `wp_throwing`: to prove that `.throwing v` satisfies `Φ` from the hypotheses
`Δ`, prove `Φ (.throwing v)` (`H`).
-/
public theorem tac_wp_throwing {v : Value} (H : Entails' Δ (Φ (.throwing v))) :
    Entails' Δ (WP (LoweredExpr.throwing v) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_throwing v)

/--
The proof-mode form of `wp_pure_step`: to prove that `e₁` satisfies `Φ` from the hypotheses `Δ`,
where `e₁` hasn't completed (`hv`) and in every state takes a head step to `e₂` that leaves the
state unchanged (`h`), prove that `e₂` satisfies `Φ` one step later (`H`).
-/
public theorem tac_wp_pure {e₁ e₂ : LoweredExpr} (hv : e₁.toOutcome? = none)
    (h : ∀ σ, HeadStep e₁ σ e₂ σ) (H : Entails' Δ iprop(▷ WP e₂ @ s; E {{ Φ }})) :
    Entails' Δ (WP e₁ @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_pure_step hv h)

/--
The proof-mode form of `wp_bind_item`, for an evaluation context item `Ki` whose hole holds an
expression `e` that hasn't completed (`_he`): to prove that `Ki.fill e` satisfies `Φ` from the
hypotheses `Δ`, prove that `e` satisfies the postcondition that plugging its outcome `o` back into
`Ki` satisfies `Φ` (`H`).
-/
public theorem tac_wp_bind (Ki : EctxItem (τ := τ)) {e : LoweredExpr} (_he : e.toOutcome? = none)
    (H : Entails' Δ (WP e @ s; E {{ o, WP (Ki.fill o.toExpr) @ s; E {{ Φ }} }})) :
    Entails' Δ (WP (Ki.fill e) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_bind_item Ki)

/--
The proof-mode form of `wp_blockDeclare`: to prove that a block that starts with a declaration of
`v` satisfies `Φ` from the hypotheses `Δ`, prove its premise (`H`).
-/
public theorem tac_wp_blockDeclare {v : Variable} {T : τ} {startsNull : Bool}
    {ms : List LoweredExpr}
    (H : Entails' Δ iprop(▷ (∀ ℓ, ℓ ↦ (if startsNull then .val .null else .uninit : Cell) -∗
        WP (LoweredExpr.block (LoweredExpr.resolveBlock v ℓ ms)) @ s; E {{ Φ }}))) :
    Entails' Δ (WP (LoweredExpr.block (.declare v T startsNull :: ms)) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_blockDeclare

/--
The proof-mode form of `wp_blockExpr_declare`: to prove that a block with a value whose statements
start with a declaration of `v` satisfies `Φ` from the hypotheses `Δ`, prove its premise (`H`).
-/
public theorem tac_wp_blockExpr_declare {v : Variable} {T : τ} {startsNull : Bool}
    {ms : List LoweredExpr} {m : LoweredExpr}
    (H : Entails' Δ iprop(▷ (∀ ℓ, ℓ ↦ (if startsNull then .val .null else .uninit : Cell) -∗
        WP ((LoweredExpr.blockExpr ms m).resolve v ℓ) @ s; E {{ Φ }}))) :
    Entails' Δ (WP (LoweredExpr.blockExpr (.declare v T startsNull :: ms) m) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_blockExpr_declare

/--
The proof-mode form of `wp_letIn`: to prove that a let expression whose initializer has evaluated
to `w` satisfies `Φ` from the hypotheses `Δ`, prove its premise (`H`).
-/
public theorem tac_wp_letIn {v : Variable} {w : Value} {m₂ : LoweredExpr}
    (H : Entails' Δ iprop(▷ (∀ ℓ, ℓ ↦ (.val w : Cell) -∗ WP (m₂.resolve v ℓ) @ s; E {{ Φ }}))) :
    Entails' Δ (WP (LoweredExpr.letIn v (.val w) m₂) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_letIn

/--
The proof-mode form of `wp_varAt`, with the subtype fact as a pure premise (`⌜S ≤ T⌝`), after the
dynamic type: to prove that reading `x`, resolved to the cell at `ℓ`, satisfies `Φ` from the
hypotheses `Δ`, prove `wp_varAt`'s premises (`H`).
-/
public theorem tac_wp_load {x : Variable} {T S : τ} {ℓ : Loc} {dq : DFrac} {v : Value}
    (H : Entails' Δ iprop(HasDynamicType v S ∗ ⌜S ≤ T⌝ ∗ ▷ (ℓ ↦{dq} (.val v : Cell)) ∗
        ▷ ((ℓ ↦{dq} (.val v : Cell)) -∗ Φ (.normal v)))) :
    Entails' Δ (WP (LoweredExpr.varAt x T ℓ) @ s; E {{ Φ }}) := by
  refine (show Δ ⊢ _ from H).trans ?_
  iintro ⟨#Hty, %hST, Hl, HΦ⟩
  iapply wp_varAt hST
  isplitr
  · iexact Hty
  isplitl [Hl]
  · iexact Hl
  · iexact HΦ

/--
The proof-mode form of `wp_propertyGet_field`, with its pure facts as premises
(`⌜P.dispatch k p.name = some (.field iv)⌝` and `⌜fs.lookup iv = some ℓf⌝`, after the object's own
cell, and `⌜S ≤ T⌝`, after the dynamic type): to prove that reading property `p` of the object at
`ℓ` satisfies `Φ` from the hypotheses `Δ`, prove `wp_propertyGet_field`'s premises (`H`).
-/
public theorem tac_wp_load_field {ℓ ℓf : Loc} {p : Property} {k iv : String} {T C S : τ}
    {fs : List (String × Loc)} {dq : DFrac} {w : Value}
    (H : Entails' Δ iprop(ℓ ↦{.discard} (.object k C fs : Cell) ∗
        ⌜P.dispatch k p.name = some (.field iv)⌝ ∗ ⌜fs.lookup iv = some ℓf⌝ ∗
        HasDynamicType w S ∗ ⌜S ≤ T⌝ ∗ ▷ (ℓf ↦{dq} (.val w : Cell)) ∗
        ▷ ((ℓf ↦{dq} (.val w : Cell)) -∗ Φ (.normal w)))) :
    Entails' Δ (WP (LoweredExpr.propertyGet (.val (.obj ℓ)) p T) @ s; E {{ Φ }}) := by
  refine (show Δ ⊢ _ from H).trans ?_
  iintro ⟨#Hobj, %hd, %hf, #Hty, %hST, Hl, HΦ⟩
  iapply wp_propertyGet_field hd hf hST
  isplitr
  · iexact Hobj
  isplitr
  · iexact Hty
  isplitl [Hl]
  · iexact Hl
  · iexact HΦ

/--
The proof-mode form of `wp_variableSetAt`, with the points-to first (`H`), so that framing it
determines the cell, and then the facts that the cell isn't an object's own cell (`hc`) and, if
`x` is `final`, is unassigned (`hfin`): to prove that assigning `w` to `x`, resolved to the cell at
`ℓ`, satisfies `Φ` from the hypotheses `Δ`, prove `wp_variableSetAt`'s premises.
-/
public theorem tac_wp_store {x : Variable} {ℓ : Loc} {c : Cell} {w : Value}
    (H : Entails' Δ iprop(▷ (ℓ ↦ c) ∗ ▷ ((ℓ ↦ (.val w : Cell)) -∗ Φ (.normal w))))
    (hc : c.isVar = true) (hfin : x.isFinal = true → c = .uninit) :
    Entails' Δ (WP (LoweredExpr.variableSetAt x ℓ (.val w)) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_variableSetAt hc hfin)

/--
The proof-mode form of `wp_value` for an expression that is returning `v`: to prove that
`.returning v` satisfies `Φ` from the hypotheses `Δ`, prove `Φ (.returning v)` (`H`).
-/
public theorem tac_wp_returning {v : Value} (H : Entails' Δ (Φ (.returning v))) :
    Entails' Δ (WP (LoweredExpr.returning v) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_value' (v := DartLang.Outcome.returning v))

/--
The proof-mode form of `wp_bind_item` for the argument of a call in evaluation position: if the
arguments split into values `vs`, then an argument `m` that hasn't completed, then the rest `ms`
(`hsplit` and `_hm`), then to prove that the call satisfies `Φ` from the hypotheses `Δ`, prove
that `m` satisfies the postcondition that plugging its outcome `o` back into the call satisfies
`Φ` (`H`). (`wp_bind` finds the split by computing `LoweredExpr.splitVals`.)
-/
public theorem tac_wp_bind_call {f : String} {args : List LoweredExpr} {T : τ} {vs : List Value}
    {m : LoweredExpr} {ms : List LoweredExpr} (hsplit : LoweredExpr.splitVals args = (vs, m :: ms))
    (_hm : m.toOutcome? = none)
    (H : Entails' Δ (WP m @ s; E {{ o, WP ((EctxItem.call f vs ms T).fill o.toExpr) @ s; E
      {{ Φ }} }})) :
    Entails' Δ (WP (LoweredExpr.call f args T) @ s; E {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  subst h
  exact (show Δ ⊢ _ from H).trans (wp_bind_item (.call f vs ms T))

/--
The proof-mode form of `wp_call`, for a call whose arguments are all values `vs` (`hsplit`): to
prove that it satisfies `Φ` from the hypotheses `Δ`, where the function table declares `f` as `d`
(`hf`) with one formal parameter per argument (`hlen`), prove `wp_call`'s premise (`H`).
-/
public theorem tac_wp_call {f : String} {args : List LoweredExpr} {T : τ} {vs : List Value}
    {d : FunctionDecl (τ := τ)} (hsplit : LoweredExpr.splitVals args = (vs, []))
    (hf : P.functions f = some d) (hlen : d.params.length = vs.length)
    (H : Entails' Δ iprop(▷ (∀ ℓs, PointsToVals ℓs vs -∗
        WP (LoweredExpr.frame ((d.body.withIntMode (P.intModeOf f)).bindVariables
          (d.params.zip ℓs)) T) @ s; E {{ Φ }}))) :
    Entails' Δ (WP (LoweredExpr.call f args T) @ s; E {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit, List.append_nil] at h
  subst h
  exact (show Δ ⊢ _ from H).trans (wp_call hf hlen)

/--
The proof-mode form of `FunSpec.wp_call`, for a call whose arguments are all values `vs`
(`hsplit`): to prove that it satisfies `Φ` from the hypotheses `Δ`, prove that `f` meets a
specification, its precondition holds, and its postcondition implies `Φ` (`H`).
-/
public theorem tac_wp_call_spec {f : String} {args : List LoweredExpr} {T : τ} {vs : List Value}
    {Pre : List Value → IProp GF} {Post : List Value → DartLang.Outcome (τ := τ) → IProp GF}
    {Φ : DartLang.Outcome (τ := τ) → IProp GF} (hsplit : LoweredExpr.splitVals args = (vs, []))
    (H : Entails' Δ iprop(FunSpec f Pre Post ∗ Pre vs ∗ ∀ o, Post vs o -∗ Φ o)) :
    Entails' Δ (WP (LoweredExpr.call f args T) {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit, List.append_nil] at h
  subst h
  exact (show Δ ⊢ _ from H).trans FunSpec.wp_call

/--
The proof-mode form of `wp_frame`: to prove that the body `m` of a running call satisfies `Φ` from
the hypotheses `Δ`, prove that `m` satisfies the postcondition that `Φ` holds, one step later, of
the call's outcome (`H`; see `framePost`).
-/
public theorem tac_wp_frame {m : LoweredExpr} {T : τ}
    (H : Entails' Δ (WP m @ s; E {{ o, framePost Φ o }})) :
    Entails' Δ (WP (LoweredExpr.frame m T) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_frame

/--
The proof-mode form of `wp_value` for an expression that is breaking out of labeled statement `l`:
to prove that `.breaking l` satisfies `Φ` from the hypotheses `Δ`, prove `Φ (.breaking l)` (`H`).
-/
public theorem tac_wp_breaking {l : String} (H : Entails' Δ (Φ (.breaking l))) :
    Entails' Δ (WP (LoweredExpr.breaking (τ := τ) l) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_value' (v := DartLang.Outcome.breaking l))

/--
The proof-mode form of `wp_labeled`: to prove that the labeled statement `l` with body `m`
satisfies `Φ` from the hypotheses `Δ`, prove that `m` satisfies the postcondition that `Φ` holds,
one step later, of the labeled statement's outcome (`H`; see `labeledPost`).
-/
public theorem tac_wp_labeled {l : String} {m : LoweredExpr}
    (H : Entails' Δ (WP m @ s; E {{ o, labeledPost l Φ o }})) :
    Entails' Δ (WP (LoweredExpr.labeled l m) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_labeled

/--
The proof-mode form of `wp_loop_inv`: to prove that a loop with body `m` satisfies `Φ` from the
hypotheses `Δ`, given an invariant `I`, prove that `Δ` gives `I` (`HI`), and that `I` makes the
body satisfy the postcondition that gives `I` back when it completes normally, and `Φ` otherwise
(`H`; see `loopInvPost`).
-/
public theorem tac_wp_loop_inv {m : LoweredExpr} (I : IProp GF) (HI : Entails' Δ I)
    (H : I ⊢ WP m @ s; E {{ o, loopInvPost I Φ o }}) :
    Entails' Δ (WP (LoweredExpr.loop m) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from HI).trans (wp_loop_inv I H)

/--
The proof-mode form of `wp_intBin`: to prove that a binary operator on integers `n₁` and `n₂`, in
integer mode `mode`, satisfies `Φ` from the hypotheses `Δ`, where its result is `v` (`h`), prove
that `Φ` holds of `v` one step later (`H`).
-/
public theorem tac_wp_intBin {op : IntBinOp} {mode : IntMode} {n₁ n₂ : Int} {v : Value}
    (h : op.eval mode n₁ n₂ = some v) (H : Entails' Δ iprop(▷ Φ (.normal v))) :
    Entails' Δ (WP (LoweredExpr.intBin (τ := τ) op (some mode) (.val (.int n₁)) (.val (.int n₂))) @
      s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_intBin h)

/--
`tac_wp_intBin` for an arithmetic operator in mode `checked`: to prove that it satisfies `Φ` from
the hypotheses `Δ`, where its exact result is `n` (`hn`, its result in mode `unbounded`), prove
that `n` is in 64-bit range (`hr`), and that `Φ` holds of `n` one step later (`H`).
-/
public theorem tac_wp_intBin_checked {op : IntBinOp} {n₁ n₂ n : Int}
    (hn : op.eval (τ := τ) .unbounded n₁ n₂ = some (.int n)) (hr : -2 ^ 63 ≤ n ∧ n < 2 ^ 63)
    (H : Entails' Δ iprop(▷ Φ (.normal (.int n)))) :
    Entails' Δ (WP (LoweredExpr.intBin (τ := τ) op (some .checked) (.val (.int n₁))
      (.val (.int n₂))) @ s; E {{ Φ }}) :=
  tac_wp_intBin (IntBinOp.eval_checked_of_range hn hr) H

/--
The proof-mode form of `wp_bind_item` for an operand in evaluation position of an expression
`F args` with a list of operands (an instance creation, or the arguments of a call of a constructor
or member): if the operands split into values `vs`, then an operand `m` that hasn't completed, then
the rest `ms` (`hsplit` and `_hm`), and `mk vs ms` is the context item for `m` (`hmk`), then to
prove that `F args` satisfies `Φ` from the hypotheses `Δ`, prove that `m` satisfies the
postcondition that plugging its outcome `o` back into the item satisfies `Φ` (`H`).
-/
public theorem tac_wp_bind_args {F : List LoweredExpr → LoweredExpr}
    {mk : List Value → List LoweredExpr → EctxItem (τ := τ)}
    (hmk : ∀ vs m ms, (mk vs ms).fill m = F (vs.map .val ++ m :: ms)) {args : List LoweredExpr}
    {vs : List Value} {m : LoweredExpr} {ms : List LoweredExpr}
    (hsplit : LoweredExpr.splitVals args = (vs, m :: ms)) (_hm : m.toOutcome? = none)
    (H : Entails' Δ (WP m @ s; E {{ o, WP ((mk vs ms).fill o.toExpr) @ s; E {{ Φ }} }})) :
    Entails' Δ (WP (F args) @ s; E {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  rw [← h, ← hmk]
  exact (show Δ ⊢ _ from H).trans (wp_bind_item (mk vs ms))

/--
The proof-mode form of `wp_new`, for an instance creation whose arguments are all values `vs`
(`hsplit`): to prove that it satisfies `Φ` from the hypotheses `Δ`, where the constructor table
declares `k` as `d` (`hk`) and the class table declares its class as `c` (`hc`), prove `wp_new`'s
premise (`H`).
-/
public theorem tac_wp_new {k : String} {args : List LoweredExpr} {T : τ} {vs : List Value}
    {d : ConstructorDecl (τ := τ)} {c : ClassDecl (τ := τ)}
    (hsplit : LoweredExpr.splitVals args = (vs, [])) (hk : P.constructors k = some d)
    (hc : P.classes d.cls = some c)
    (H : Entails' Δ iprop(▷ (∀ ℓ ℓs, ⌜ℓs.length = c.instanceVariables.length⌝ -∗
        ℓ ↦{.discard} (.object d.cls c.type (c.instanceVariables.zip ℓs) : Cell) -∗
        PointsToUninit (τ := τ) ℓs -∗
        WP (LoweredExpr.seq (.ctorRun ℓ k vs) (.val (.obj ℓ))) @ s; E {{ Φ }}))) :
    Entails' Δ (WP (LoweredExpr.new k args T) @ s; E {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit, List.append_nil] at h
  subst h
  exact (show Δ ⊢ _ from H).trans (wp_new hk hc)

/--
The proof-mode form of `wp_ctorRun`: to prove that running constructor `k` on the object at `ℓ`
satisfies `Φ` from the hypotheses `Δ`, where the constructor table declares `k` as `d` (`hk`) with
one formal parameter per argument (`hlen`), prove `wp_ctorRun`'s premise (`H`).
-/
public theorem tac_wp_ctorRun {ℓ : Loc} {k : String} {d : ConstructorDecl (τ := τ)}
    {vs : List Value} (hk : P.constructors k = some d) (hlen : d.params.length = vs.length)
    (H : Entails' Δ iprop(▷ (∀ ℓs, PointsToVals ℓs (.obj ℓ :: vs) -∗
        WP (LoweredExpr.ctorFrame (P.memberBody k d.cls (d.this :: d.params)
          (.block (d.initializers ++ [d.body])) ℓs)) @ s; E {{ Φ }}))) :
    Entails' Δ (WP (LoweredExpr.ctorRun ℓ k vs) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_ctorRun hk hlen)

/--
The proof-mode form of `wp_ctorFrame`: to prove that the initializers and body `m` of a running
constructor satisfy `Φ` from the hypotheses `Δ`, prove that `m` satisfies the postcondition that
`Φ` holds, one step later, of the constructor's outcome (`H`; see `ctorFramePost`).
-/
public theorem tac_wp_ctorFrame {m : LoweredExpr}
    (H : Entails' Δ (WP m @ s; E {{ o, ctorFramePost Φ o }})) :
    Entails' Δ (WP (LoweredExpr.ctorFrame m) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_ctorFrame

/--
The proof-mode form of `wp_methodCall`, for a method call on the object at `ℓ` whose arguments are
all values `vs` (`hsplit`): to prove that it satisfies `Φ` from the hypotheses `Δ`, where the
object's class `k` dispatches the method's name to member `key`, provided by `holder` (`hd`),
declared as `d` (`hm`) with one formal parameter per argument (`hlen`), prove `wp_methodCall`'s
premises (`H`).
-/
public theorem tac_wp_methodCall {ℓ : Loc} {name k key holder : String} {C : τ}
    {fs : List (String × Loc)} {d : MemberDecl (τ := τ)} {args : List LoweredExpr}
    {vs : List Value} {T : τ} (hsplit : LoweredExpr.splitVals args = (vs, []))
    (hd : P.dispatch k name = some (.proc key holder)) (hm : P.members key = some d)
    (hlen : d.params.length = vs.length)
    (H : Entails' Δ iprop(ℓ ↦{.discard} (.object k C fs : Cell) ∗
        ▷ (∀ ℓs, PointsToVals ℓs (.obj ℓ :: vs) -∗
          WP (LoweredExpr.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs) T) @ s;
            E {{ Φ }}))) :
    Entails' Δ (WP (LoweredExpr.methodCall (.val (.obj ℓ)) name args T) @ s; E {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit, List.append_nil] at h
  subst h
  exact (show Δ ⊢ _ from H).trans (wp_methodCall hd hm hlen)

/--
The proof-mode form of `MemberSpec.wp_methodCall`, for a method call on the object at `ℓ` whose
arguments are all values `vs` (`hsplit`), where the object's class `k` dispatches the method's name
to member `key`, provided by `holder` (`hd`), declared as `d` (`hm`) with one formal parameter per
argument (`hlen`): to prove that it satisfies `Φ` from the hypotheses `Δ`, prove the object's
header, a specification of `key` (one step later), its precondition, and that its postcondition
implies `Φ` (`H`).
-/
public theorem tac_wp_method_spec {ℓ : Loc} {name k key holder : String} {C : τ}
    {fs : List (String × Loc)} {d : MemberDecl (τ := τ)} {args : List LoweredExpr}
    {vs : List Value} {T : τ} {Pre : List Value → IProp GF}
    {Post : List Value → DartLang.Outcome (τ := τ) → IProp GF}
    {Φ : DartLang.Outcome (τ := τ) → IProp GF} (hsplit : LoweredExpr.splitVals args = (vs, []))
    (hd : P.dispatch k name = some (.proc key holder)) (hm : P.members key = some d)
    (hlen : d.params.length = vs.length)
    (H : Entails' Δ iprop(ℓ ↦{.discard} (.object k C fs : Cell) ∗
        ▷ MemberSpec key holder Pre Post ∗ Pre (.obj ℓ :: vs) ∗
        ▷ (∀ o, Post (.obj ℓ :: vs) o -∗ Φ o))) :
    Entails' Δ (WP (LoweredExpr.methodCall (.val (.obj ℓ)) name args T) {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit, List.append_nil] at h
  subst h
  exact (show Δ ⊢ _ from H).trans (MemberSpec.wp_methodCall hd hm hlen)

/--
The proof-mode form of `wp_constant_string`: to prove that a string constant with code units `cu`
satisfies `Φ` from the hypotheses `Δ`, prove `wp_constant_string`'s premise (`H`).
-/
public theorem tac_wp_constant_string {cu : List UInt16}
    (H : Entails' Δ iprop(▷ (∀ ℓ, ℓ ↦{.discard} (.string cu : Cell) -∗
        IsConst τ (.string cu) ℓ -∗ Φ (.normal (.obj ℓ))))) :
    Entails' Δ (WP (LoweredExpr.constant (τ := τ) (.string cu)) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_constant_string

/--
The proof-mode form of `wp_concat`, for a string concatenation whose parts are all values `vs`
(`hsplit`): to prove that it satisfies `Φ` from the hypotheses `Δ`, prove `wp_concat`'s premises
(`H`).
-/
public theorem tac_wp_concat {args : List LoweredExpr} {vs : List Value}
    {cus : List (List UInt16)} (hsplit : LoweredExpr.splitVals args = (vs, []))
    (H : Entails' Δ iprop(StringParts vs cus ∗
        ▷ (∀ ℓ, ℓ ↦{.discard} (.string cus.flatten : Cell) -∗ Fresh τ ℓ -∗
          Φ (.normal (.obj ℓ))))) :
    Entails' Δ (WP (LoweredExpr.concat args) @ s; E {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit, List.append_nil] at h
  subst h
  exact (show Δ ⊢ _ from H).trans wp_concat

end DartSemantics

/--
Take a head step that doesn't depend on, or change, the state (for `wp_pure`). Running a loop
(`HeadStep.loop`) isn't one of them: `wp_pures` would unroll it forever. Use the loop invariant rule
(`wp_loop_inv`), or `wp_loop_step` to unroll one iteration.
-/
syntax "dart_pure_head_step" : tactic

macro_rules
  | `(tactic| dart_pure_head_step) => `(tactic| first
    | exact DartSemantics.HeadStep.null
    | exact DartSemantics.HeadStep.bool
    | exact DartSemantics.HeadStep.int
    | exact DartSemantics.HeadStep.declare
    | exact DartSemantics.HeadStep.blockNil
    | (refine DartSemantics.HeadStep.blockCons ?_; intro _ _ _ h; cases h)
    | exact DartSemantics.HeadStep.blockExprNil
    | (refine DartSemantics.HeadStep.blockExprCons ?_; intro _ _ _ h; cases h)
    | exact DartSemantics.HeadStep.seq
    | exact DartSemantics.HeadStep.nullCheckNull
    | (refine DartSemantics.HeadStep.nullCheck ?_; intro h; cases h)
    | exact DartSemantics.HeadStep.condTrue
    | exact DartSemantics.HeadStep.condFalse
    | exact DartSemantics.HeadStep.bubbleException (Ki := .nullCheck)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .as _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .is _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .cond _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .propertyGet _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .seq _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .variableSetAt _ _)
    | exact DartSemantics.HeadStep.ret
    | exact DartSemantics.HeadStep.frameReturning
    | exact DartSemantics.HeadStep.frameVal
    | exact DartSemantics.HeadStep.checkPass rfl
    | exact DartSemantics.HeadStep.checkFail rfl
    | exact DartSemantics.HeadStep.checkEqPass rfl
    | exact DartSemantics.HeadStep.checkEqFail rfl
    | exact DartSemantics.HeadStep.bubbleException (Ki := .ret)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .frame _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .check _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .checkEqL _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .checkEqR _)
    | exact DartSemantics.HeadStep.bubbleException_call rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .nullCheck) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .as _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .is _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .cond _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .propertyGet _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .seq _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .variableSetAt _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .ret) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .check _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .checkEqL _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .checkEqR _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn_call rfl
    | exact DartSemantics.HeadStep.labeledVal
    | exact DartSemantics.HeadStep.labeledBreak
    | exact DartSemantics.HeadStep.brk
    | exact DartSemantics.HeadStep.intBin rfl
    | exact DartSemantics.HeadStep.intNeg rfl
    | exact DartSemantics.HeadStep.primEq rfl
    | exact DartSemantics.HeadStep.bubbleException (Ki := .labeled _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .intBinL _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .intBinR _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .intNeg _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .primEqL _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .primEqR _)
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .labeled _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .intBinL _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .intBinR _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .intNeg _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .primEqL _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .primEqR _) rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .nullCheck) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .as _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .is _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .cond _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .propertyGet _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .seq _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .variableSetAt _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .ret) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .check _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .checkEqL _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .checkEqR _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .labeled _) (by decide) rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .intBinL _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .intBinR _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .intNeg _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .primEqL _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .primEqR _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak_call rfl
    | exact DartSemantics.HeadStep.initCtor
    | exact DartSemantics.HeadStep.ctorFrameVal
    | exact DartSemantics.HeadStep.ctorFrameReturning
    | exact DartSemantics.HeadStep.identical rfl
    | exact DartSemantics.HeadStep.bubbleException (Ki := .initCtorRecv _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .initFieldL _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .initFieldR _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .propertySetL _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .propertySetR _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .ctorFrame)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .methodCallRecv _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .superCallRecv _ _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .superGet _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .superSetL _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .superSetR _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .checkPromotion _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .identicalL _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .identicalR _)
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .initCtorRecv _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .initFieldL _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .initFieldR _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .propertySetL _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .propertySetR _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .methodCallRecv _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .superCallRecv _ _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .superGet _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .superSetL _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .superSetR _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .checkPromotion _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .identicalL _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .identicalR _) rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .initCtorRecv _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .initFieldL _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .initFieldR _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .propertySetL _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .propertySetR _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .methodCallRecv _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .superCallRecv _ _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .superGet _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .superSetL _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .superSetR _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .checkPromotion _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .identicalL _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .identicalR _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleException (Ki := .letIn _ _)
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .letIn _ _) rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .letIn _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleException_args (F := (.new _ · _)) (mk := (.new _ · · _))
        (fun _ _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleException_args (F := (.initCtor (.val _) _ ·))
        (mk := (.initCtorArgs _ _ · ·)) (fun _ _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleException_args (F := (.methodCall (.val _) _ · _))
        (mk := (.methodCallArgs _ _ · · _)) (fun _ _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleException_args (F := (.superCall (.val _) _ _ · _))
        (mk := (.superCallArgs _ _ _ · · _)) (fun _ _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleReturn_args (F := (.new _ · _)) (mk := (.new _ · · _))
        (fun _ _ _ => rfl) (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleReturn_args (F := (.initCtor (.val _) _ ·))
        (mk := (.initCtorArgs _ _ · ·)) (fun _ _ _ => rfl) (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleReturn_args (F := (.methodCall (.val _) _ · _))
        (mk := (.methodCallArgs _ _ · · _)) (fun _ _ _ => rfl) (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleReturn_args (F := (.superCall (.val _) _ _ · _))
        (mk := (.superCallArgs _ _ _ · · _)) (fun _ _ _ => rfl) (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleBreak_args (F := (.new _ · _)) (mk := (.new _ · · _))
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleBreak_args (F := (.initCtor (.val _) _ ·))
        (mk := (.initCtorArgs _ _ · ·)) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleBreak_args (F := (.methodCall (.val _) _ · _))
        (mk := (.methodCallArgs _ _ · · _)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleBreak_args (F := (.superCall (.val _) _ _ · _))
        (mk := (.superCallArgs _ _ _ · · _)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.constant rfl
    | exact DartSemantics.HeadStep.bubbleException_args (F := (.concat ·)) (mk := (.concat · ·))
        (fun _ _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleReturn_args (F := (.concat ·)) (mk := (.concat · ·))
        (fun _ _ _ => rfl) (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.bubbleBreak_args (F := (.concat ·)) (mk := (.concat · ·))
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) rfl
    | exact DartSemantics.HeadStep.assertFailNone
    | exact DartSemantics.HeadStep.assertFailSome
    | exact DartSemantics.HeadStep.bubbleException (Ki := .assertFail)
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .assertFail) rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .assertFail) rfl rfl
    -- Whether assertions are checked comes from a hypothesis in the Lean context.
    | exact DartSemantics.HeadStep.assertDisabled ‹_›
    | exact DartSemantics.HeadStep.assertEnabled ‹_›)

/--
Tidy the goal after a step: reduce `Outcome.toExpr`, `EctxItem.fill`, `framePost`, `labeledPost`
and `loopInvPost`, the list operations that plugging into a call's arguments leaves, and
beta-reduce postconditions.
-/
syntax "dart_wp_tidy" : tactic

macro_rules
  | `(tactic| dart_wp_tidy) =>
    `(tactic| try simp only [DartSemantics.tidy_toExpr_normal,
      DartSemantics.tidy_toExpr_throwing, DartSemantics.tidy_toExpr_returning,
      DartSemantics.tidy_toExpr_breaking,
      DartSemantics.tidy_fill_nullCheck, DartSemantics.tidy_fill_as, DartSemantics.tidy_fill_is,
      DartSemantics.tidy_fill_cond, DartSemantics.tidy_fill_propertyGet,
      DartSemantics.tidy_fill_seq, DartSemantics.tidy_fill_variableSetAt,
      DartSemantics.tidy_fill_call, DartSemantics.tidy_fill_ret, DartSemantics.tidy_fill_frame,
      DartSemantics.tidy_fill_check, DartSemantics.tidy_fill_checkEqL,
      DartSemantics.tidy_fill_checkEqR, DartSemantics.tidy_fill_labeled,
      DartSemantics.tidy_fill_intBinL, DartSemantics.tidy_fill_intBinR,
      DartSemantics.tidy_fill_intNeg, DartSemantics.tidy_fill_primEqL,
      DartSemantics.tidy_fill_primEqR, DartSemantics.tidy_fill_new,
      DartSemantics.tidy_fill_initCtorRecv, DartSemantics.tidy_fill_initCtorArgs,
      DartSemantics.tidy_fill_initFieldL, DartSemantics.tidy_fill_initFieldR,
      DartSemantics.tidy_fill_propertySetL, DartSemantics.tidy_fill_propertySetR,
      DartSemantics.tidy_fill_ctorFrame, DartSemantics.tidy_fill_methodCallRecv,
      DartSemantics.tidy_fill_methodCallArgs, DartSemantics.tidy_fill_superCallRecv,
      DartSemantics.tidy_fill_superCallArgs, DartSemantics.tidy_fill_superGet,
      DartSemantics.tidy_fill_superSetL, DartSemantics.tidy_fill_superSetR,
      DartSemantics.tidy_fill_checkPromotion, DartSemantics.tidy_fill_identicalL,
      DartSemantics.tidy_fill_identicalR, DartSemantics.tidy_fill_letIn,
      DartSemantics.tidy_fill_concat, DartSemantics.tidy_fill_assertFail,
      DartSemantics.tidy_splitVals_nil,
      DartSemantics.tidy_splitVals_val, DartSemantics.tidy_splitVals_cons, ne_eq, reduceCtorEq,
      not_false_eq_true, implies_true,
      DartSemantics.ctorFramePost,
      DartSemantics.framePost, DartSemantics.labeledPost,
      DartSemantics.loopInvPost, ite_true, ite_false, ↓reduceIte, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append])

/--
When the expression has completed, replace its weakest precondition with the postcondition applied
to its outcome.
-/
syntax "wp_value" : tactic

macro_rules
  | `(tactic| wp_value) => `(tactic|
    ((first
      | refine DartSemantics.tac_wp_val ?_
      | refine DartSemantics.tac_wp_throwing ?_
      | refine DartSemantics.tac_wp_returning ?_
      | refine DartSemantics.tac_wp_breaking ?_); dart_wp_tidy))

/-- Take one head step that doesn't depend on, or change, the state. -/
syntax "wp_pure" : tactic

macro_rules
  | `(tactic| wp_pure) => `(tactic|
    (apply DartSemantics.tac_wp_pure
     · rfl
     · intro _
       dart_pure_head_step
     inext
     dart_wp_tidy))

/-- Focus on the subexpression in evaluation position, if it hasn't completed. -/
syntax "wp_bind" : tactic

macro_rules
  | `(tactic| wp_bind) => `(tactic|
    ((first
      | refine DartSemantics.tac_wp_bind .nullCheck (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.as _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.is _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.cond _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.propertyGet _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.seq _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.variableSetAt _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind .ret (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.frame _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.check _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.checkEqL _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.checkEqR _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.labeled _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.intBinL _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.intBinR _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.intNeg _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.primEqL _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.primEqR _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind_call (by rfl) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.initCtorRecv _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.initFieldL _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.initFieldR _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.propertySetL _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.propertySetR _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind .ctorFrame (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.methodCallRecv _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.superCallRecv _ _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.superGet _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.superSetL _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.superSetR _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.checkPromotion _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.identicalL _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.identicalR _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.letIn _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind .assertFail (by rfl) ?_
      | refine DartSemantics.tac_wp_bind_args (F := (.new _ · _)) (mk := (.new _ · · _))
          (fun _ _ _ => rfl) (by rfl) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind_args (F := (.initCtor (.val _) _ ·))
          (mk := (.initCtorArgs _ _ · ·)) (fun _ _ _ => rfl) (by rfl) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind_args (F := (.methodCall (.val _) _ · _))
          (mk := (.methodCallArgs _ _ · · _)) (fun _ _ _ => rfl) (by rfl) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind_args (F := (.superCall (.val _) _ _ · _))
          (mk := (.superCallArgs _ _ _ · · _)) (fun _ _ _ => rfl) (by rfl) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind_args (F := (.concat ·)) (mk := (.concat · ·))
          (fun _ _ _ => rfl) (by rfl) (by rfl) ?_);
      dart_wp_tidy))

/--
Step into the body of a running call (`frame`), the initializers and body of a running constructor
(`ctorFrame`), or the body of a labeled statement (`labeled`), which hasn't completed: the goal
becomes a weakest precondition of the body, whose postcondition is that the goal's postcondition
holds, one step later, of the outcome of the call, constructor or labeled statement
(`tac_wp_frame`, `tac_wp_ctorFrame` and `tac_wp_labeled`, with `framePost`, `ctorFramePost` and
`labeledPost` unfolded). `apply`, unlike `refine`, elaborates the lemma before unifying its
conclusion with the goal, so the type representation `τ` is inferred from the goal.
-/
syntax "dart_wp_enter" : tactic

macro_rules
  | `(tactic| dart_wp_enter) => `(tactic|
    ((first
      | apply DartSemantics.tac_wp_frame
      | apply DartSemantics.tac_wp_ctorFrame
      | apply DartSemantics.tac_wp_labeled); dart_wp_tidy))

/--
Take every step that doesn't involve the state: repeat `wp_value`, `wp_pure`, `dart_wp_enter` and
`wp_bind` until none applies. When a body that `dart_wp_enter` stepped into completes, the goal is
the postcondition one step later (`▷`); `inext` then removes the `▷`, so that the steps after the
call, constructor or labeled statement can be taken too.
-/
syntax "wp_pures" : tactic

macro_rules
  | `(tactic| wp_pures) => `(tactic|
    (dart_wp_tidy
     repeat (first | wp_value | wp_pure | dart_wp_enter | wp_bind | inext)))

/--
`wp_alloc ℓ H` takes the step of a declaration at the start of a block (or of the statements of a
block with a value), introducing the new cell `ℓ` and its points-to `H`, and resolves the declared
variable in the rest of the block (and in the value, unless a later statement redeclares it).
-/
syntax "wp_alloc " ident ppSpace ident : tactic

macro_rules
  | `(tactic| wp_alloc $l $h) => `(tactic|
    ((first
       | refine DartSemantics.tac_wp_blockDeclare ?_
       | refine DartSemantics.tac_wp_blockExpr_declare ?_)
     inext
     iintro %$l $h:ident
     simp (config := { decide := true }) only [DartLang.LoweredExpr.resolveBlock,
       DartLang.LoweredExpr.resolve, DartLang.LoweredExpr.declaresVar, List.any_cons,
       List.any_nil, Bool.or_false, Bool.false_or, ite_true, ite_false, Bool.false_eq_true,
       ↓reduceIte]))

/--
`wp_let ℓ H` takes the step of a let expression whose initializer has evaluated, introducing the
new cell `ℓ` of its variable and the cell's points-to `H`, and resolves the variable in the let
expression's body.
-/
syntax "wp_let " ident ppSpace ident : tactic

macro_rules
  | `(tactic| wp_let $l $h) => `(tactic|
    (refine DartSemantics.tac_wp_letIn ?_
     inext
     iintro %$l $h:ident
     simp (config := { decide := true }) only [DartLang.LoweredExpr.resolveBlock,
       DartLang.LoweredExpr.resolve, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte]))

/-- Prove that a value has a dynamic type: the null object, a boolean, an integer, an object whose
header (a persistent points-to for its own cell) is in the context, or a value with a
`HasDynamicType` hypothesis in the context. -/
syntax "dart_dynamic_type" : tactic

macro_rules
  | `(tactic| dart_dynamic_type) => `(tactic| first
    | iapply DartSemantics.HasDynamicType.null
    | iapply DartSemantics.HasDynamicType.bool
    | iapply DartSemantics.HasDynamicType.int
    | (iapply DartSemantics.HasDynamicType.obj; iassumption)
    | iassumption)

/--
Prove a pure side condition of a load: a subtype fact, or the lookup of an instance variable. If
neither `decide` nor `rfl` proves it (for example, a subtype fact about types that aren't
concrete), it's left as a goal, after the remaining goals.
-/
syntax "dart_load_side_condition" : tactic

macro_rules
  | `(tactic| dart_load_side_condition) =>
    `(tactic| (ipureintro; first | decide | rfl | rotate_left))

/--
Prove the dispatch side condition of a load of an instance variable: that the object's class
dispatches the property's name to the implicit getter of some instance variable. A hypothesis in
the Lean context saying so (`assumption`) also determines which instance variable it is. If
neither `decide`, `rfl` nor `assumption` proves it, it's left as a goal, after the remaining
goals; then so is the instance variable's lookup, which depends on it.
-/
syntax "dart_dispatch_side_condition" : tactic

macro_rules
  | `(tactic| dart_dispatch_side_condition) =>
    `(tactic| (ipureintro; first | decide | rfl | assumption | rotate_left))

/--
`wp_load H` takes the step of reading a variable, or an instance variable of an object, using the
points-to `H` for the cell read. The value's dynamic type comes from `dart_dynamic_type`, and the
pure side conditions (the subtype fact needed for the promotion check, and for an instance
variable, the dispatch of the property's name to it and its lookup) from
`dart_load_side_condition` and `dart_dispatch_side_condition`; any they can't prove are left as
goals after the main one. Afterwards, `H` is back in the context.
-/
syntax "wp_load " ident : tactic

macro_rules
  | `(tactic| wp_load $h) => `(tactic|
    (first
      | (apply DartSemantics.tac_wp_load
         iframe $h:ident
         isplitr
         · dart_dynamic_type
         isplitr
         dart_load_side_condition)
      | (apply DartSemantics.tac_wp_load_field
         iframe $h:ident
         isplitr
         · iassumption
         isplitr
         dart_dispatch_side_condition
         isplitr
         dart_load_side_condition
         isplitr
         · dart_dynamic_type
         isplitr
         dart_load_side_condition)
     inext
     iintro $h:ident
     dart_wp_tidy))

/--
`wp_store H` takes the step of an assignment to a local variable, using the points-to `H` for the
variable's cell. Afterwards, `H` is back in the context, saying that the cell holds the value
assigned. The side condition for `final` variables (`hfin` of `wp_variableSetAt`) is proved when
the variable isn't `final` or the cell is `.uninit`, and otherwise left as a goal after the main
one.
-/
syntax "wp_store " ident : tactic

macro_rules
  | `(tactic| wp_store $h) => `(tactic|
    (apply DartSemantics.tac_wp_store
     iframe $h:ident
     rotate_left
     · rfl
     first
       | (· intro h
            cases h)
       | (· intro _
            rfl)
       | rotate_left
     inext
     iintro $h:ident
     dart_wp_tidy))

/--
`wp_call hf` takes the step of a call of top-level function `f` whose arguments are all values,
using `hf : P.functions f = some d` (the function table's declaration of `f`). The number of
arguments is checked by `rfl`. Afterwards, the goal is `wp_call`'s premise without its `▷`: for
all locations `ℓs`, given the cells of the formal parameters (`PointsToVals ℓs vs`), the body
satisfies the postcondition.
-/
syntax "wp_call " term : tactic

macro_rules
  | `(tactic| wp_call $hf) => `(tactic|
    (refine DartSemantics.tac_wp_call (by rfl) $hf (by rfl) ?_
     inext))

/--
`wp_call_spec H` takes a call of a top-level function `f` whose arguments are all values, using
the specification `H : FunSpec f Pre Post` in the context. Afterwards, the goal is the
precondition, and that the postcondition implies the goal's postcondition
(`Pre vs ∗ ∀ o, Post vs o -∗ Φ o`).
-/
syntax "wp_call_spec " ident : tactic

macro_rules
  | `(tactic| wp_call_spec $h) => `(tactic|
    (apply DartSemantics.tac_wp_call_spec (by rfl)
     isplitr
     · iexact $h:ident))

/--
`wp_loop_step` takes the step of a loop that runs its body once, and then the loop again (which
`wp_pures` doesn't take; see `dart_pure_head_step`).
-/
syntax "wp_loop_step" : tactic

macro_rules
  | `(tactic| wp_loop_step) => `(tactic|
    (refine DartSemantics.tac_wp_pure rfl (fun _ => DartSemantics.HeadStep.loop) ?_
     inext))

/--
`wp_loop_inv I` applies the loop invariant rule (`tac_wp_loop_inv`) to a loop, with invariant `I`.
It leaves two goals: that the hypotheses give `I` (the invariant holds before the loop), and that
`I` makes the loop's body satisfy the postcondition that gives `I` back when the body completes
normally, and the loop's postcondition otherwise (one iteration preserves the invariant), with
`loopInvPost` unfolded.
-/
syntax "wp_loop_inv " term : tactic

macro_rules
  | `(tactic| wp_loop_inv $I) => `(tactic|
    ((apply DartSemantics.tac_wp_loop_inv $I) <;> dart_wp_tidy))

/--
`wp_int_checked` takes the step of an arithmetic operator on integers in mode `checked` whose
result `rfl` can't compute (because its operands aren't concrete numbers, say): it leaves the goal
that the exact result is in 64-bit range, and then the main goal, with the result.
-/
syntax "wp_int_checked" : tactic

macro_rules
  | `(tactic| wp_int_checked) => `(tactic|
    (apply DartSemantics.tac_wp_intBin_checked
     · rfl
     rotate_left
     inext
     dart_wp_tidy
     rotate_right))

/--
Bind the formal parameters of a function's body to their cells, after `wp_call` or in a proof of
`FunSpec.intro`'s premise, once the list of locations is concrete: compute
`(body.withIntMode mode).bindVariables (params.zip ℓs)`, setting the mode of each integer operator
in the body and resolving each parameter in the body to its cell. Likewise for the body of a member
or constructor (`SemanticParams.memberBody`), which also binds `this`, and fills in the `super`
slots.
-/
syntax "dart_bind_params" : tactic

macro_rules
  | `(tactic| dart_bind_params) => `(tactic|
    simp (config := { decide := true }) only [List.zip_cons_cons, List.zip_nil_left,
      List.zip_nil_right, DartLang.LoweredExpr.bindVariables, List.foldl_cons, List.foldl_nil,
      DartLang.LoweredExpr.withIntMode, DartLang.LoweredExpr.withIntModeList,
      DartSemantics.SemanticParams.memberBody, DartLang.LoweredExpr.withSuperclass,
      DartLang.LoweredExpr.withSuperclassList,
      DartLang.LoweredExpr.resolve, DartLang.LoweredExpr.resolveBlock,
      DartLang.LoweredExpr.resolveList, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte])

/--
`wp_new hk hc` takes the step of an instance creation by constructor `k` whose arguments are all
values, using `hk : P.constructors k = some d` and `hc : P.classes d.cls = some c` (the tables'
declarations of the constructor and its class). Afterwards, the goal is `wp_new`'s premise without
its `▷`: for the new object's own cell at `ℓ` and its instance variables' cells at `ℓs`, given the
object's header, the number of cells, and their ownership (all uninitialized), running the
constructor and then evaluating to the object satisfies the postcondition.
-/
syntax "wp_new " term:max ppSpace term:max : tactic

macro_rules
  | `(tactic| wp_new $hk $hc) => `(tactic|
    (refine DartSemantics.tac_wp_new (by rfl) $hk $hc ?_
     inext))

/--
`wp_ctor_run hk` takes the step of running constructor `k` on an object, using
`hk : P.constructors k = some d`. The number of arguments is checked by `rfl`. Afterwards, the goal
is `wp_ctorRun`'s premise without its `▷`: for all locations `ℓs`, given the cells of `this` and the
formal parameters (`PointsToVals ℓs (.obj ℓ :: vs)`), the initializers and body satisfy the
postcondition.
-/
syntax "wp_ctor_run " term : tactic

macro_rules
  | `(tactic| wp_ctor_run $hk) => `(tactic|
    (refine DartSemantics.tac_wp_ctorRun $hk (by rfl) ?_
     inext))

/--
`wp_method hd hm` takes the step of a method call on an object whose arguments are all values, using
`hd : P.dispatch k name = some (.proc key holder)` (the object's class's dispatch of the method's
name) and `hm : P.members key = some d` (the member table's declaration of the member). The
object's header must be in the context, and the number of arguments is checked by `rfl`.
Afterwards, the goal is `wp_methodCall`'s premise without its `▷`: for all locations `ℓs`, given the
cells of `this` and the formal parameters (`PointsToVals ℓs (.obj ℓ :: vs)`), the body satisfies the
postcondition.
-/
syntax "wp_method " term:max ppSpace term:max : tactic

macro_rules
  | `(tactic| wp_method $hd $hm) => `(tactic|
    (apply DartSemantics.tac_wp_methodCall (by rfl) $hd $hm (by rfl)
     isplitr
     · iassumption
     inext))

/--
`wp_method_spec H hd hm` takes a method call on an object whose arguments are all values, using the
specification `H : MemberSpec key holder Pre Post` in the context of the member that the object's
class dispatches the method's name to (`hd : P.dispatch k name = some (.proc key holder)`, and
`hm : P.members key = some d`). The object's header must be in the context, and the number of
arguments is checked by `rfl`. Afterwards, the goal is the precondition, and that the postcondition
implies the goal's postcondition one step later (`Pre (.obj ℓ :: vs) ∗ ▷ ∀ o, Post … o -∗ Φ o`).
-/
syntax "wp_method_spec " ident ppSpace term:max ppSpace term:max : tactic

macro_rules
  | `(tactic| wp_method_spec $h $hd $hm) => `(tactic|
    (apply DartSemantics.tac_wp_method_spec (by rfl) $hd $hm (by rfl)
     isplitr
     · iassumption
     isplitr
     · inext
       iexact $h:ident))

/--
`wp_const ℓ Hl Hc` takes the step of a string constant, introducing the location `ℓ` of its
canonical object, a persistent points-to `Hl` saying that it's a string with the constant's code
units (`ℓ ↦{.discard} .string cu`), and `Hc` saying that it's the constant's canonical object
(`IsConst τ (.string cu) ℓ`).
-/
syntax "wp_const " ident ppSpace ident ppSpace ident : tactic

macro_rules
  | `(tactic| wp_const $l $hl $hc) => `(tactic|
    (refine DartSemantics.tac_wp_constant_string ?_
     inext
     iintro %$l #$hl:ident #$hc:ident
     dart_wp_tidy))

/--
Prove `StringParts vs cus`, for parts `vs` and their string forms `cus` written out: a primitive
part's string form by `rfl`, and a string part's from a persistent points-to for its cell in the
context.
-/
syntax "dart_string_parts" : tactic

macro_rules
  | `(tactic| dart_string_parts) => `(tactic|
    (simp only [DartSemantics.StringParts, DartSemantics.StringPart]
     repeat' (first
       | itrivial
       | (ipureintro; rfl)
       | iassumption
       | isplitr)))

/--
`wp_concat cus ℓ H Hf` takes the step of a string concatenation whose parts are all values, whose
string forms are `cus` (proved by `dart_string_parts`), introducing the location `ℓ` of the new
string, its persistent points-to `H`, and `Hf` saying that it's newly allocated (`Fresh τ ℓ`).
-/
syntax "wp_concat " term:max ppSpace ident ppSpace ident ppSpace ident : tactic

macro_rules
  | `(tactic| wp_concat $cus $l $h $hf) => `(tactic|
    (refine DartSemantics.tac_wp_concat (cus := $cus) (by rfl) ?_
     dart_wp_tidy
     isplitr
     · dart_string_parts
     inext
     iintro %$l #$h:ident $hf:ident
     dart_wp_tidy))
