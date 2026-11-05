module
public import DartSemantics.Language
public import Mathlib.Logic.Relation

/-!
# The interpreter

An interpreter for the semantics, proved to agree with it. It runs on any type representation
with a run-time subtype check algorithm (`RtSubChecker`), such as `SimpleType`.

The semantics is a relation, because a run-time subtype check need not terminate (see
`HeadStep.lean`). The interpreter is a function, so it can't follow a check forever. Instead, it
takes *fuel*, a budget for each check: `primStep fuel e σ` is the step that `e` takes in state `σ`,
or `stuck` if `e` has none, or `outOfFuel` if a check didn't answer within the budget. Running out
of fuel is never reported as `stuck`, and given enough fuel, the interpreter finds every step
except one that a check that doesn't terminate would take, forever.

When `e` is stuck, the interpreter also reports the *redex* it was trying to step: the
subexpression of `e` in evaluation position, which has no head step (`primStep_stuck_redex`). For
example, `{ x!; y }` with `x` unbound is stuck at the redex `x`. This tells a user of the
interpreter *why* a program is stuck, without repeating the semantics' evaluation order.

The interpreter follows two implementation rules:
- `primStep` is structurally recursive, so that the kernel can evaluate it. (Well-founded
  recursion would make it irreducible.)
- It uses the state *linearly*: it decides where the redex is before it touches the state, and
  then uses the state once. Otherwise, the state would still be shared when an allocation pushes
  a cell onto the heap, and every allocation would copy the heap.
-/

namespace DartSemantics.Interp

open DartLang Iris.ProgramLogic EctxItemLanguage Language.Notation PrimStep

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "EctxItem" => EctxItem (τ := τ)
local notation "Outcome" => Outcome (τ := τ)
local notation "State" => State (τ := τ)

/-- The result of trying to take a step. -/
public inductive StepResult where
  /-- The step goes to expression `e` and state `σ`. -/
  | next (e : LoweredExpr) (σ : State)
  /--
  There is no step. `redex` is the subexpression in evaluation position, which has no head step
  (see `primStep_stuck_redex`).
  -/
  | stuck (redex : LoweredExpr)
  /-- A run-time subtype check didn't answer within the budget of fuel. -/
  | outOfFuel

local notation "StepResult" => StepResult (τ := τ)

/--
Apply `f` to the expression that a step goes to. (A redex that is stuck is left alone: it is still
the subexpression in evaluation position.)
-/
@[expose]
public def StepResult.map (f : LoweredExpr → LoweredExpr) : StepResult → StepResult
  | .next e σ => .next (f e) σ
  | .stuck redex => .stuck redex
  | .outOfFuel => .outOfFuel

/-- Plug the expression that a step goes to into the hole of context item `Ki`. -/
@[expose]
public def stepIn (Ki : EctxItem) (r : StepResult) : StepResult := r.map Ki.fill

variable [RtSubChecker τ]

/--
Run the run-time check of whether `S` is a subtype of `T`, within a budget of `fuel`, and continue
with `k` applied to the answer.
-/
@[expose]
public def withCheck (fuel : Nat) (S T : τ) (k : Bool → StepResult) : StepResult :=
  match RtSubChecker.check fuel S T with
  | some (b, _) => k b
  | none => .outOfFuel

variable [P : SemanticParams τ]

/--
Perform the promotion check of value `v` against type `T` (if the semantics performs promotion
checks), within a budget of `fuel`, and continue with `r` if it passes. If it fails, the step is
stuck at `redex`.
-/
@[expose]
public def promotionCheck (fuel : Nat) (σ : State) (v : Value) (T : τ) (redex : LoweredExpr)
    (r : StepResult) : StepResult :=
  match P.promotionChecks with
  | .trust => r
  | .verify =>
    match σ.dynamicType v with
    | some S => withCheck fuel S T fun b => if b then r else .stuck redex
    | none => .stuck redex

/--
The head step of the call `e`, which is `.call f args T`, in state `σ` (see `HeadStep.call`): once
every argument is a value, the call itself; if an argument has thrown, returned or broken out of a
labeled statement, propagating it out of the call. If there is none, the result is stuck at `e`.
-/
@[expose]
public def headStepCall (e : LoweredExpr) (f : String) (args : List LoweredExpr) (T : τ)
    (σ : State) : StepResult :=
  match LoweredExpr.splitVals args with
  | (vs, []) =>
    match P.functions f with
    | some d =>
      if d.params.length = vs.length then
        let r := σ.allocAll (vs.map Cell.val)
        .next (.frame (d.body.bindVariables (d.params.zip r.1)) T) r.2
      else .stuck e
    | none => .stuck e
  | (_, .throwing v :: _) => .next (.throwing v) σ
  | (_, .returning v :: _) => .next (.returning v) σ
  | (_, .breaking l :: _) => .next (.breaking l) σ
  | _ => .stuck e

/--
The head step of `e` in state `σ` (see `HeadStep`), with a budget of `fuel` for each check. If
there is none, the result is stuck at `e` itself.
-/
@[expose]
public def headStep (fuel : Nat) (e : LoweredExpr) (σ : State) : StepResult :=
  match e with
  | .null => .next (.val .null) σ
  | .bool b => .next (.val (.bool b)) σ
  | .int n => .next (.val (.int n)) σ
  | .declare v T startsNull => .next (.block [.declare v T startsNull]) σ
  | .block [] => .next (.val .null) σ
  | .block (.declare v _ startsNull :: ms) =>
    .next (.block (LoweredExpr.resolveBlock v σ.fresh ms))
      (σ.alloc (if startsNull then .val .null else .uninit))
  | .block (m :: ms) => .next (.seq m (.block ms)) σ
  | .seq (.val _) m => .next m σ
  | .varAt _ T ℓ =>
    match σ.lookup ℓ with
    | some (.val v) => promotionCheck fuel σ v T e (.next (.val v) σ)
    | _ => .stuck e
  | .nullCheck (.val .null) => .next (.throwing (.error .typeError)) σ
  | .nullCheck (.val v) => .next (.val v) σ
  | .as (.val v) T =>
    match σ.dynamicType v with
    | some S =>
      withCheck fuel S T fun b =>
        if b then .next (.val v) σ else .next (.throwing (.error .typeError)) σ
    | none => .stuck e
  | .is (.val v) T =>
    match σ.dynamicType v with
    | some S => withCheck fuel S T fun b => .next (.val (.bool b)) σ
    | none => .stuck e
  | .cond (.val (.bool true)) m₂ _ _ => .next m₂ σ
  | .cond (.val (.bool false)) _ m₃ _ => .next m₃ σ
  | .propertyGet (.val v) p T =>
    match σ.instanceVariable? v p.name with
    | some ℓf =>
      match σ.lookup ℓf with
      | some (.val w) => promotionCheck fuel σ w T e (.next (.val w) σ)
      | _ => .stuck e
    | none =>
      match P.getterImpl p v σ with
      | some w => promotionCheck fuel σ w T e (.next (.val w) σ)
      | none => .stuck e
  | .variableSetAt x ℓ (.val w) =>
    -- Inspect the cell before updating it, so that the update can be done in place.
    match σ.lookup ℓ with
    | some (.object _ _) => .stuck e
    | some (.val _) => if x.isFinal then .stuck e else .next (.val w) (σ.update ℓ (.val w))
    | some .uninit => .next (.val w) (σ.update ℓ (.val w))
    | none => .stuck e
  | .call f args T => headStepCall e f args T σ
  | .ret (.val v) => .next (.returning v) σ
  | .frame (.returning v) _ => .next (.val v) σ
  | .frame (.val _) _ => .next (.val .null) σ
  | .check kind (.val v) =>
    match kind.holds v with
    | true => .next (.val .null) σ
    | false => .next (.throwing (.error .expectFailed)) σ
  | .checkEq (.val v₁) (.val v₂) =>
    match Value.primEq? v₁ v₂ with
    | some true => .next (.val .null) σ
    | some false => .next (.throwing (.error .expectFailed)) σ
    | none => .stuck e
  | .loop m => .next (.seq m (.loop m)) σ
  | .labeled _ (.val _) => .next (.val .null) σ
  | .labeled l (.breaking l') => if l' = l then .next (.val .null) σ else .next (.breaking l') σ
  | .brk l => .next (.breaking l) σ
  | .nullCheck (.throwing v) => .next (.throwing v) σ
  | .as (.throwing v) _ => .next (.throwing v) σ
  | .is (.throwing v) _ => .next (.throwing v) σ
  | .cond (.throwing v) _ _ _ => .next (.throwing v) σ
  | .propertyGet (.throwing v) _ _ => .next (.throwing v) σ
  | .seq (.throwing v) _ => .next (.throwing v) σ
  | .variableSetAt _ _ (.throwing v) => .next (.throwing v) σ
  | .ret (.throwing v) => .next (.throwing v) σ
  | .frame (.throwing v) _ => .next (.throwing v) σ
  | .check _ (.throwing v) => .next (.throwing v) σ
  | .checkEq (.throwing v) _ => .next (.throwing v) σ
  | .checkEq (.val _) (.throwing v) => .next (.throwing v) σ
  | .labeled _ (.throwing v) => .next (.throwing v) σ
  | .nullCheck (.returning v) => .next (.returning v) σ
  | .as (.returning v) _ => .next (.returning v) σ
  | .is (.returning v) _ => .next (.returning v) σ
  | .cond (.returning v) _ _ _ => .next (.returning v) σ
  | .propertyGet (.returning v) _ _ => .next (.returning v) σ
  | .seq (.returning v) _ => .next (.returning v) σ
  | .variableSetAt _ _ (.returning v) => .next (.returning v) σ
  | .ret (.returning v) => .next (.returning v) σ
  | .check _ (.returning v) => .next (.returning v) σ
  | .checkEq (.returning v) _ => .next (.returning v) σ
  | .checkEq (.val _) (.returning v) => .next (.returning v) σ
  | .labeled _ (.returning v) => .next (.returning v) σ
  | .nullCheck (.breaking l) => .next (.breaking l) σ
  | .as (.breaking l) _ => .next (.breaking l) σ
  | .is (.breaking l) _ => .next (.breaking l) σ
  | .cond (.breaking l) _ _ _ => .next (.breaking l) σ
  | .propertyGet (.breaking l) _ _ => .next (.breaking l) σ
  | .seq (.breaking l) _ => .next (.breaking l) σ
  | .variableSetAt _ _ (.breaking l) => .next (.breaking l) σ
  | .ret (.breaking l) => .next (.breaking l) σ
  | .check _ (.breaking l) => .next (.breaking l) σ
  | .checkEq (.breaking l) _ => .next (.breaking l) σ
  | .checkEq (.val _) (.breaking l) => .next (.breaking l) σ
  | _ => .stuck e

/-
`primStep` and `primStepArgs` are mutually recursive: a call's arguments are a list of
expressions, and stepping one of them steps an expression. Each is structurally recursive (on the
expression, and on the list of arguments that remain), so the pair still reduces in the kernel.
-/
mutual

/--
The step that `e` takes in state `σ`, with a budget of `fuel` for each check: the head step of
the redex in evaluation position. The expression is decomposed one evaluation context item at a
time, as `EctxItem.fill` builds it up.
-/
@[expose]
public def primStep (fuel : Nat) (e : LoweredExpr) (σ : State) : StepResult :=
  match e with
  | .nullCheck m =>
    if m.toOutcome?.isSome then headStep fuel e σ else stepIn .nullCheck (primStep fuel m σ)
  | .as m T =>
    if m.toOutcome?.isSome then headStep fuel e σ else stepIn (.as T) (primStep fuel m σ)
  | .is m T =>
    if m.toOutcome?.isSome then headStep fuel e σ else stepIn (.is T) (primStep fuel m σ)
  | .cond m₁ m₂ m₃ T =>
    if m₁.toOutcome?.isSome then headStep fuel e σ
    else stepIn (.cond m₂ m₃ T) (primStep fuel m₁ σ)
  | .propertyGet m p T =>
    if m.toOutcome?.isSome then headStep fuel e σ
    else stepIn (.propertyGet p T) (primStep fuel m σ)
  | .seq m₁ m₂ =>
    if m₁.toOutcome?.isSome then headStep fuel e σ else stepIn (.seq m₂) (primStep fuel m₁ σ)
  | .variableSetAt x ℓ m =>
    if m.toOutcome?.isSome then headStep fuel e σ
    else stepIn (.variableSetAt x ℓ) (primStep fuel m σ)
  | .call f args T => primStepArgs fuel e f [] args T σ
  | .ret m =>
    if m.toOutcome?.isSome then headStep fuel e σ else stepIn .ret (primStep fuel m σ)
  | .frame m T =>
    if m.toOutcome?.isSome then headStep fuel e σ else stepIn (.frame T) (primStep fuel m σ)
  | .check kind m =>
    if m.toOutcome?.isSome then headStep fuel e σ else stepIn (.check kind) (primStep fuel m σ)
  | .checkEq m₁ m₂ =>
    if m₁.toOutcome?.isSome then
      match m₁ with
      | .val v₁ =>
        if m₂.toOutcome?.isSome then headStep fuel e σ
        else stepIn (.checkEqR v₁) (primStep fuel m₂ σ)
      | _ => headStep fuel e σ
    else stepIn (.checkEqL m₂) (primStep fuel m₁ σ)
  | .labeled l m =>
    if m.toOutcome?.isSome then headStep fuel e σ else stepIn (.labeled l) (primStep fuel m σ)
  | _ => headStep fuel e σ
termination_by structural e

/--
The step that the call `e`, which is `.call f (vs.map .val ++ args) T`, takes in state `σ`, where
the arguments before `args` have evaluated to `vs`: the step of the first argument in `args` that
hasn't completed, if there is one, and otherwise the head step of `e`.
-/
@[expose]
public def primStepArgs (fuel : Nat) (e : LoweredExpr) (f : String) (vs : List Value)
    (args : List LoweredExpr) (T : τ) (σ : State) : StepResult :=
  match args with
  | [] => headStep fuel e σ
  | m :: ms =>
    if m.toOutcome?.isSome then
      match m with
      | .val v => primStepArgs fuel e f (vs ++ [v]) ms T σ
      | _ => headStep fuel e σ
    else stepIn (.call f vs ms T) (primStep fuel m σ)
termination_by structural args

end

/-- The result of running a program. -/
public inductive RunResult where
  /-- The program completed with outcome `o`, in state `σ`. -/
  | done (o : Outcome) (σ : State)
  /--
  The program got stuck at expression `e`, in state `σ`. `redex` is the subexpression of `e` in
  evaluation position, which has no head step (see `run_stuck`).
  -/
  | stuck (e redex : LoweredExpr) (σ : State)
  /-- The program ran out of fuel at expression `e`, in state `σ`. -/
  | outOfFuel (e : LoweredExpr) (σ : State)
  deriving Repr

local notation "RunResult" => RunResult (τ := τ)

/--
Run expression `e` from state `σ`, for at most `fuel` steps, giving each step's checks a budget of
the fuel that remains.
-/
@[expose]
public def run (fuel : Nat) (e : LoweredExpr) (σ : State) : RunResult :=
  match e.toOutcome? with
  | some o => .done o σ
  | none =>
    match fuel with
    | 0 => .outOfFuel e σ
    | fuel + 1 =>
      match primStep fuel e σ with
      | .next e' σ' => run fuel e' σ'
      | .stuck redex => .stuck e redex σ
      | .outOfFuel => .outOfFuel e σ

/-! ## Agreement with the semantics -/

/--
`Converges f r`: as a function of the budget of fuel, `f` gives `r` once the budget is large
enough, and runs out of fuel otherwise.
-/
public def Converges (f : Nat → StepResult) (r : StepResult) : Prop :=
  (∀ fuel, f fuel = r ∨ f fuel = .outOfFuel) ∧ ∃ n, ∀ fuel, n ≤ fuel → f fuel = r

omit Γ [RtSubChecker τ] P in
/-- If `f` gives `r` regardless of its budget of fuel (`h`), then `f` converges to `r`. -/
theorem Converges.of_eq {f : Nat → StepResult} {r : StepResult} (h : ∀ fuel, f fuel = r) :
    Converges f r :=
  ⟨fun fuel => .inl (h fuel), 0, fun fuel _ => h fuel⟩

omit Γ [RtSubChecker τ] P in
/--
If two functions of fuel `f` and `g` always produce the same result (`h`), and `g` converges to `r`
(`hg`), then `f` does too.
-/
theorem Converges.congr {f g : Nat → StepResult} {r : StepResult} (h : ∀ fuel, f fuel = g fuel)
    (hg : Converges g r) : Converges f r :=
  funext h ▸ hg

omit Γ [RtSubChecker τ] P in
/--
Applying `g` to the expression that each step goes to preserves convergence: if `f` converges to
`r` (`h`), then `f` followed by `StepResult.map g` converges to `r.map g`.
-/
theorem Converges.map {f : Nat → StepResult} {r : StepResult} (g : LoweredExpr → LoweredExpr)
    (h : Converges f r) : Converges (fun fuel => (f fuel).map g) (r.map g) := by
  obtain ⟨h₁, n, h₂⟩ := h
  refine ⟨fun fuel => ?_, n, fun fuel hn => by simp only [h₂ fuel hn]⟩
  rcases h₁ fuel with h | h <;> simp [h, StepResult.map]

omit Γ [RtSubChecker τ] P in
/-- If `f` converges to both `r₁` (`h₁`) and `r₂` (`h₂`), then they're the same (`r₁ = r₂`). -/
public theorem Converges.unique {f : Nat → StepResult} {r₁ r₂ : StepResult} (h₁ : Converges f r₁)
    (h₂ : Converges f r₂) : r₁ = r₂ := by
  obtain ⟨-, n₁, h₁⟩ := h₁
  obtain ⟨-, n₂, h₂⟩ := h₂
  rw [← h₁ (max n₁ n₂) (Nat.le_max_left _ _), ← h₂ (max n₁ n₂) (Nat.le_max_right _ _)]

omit P in
/--
If the run-time check of `S` against `T` answers `b` (`h`), and `k b` is `r` (`hk`), then
`withCheck` converges to `r`: it finds the answer once its budget of fuel is large enough.
-/
theorem withCheck_converges {S T : τ} {b : Bool} {k : Bool → StepResult} {r : StepResult}
    (h : RtSub S T b) (hk : k b = r) : Converges (fun fuel => withCheck fuel S T k) r := by
  subst hk
  constructor
  · intro fuel
    cases hc : RtSubChecker.check fuel S T with
    | none => exact .inr (by simp [withCheck, hc])
    | some p =>
      obtain ⟨b', fuel'⟩ := p
      exact .inl (by simp [withCheck, hc, rtSub_unique (RtSubChecker.check_sound hc) h])
  · obtain ⟨n, fuel', hc⟩ := RtSubChecker.check_complete h
    refine ⟨n, fun fuel hn => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp [withCheck, RtSubChecker.check_mono j hc]

omit P in
/--
If the run-time check of `S` against `T` gives no answer (`h`: it doesn't terminate), then
`withCheck` runs out of fuel (`.outOfFuel`), however much fuel it has.
-/
theorem withCheck_diverge {fuel : Nat} {S T : τ} {k : Bool → StepResult}
    (h : ∀ b, ¬ RtSub S T b) : withCheck fuel S T k = .outOfFuel := by
  unfold withCheck
  cases hc : RtSubChecker.check fuel S T with
  | none => rfl
  | some p => exact absurd (RtSubChecker.check_sound hc) (h _)

omit P in
/--
If `withCheck` produces a step (`h`), then the run-time check gave some answer `b` that `RtSub`
allows (`RtSub S T b`), and the step is `k b` (`k b = .next e σ`).
-/
theorem withCheck_eq_next {fuel : Nat} {S T : τ} {k : Bool → StepResult} {e : LoweredExpr}
    {σ : State} (h : withCheck fuel S T k = .next e σ) : ∃ b, RtSub S T b ∧ k b = .next e σ := by
  unfold withCheck at h
  cases hc : RtSubChecker.check fuel S T with
  | none => simp [hc] at h
  | some p =>
    obtain ⟨b, fuel'⟩ := p
    simp only [hc] at h
    exact ⟨b, RtSubChecker.check_sound hc, h⟩

/--
If `v` passes the promotion check against `T` (`h`), then `promotionCheck` converges to `r`: it
lets the step go ahead once its budget of fuel is large enough.
-/
theorem promotionCheck_converges {σ : State} {v : Value} {T : τ} {redex : LoweredExpr}
    (h : PassesPromotionCheck σ v T) (r : StepResult) :
    Converges (fun fuel => promotionCheck fuel σ v T redex r) r := by
  cases h with
  | trust h => exact Converges.of_eq fun fuel => by simp [promotionCheck, h]
  | verify h hS hT =>
    refine Converges.congr (fun fuel => ?_) (withCheck_converges (k := fun b => if b then r
      else .stuck redex) hT rfl)
    simp [promotionCheck, h, hS]

/--
If `promotionCheck` lets a step go ahead (`h`), then `v` passes the promotion check against `T`
(`PassesPromotionCheck σ v T`), and the step is `r` (`r = .next e σ'`).
-/
theorem promotionCheck_eq_next {fuel : Nat} {σ σ' : State} {v : Value} {T : τ}
    {redex : LoweredExpr} {r : StepResult} {e : LoweredExpr}
    (h : promotionCheck fuel σ v T redex r = .next e σ') :
    PassesPromotionCheck σ v T ∧ r = .next e σ' := by
  unfold promotionCheck at h
  split at h
  · exact ⟨.trust ‹_›, h⟩
  · split at h
    · obtain ⟨b, hb, hk⟩ := withCheck_eq_next h
      cases b
      · simp at hk
      · exact ⟨.verify ‹_› ‹_› hb, hk⟩
    · simp at h

/--
Completeness of `headStep`: if `e` takes a head step to `e'` (`h`), then either:
- `headStep` finds it, given enough fuel, and never reports that `e` is stuck
  (`Converges (headStep · e σ) (.next e' σ')`); or
- the step is one that a check that doesn't terminate takes, which goes nowhere: it leaves the
  expression (`e' = e`) and the state (`σ' = σ`) unchanged, and `headStep` runs out of fuel there,
  however much it has (`∀ fuel, headStep fuel e σ = .outOfFuel`).
-/
theorem headStep_complete {e e' : LoweredExpr} {σ σ' : State} (h : HeadStep e σ e' σ') :
    Converges (headStep · e σ) (.next e' σ') ∨
      (e' = e ∧ σ' = σ ∧ ∀ fuel, headStep fuel e σ = .outOfFuel) := by
  cases h with
  | null | bool | int | declare | blockNil | blockDeclare | seq | nullCheckNull | condTrue
  | condFalse | ret | frameReturning | frameVal | loop | labeledVal | brk =>
    exact .inl (Converges.of_eq fun _ => rfl)
  | call hf hlen =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep, headStepCall, hf, hlen])
  | checkPass h | checkFail h | checkEqPass h | checkEqFail h =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep, h])
  | @blockCons m ms σ h =>
    cases m
    case declare v T startsNull => exact absurd rfl (h v T startsNull)
    all_goals exact .inl (Converges.of_eq fun _ => rfl)
  | @varAt x T ℓ v σ hℓ hv =>
    exact .inl (Converges.congr (fun fuel => by simp [headStep, hℓ])
      (promotionCheck_converges (redex := .varAt x T ℓ) hv _))
  | @nullCheck v σ h =>
    cases v
    case null => exact absurd rfl h
    all_goals exact .inl (Converges.of_eq fun _ => rfl)
  | asTrue hS h | asFalse hS h | «is» hS h =>
    exact .inl (Converges.congr (fun fuel => by simp only [headStep, hS]; rfl)
      (withCheck_converges h (by rfl)))
  | asDiverge hS h | isDiverge hS h =>
    exact .inr ⟨rfl, rfl, fun fuel => by simp only [headStep, hS]; exact withCheck_diverge h⟩
  | @propertyGetField v w p T ℓf σ hf hw hc =>
    exact .inl (Converges.congr (fun fuel => by simp [headStep, hf, hw])
      (promotionCheck_converges (redex := .propertyGet (.val v) p T) hc _))
  | @propertyGetGetter v w p T σ hf hg hc =>
    exact .inl (Converges.congr (fun fuel => by simp [headStep, hf, hg])
      (promotionCheck_converges (redex := .propertyGet (.val v) p T) hc _))
  | @variableSetAt x ℓ w c σ hℓ hc hfin =>
    cases c
    case object C fs => exact absurd rfl (hc C fs)
    case val u =>
      cases hx : x.isFinal
      · exact .inl (Converges.of_eq fun _ => by simp [headStep, hℓ, hx])
      · exact absurd (hfin hx) nofun
    case uninit => exact .inl (Converges.of_eq fun _ => by simp [headStep, hℓ])
  | @bubbleException Ki v σ =>
    cases Ki
    case call f vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep, headStepCall,
          LoweredExpr.splitVals_map_val_append vs (ms := .throwing v :: ms) (by simp)])
    all_goals exact .inl (Converges.of_eq fun _ => rfl)
  | @bubbleReturn Ki v σ hKi =>
    cases Ki
    case call f vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep, headStepCall,
          LoweredExpr.splitVals_map_val_append vs (ms := .returning v :: ms) (by simp)])
    case frame T => simp [EctxItem.handlesReturn] at hKi
    all_goals exact .inl (Converges.of_eq fun _ => rfl)
  | @bubbleBreak Ki l σ hKi hret =>
    cases Ki
    case call f vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep, headStepCall,
          LoweredExpr.splitVals_map_val_append vs (ms := .breaking l :: ms) (by simp)])
    case frame T => simp [EctxItem.handlesReturn] at hret
    case labeled l' =>
      have hne : l ≠ l' := fun h => by subst h; simp [EctxItem.handlesBreak] at hKi
      exact .inl (Converges.of_eq fun _ => by simp [EctxItem.fill, headStep, hne])
    all_goals exact .inl (Converges.of_eq fun _ => rfl)
  | labeledBreak => exact .inl (Converges.of_eq fun _ => by simp [headStep])

omit [RtSubChecker τ] in
/--
Soundness of `headStepCall`: every step that it finds for the call `.call f args T` (`h`) is a head
step (`HeadStep (.call f args T) σ e' σ'`).
-/
theorem headStepCall_sound {f : String} {args : List LoweredExpr} {T : τ} {e' : LoweredExpr}
    {σ σ' : State} (h : headStepCall (.call f args T) f args T σ = .next e' σ') :
    HeadStep (.call f args T) σ e' σ' := by
  have hargs := LoweredExpr.splitVals_append args
  unfold headStepCall at h
  split at h
  · next vs heq =>
    rw [heq] at hargs
    simp only [List.append_nil] at hargs
    subst hargs
    split at h
    · next d hf =>
      split at h
      · next hlen =>
        obtain ⟨rfl, rfl⟩ := StepResult.next.inj h
        exact .call hf hlen
      · cases h
    · cases h
  · next vs v ms heq =>
    rw [heq] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := StepResult.next.inj h
    exact .bubbleException (Ki := .call f vs ms T)
  · next vs v ms heq =>
    rw [heq] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := StepResult.next.inj h
    exact .bubbleReturn (Ki := .call f vs ms T) rfl
  · next vs l ms heq =>
    rw [heq] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := StepResult.next.inj h
    exact .bubbleBreak (Ki := .call f vs ms T) rfl rfl
  · cases h

omit [RtSubChecker τ] in
/--
`headStepCall` is only ever stuck at the expression it was given: if it is stuck at `redex` (`h`),
then `redex = e`.
-/
theorem headStepCall_eq_stuck {e : LoweredExpr} {f : String} {args : List LoweredExpr} {T : τ}
    {redex : LoweredExpr} {σ : State} (h : headStepCall e f args T σ = .stuck redex) :
    redex = e := by
  unfold headStepCall at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [StepResult.stuck.injEq] at h; exact h.symm)

/--
Soundness of `headStep`: every step that it finds (`h`) is a head step (`HeadStep e σ e' σ'`).
-/
theorem headStep_sound {fuel : Nat} {e e' : LoweredExpr} {σ σ' : State}
    (h : headStep fuel e σ = .next e' σ') : HeadStep e σ e' σ' := by
  unfold headStep at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (obtain ⟨rfl, rfl⟩ := StepResult.next.inj h
       first
         | (constructor <;> assumption)
         | exact .variableSetAt ‹_› (by intro _ _ h; cases h) (by intro _; rfl)
         | exact .variableSetAt ‹_› (by intro _ _ h; cases h) (by simp_all)
         | (rename_i hb
            first
              | (subst hb; exact .blockDeclare)
              | (simp only [Bool.not_eq_true] at hb; subst hb; exact .blockDeclare))
         | exact .bubbleException (Ki := .nullCheck)
         | exact .bubbleException (Ki := .as _)
         | exact .bubbleException (Ki := .is _)
         | exact .bubbleException (Ki := .cond _ _ _)
         | exact .bubbleException (Ki := .propertyGet _ _)
         | exact .bubbleException (Ki := .seq _)
         | exact .bubbleException (Ki := .variableSetAt _ _)
         | exact .bubbleException (Ki := .ret)
         | exact .bubbleException (Ki := .frame _)
         | exact .bubbleException (Ki := .check _)
         | exact .bubbleException (Ki := .checkEqL _)
         | exact .bubbleException (Ki := .checkEqR _)
         | exact .bubbleException (Ki := .labeled _)
         | exact .bubbleReturn (Ki := .nullCheck) rfl
         | exact .bubbleReturn (Ki := .as _) rfl
         | exact .bubbleReturn (Ki := .is _) rfl
         | exact .bubbleReturn (Ki := .cond _ _ _) rfl
         | exact .bubbleReturn (Ki := .propertyGet _ _) rfl
         | exact .bubbleReturn (Ki := .seq _) rfl
         | exact .bubbleReturn (Ki := .variableSetAt _ _) rfl
         | exact .bubbleReturn (Ki := .ret) rfl
         | exact .bubbleReturn (Ki := .check _) rfl
         | exact .bubbleReturn (Ki := .checkEqL _) rfl
         | exact .bubbleReturn (Ki := .checkEqR _) rfl
         | exact .bubbleReturn (Ki := .labeled _) rfl
         | exact .bubbleBreak (Ki := .nullCheck) rfl rfl
         | exact .bubbleBreak (Ki := .as _) rfl rfl
         | exact .bubbleBreak (Ki := .is _) rfl rfl
         | exact .bubbleBreak (Ki := .cond _ _ _) rfl rfl
         | exact .bubbleBreak (Ki := .propertyGet _ _) rfl rfl
         | exact .bubbleBreak (Ki := .seq _) rfl rfl
         | exact .bubbleBreak (Ki := .variableSetAt _ _) rfl rfl
         | exact .bubbleBreak (Ki := .ret) rfl rfl
         | exact .bubbleBreak (Ki := .check _) rfl rfl
         | exact .bubbleBreak (Ki := .checkEqL _) rfl rfl
         | exact .bubbleBreak (Ki := .checkEqR _) rfl rfl
         | (subst_vars; exact .labeledBreak)
         | (rename_i hne
            exact .bubbleBreak (Ki := .labeled _)
              (by simp only [EctxItem.handlesBreak, beq_eq_false_iff_ne, ne_eq]
                  exact fun h => hne h.symm) rfl))
    | exact headStepCall_sound h
    | (obtain ⟨hc, hr⟩ := promotionCheck_eq_next h
       obtain ⟨rfl, rfl⟩ := StepResult.next.inj hr
       first
         | exact .varAt ‹_› hc
         | exact .propertyGetField ‹_› ‹_› hc
         | exact .propertyGetGetter ‹_› ‹_› hc)
    | (obtain ⟨b, hb, hk⟩ := withCheck_eq_next h
       first
         | (obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
            exact .is ‹_› hb)
         | (cases b <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hk <;>
            obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
            · exact .asFalse ‹_› hb
            · exact .asTrue ‹_› hb))

/--
`primStepArgs` skips over arguments that are values: on values `ws`, followed by `args`, it
continues with `ws` added to the values so far (`primStepArgs fuel e f (vs ++ ws) args T σ`).
-/
theorem primStepArgs_map_val_append (fuel : Nat) (e : LoweredExpr) (f : String)
    (vs ws : List Value) (args : List LoweredExpr) (T : τ) (σ : State) :
    primStepArgs fuel e f vs (ws.map .val ++ args) T σ =
      primStepArgs fuel e f (vs ++ ws) args T σ := by
  induction ws generalizing vs with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.cons_append, primStepArgs, LoweredExpr.toOutcome?,
      Option.isSome_some, ite_true]
    rw [ih]
    simp

/--
If the expression `e` in the hole of `Ki` hasn't completed (`he`), then `primStep` on `Ki.fill e`
takes `e`'s step, and plugs the result back into the hole (`stepIn Ki (primStep fuel e σ)`).
-/
theorem primStep_fill (fuel : Nat) {Ki : EctxItem} {e : LoweredExpr} (σ : State)
    (he : e.toOutcome? = none) : primStep fuel (Ki.fill e) σ = stepIn Ki (primStep fuel e σ) := by
  cases Ki
  case call f vs ms T =>
    simp only [EctxItem.fill, primStep]
    rw [primStepArgs_map_val_append]
    simp [primStepArgs, he]
  case checkEqR v₁ =>
    have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
    simp [EctxItem.fill, primStep, he, hv]
  all_goals simp [EctxItem.fill, primStep, he]

/--
If the expression `e` in the hole of evaluation context `K` hasn't completed (`he`), then
`primStep` on `fillCtx K e` takes `e`'s step, and plugs the result back into the context
(`(primStep fuel e σ).map (fillCtx K)`).
-/
theorem primStep_fillCtx (fuel : Nat) (K : List EctxItem) {e : LoweredExpr} (σ : State)
    (he : e.toOutcome? = none) :
    primStep fuel (fillCtx K e) σ = (primStep fuel e σ).map (fillCtx K) := by
  induction K generalizing e with
  | nil => change primStep fuel e σ = _; cases primStep fuel e σ <;> rfl
  | cons Ki K ih =>
    change primStep fuel (fillCtx K (Ki.fill e)) σ = _
    rw [ih (EctxItem.toOutcome?_fill Ki e), primStep_fill fuel σ he]
    cases primStep fuel e σ <;> rfl

/--
If every argument in `args` that could be in evaluation position has completed (`h`: for every way
of splitting `args` into values `ws`, an argument `m`, and the rest `ms`, `m` has completed), then
`primStepArgs` takes the head step of the call `e` (`headStep fuel e σ`).
-/
theorem primStepArgs_of_isSome (fuel : Nat) (e : LoweredExpr) (f : String) (vs : List Value)
    (args : List LoweredExpr) (T : τ) (σ : State)
    (h : ∀ (ws : List Value) m ms, args = ws.map .val ++ m :: ms → m.toOutcome?.isSome) :
    primStepArgs fuel e f vs args T σ = headStep fuel e σ := by
  induction args generalizing vs with
  | nil => simp [primStepArgs]
  | cons m ms ih =>
    have hm := h [] m ms rfl
    simp only [primStepArgs, hm, ite_true]
    cases m
    case val v =>
      exact ih (vs ++ [v]) fun ws m' ms' heq => h (v :: ws) m' ms' (by simp [heq])
    all_goals rfl

/--
At a redex `e`, one that takes a head step (`h`), `primStep` takes the head step
(`primStep fuel e σ = headStep fuel e σ`).
-/
theorem primStep_of_headStep {e e' : LoweredExpr} {σ σ' : State} (h : HeadStep e σ e' σ')
    (fuel : Nat) : primStep fuel e σ = headStep fuel e σ := by
  have hin : ∀ (Ki : EctxItem) (e₁ : LoweredExpr), e = Ki.fill e₁ → e₁.toOutcome?.isSome := by
    rintro Ki e₁ rfl
    exact h.isSome_toOutcome?_of_fill
  cases e with
  | nullCheck m => simp [primStep, hin .nullCheck m rfl]
  | «as» m T => simp [primStep, hin (.as T) m rfl]
  | «is» m T => simp [primStep, hin (.is T) m rfl]
  | cond m₁ m₂ m₃ T => simp [primStep, hin (.cond m₂ m₃ T) m₁ rfl]
  | propertyGet m p T => simp [primStep, hin (.propertyGet p T) m rfl]
  | seq m₁ m₂ => simp [primStep, hin (.seq m₂) m₁ rfl]
  | variableSetAt x ℓ m => simp [primStep, hin (.variableSetAt x ℓ) m rfl]
  | call f args T =>
    simp only [primStep]
    exact primStepArgs_of_isSome _ _ _ _ _ _ _ fun ws m ms heq =>
      hin (.call f ws ms T) m (by rw [heq]; rfl)
  | ret m => simp [primStep, hin .ret m rfl]
  | frame m T => simp [primStep, hin (.frame T) m rfl]
  | labeled l m => simp [primStep, hin (.labeled l) m rfl]
  | check kind m => simp [primStep, hin (.check kind) m rfl]
  | checkEq m₁ m₂ =>
    have h₁ := hin (.checkEqL m₂) m₁ rfl
    cases m₁ with
    | val v₁ =>
      have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
      simp [primStep, hin (.checkEqR v₁) m₂ rfl, hv]
    | _ => simp_all [primStep, LoweredExpr.toOutcome?]
  | _ => rfl

omit [RtSubChecker τ] in
/--
If every step that `r` reports is a step of `e` (`hr`), then every step that `stepIn Ki r` reports
(`h`) is a step of `Ki.fill e`. `primStep_sound` uses this to carry soundness from the hole of `Ki`
out to the whole expression.
-/
theorem stepIn_sound {Ki : EctxItem} {e e' : LoweredExpr} {σ σ' : State} {r : StepResult}
    (hr : ∀ {e'' σ''}, r = .next e'' σ'' → (e, σ) -<[]>-> (e'', σ'', []))
    (h : stepIn Ki r = .next e' σ') : (Ki.fill e, σ) -<[]>-> (e', σ', []) := by
  cases r with
  | next e'' σ'' =>
    simp only [stepIn, StepResult.map, StepResult.next.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact primStep_fillItem (hr rfl)
  | stuck _ | outOfFuel => cases h

mutual

/--
**Soundness of the interpreter**: every step that `primStep` takes from `e` in state `σ`, to `e'` in
state `σ'` (`h`), is a step of the semantics (`(e, σ) -<[]>-> (e', σ', [])`).
-/
public theorem primStep_sound {fuel : Nat} (e : LoweredExpr) {σ : State} {e' : LoweredExpr}
    {σ' : State} (h : primStep fuel e σ = .next e' σ') : (e, σ) -<[]>-> (e', σ', []) := by
  rw [primStep.eq_def] at h
  cases e <;> dsimp only at h <;>
    repeat' first
      | exact (headStep_sound h).primStep
      | (have := stepIn_sound (primStep_sound _) h; exact this)
      | exact primStepArgs_sound [] _ (by simp) h
      | split at h

/--
Soundness of `primStepArgs`: every step that it takes (`h`) from the call `e`, which is
`.call f (vs.map .val ++ args) T` (`he`), is a step of the semantics
(`(e, σ) -<[]>-> (e', σ', [])`).
-/
theorem primStepArgs_sound {fuel : Nat} {e : LoweredExpr} {f : String} (vs : List Value)
    (args : List LoweredExpr) {T : τ} {σ : State} {e' : LoweredExpr} {σ' : State}
    (he : e = .call f (vs.map .val ++ args) T)
    (h : primStepArgs fuel e f vs args T σ = .next e' σ') :
    (e, σ) -<[]>-> (e', σ', []) := by
  match args with
  | [] =>
    simp only [primStepArgs] at h
    exact (headStep_sound h).primStep
  | m :: ms =>
    simp only [primStepArgs] at h
    split at h
    · split at h
      · exact primStepArgs_sound (f := f) (T := T) (vs ++ [‹Value›]) ms (by simp [he]) h
      · exact (headStep_sound h).primStep
    · subst he
      exact stepIn_sound (Ki := .call f vs ms T) (primStep_sound m) h

end

/--
**Completeness of the interpreter**: if `e` takes a step to `e'` (`h`), then the step makes no
observations (`obs = []`) and forks no threads (`efs = []`), and either:
- `primStep` finds it, given enough fuel, and never reports that `e` is stuck
  (`Converges (primStep · e σ) (.next e' σ')`); or
- the step is one that a run-time subtype check that doesn't terminate takes, which goes nowhere:
  it leaves the expression (`e' = e`) and the state (`σ' = σ`) unchanged, and `primStep` runs out
  of fuel there, however much it has (`∀ fuel, primStep fuel e σ = .outOfFuel`).
-/
public theorem primStep_complete {e e' : LoweredExpr} {σ σ' : State} {obs : List Obs}
    {efs : List LoweredExpr} (h : (e, σ) -<obs>-> (e', σ', efs)) :
    obs = [] ∧ efs = [] ∧
      (Converges (primStep · e σ) (.next e' σ') ∨
        (e' = e ∧ σ' = σ ∧ ∀ fuel, primStep fuel e σ = .outOfFuel)) := by
  obtain ⟨hbase⟩ := h
  rename_i e₁ e₂ K
  obtain ⟨hbase, rfl, rfl⟩ := hbase
  refine ⟨rfl, rfl, ?_⟩
  have heq : ∀ fuel, primStep fuel (fill K e₁) σ = (headStep fuel e₁ σ).map (fillCtx K) := by
    intro fuel
    rw [fill_eq_fillCtx, primStep_fillCtx fuel K σ hbase.toOutcome?_eq_none,
      primStep_of_headStep hbase]
  rcases headStep_complete hbase with hc | ⟨rfl, rfl, hd⟩
  · exact .inl (Converges.congr heq (hc.map _))
  · exact .inr ⟨rfl, rfl, fun fuel => by rw [heq, hd]; rfl⟩

/--
If `primStep` reports that `e` is stuck (at some redex; `h`), it is: `e` takes no step
(`Irreducible`).
-/
public theorem primStep_stuck {fuel : Nat} {e redex : LoweredExpr} {σ : State}
    (h : primStep fuel e σ = .stuck redex) : Irreducible (e, σ) := by
  intro obs e' σ' efs hstep
  obtain ⟨-, -, hc | ⟨-, -, hd⟩⟩ := primStep_complete hstep
  · rcases hc.1 fuel with h' | h' <;> simp only [h] at h' <;> cases h'
  · rw [hd fuel] at h
    cases h

/-! ## The redex of a stuck expression -/

omit P in
/--
`withCheck` is stuck at `redex` (`h`) only if its continuation `k` is stuck, at `redex`, when
given some answer `b` of the run-time subtype check (`k b = .stuck redex`).

`withCheck` itself never gets stuck: it either runs out of fuel, or passes the check's answer to
`k`. So `b` is the answer that the check gave.
-/
theorem withCheck_eq_stuck {fuel : Nat} {S T : τ} {k : Bool → StepResult} {redex : LoweredExpr}
    (h : withCheck fuel S T k = .stuck redex) : ∃ b, k b = .stuck redex := by
  unfold withCheck at h
  split at h
  · exact ⟨_, h⟩
  · cases h

/--
`promotionCheck` is stuck at `redex'` (`h`) only if either:
- the step `r` that it continues with is stuck at `redex'` (`r = .stuck redex'`); or
- the promotion check failed, so `promotionCheck` is stuck at the redex it was given
  (`redex' = redex`).
-/
theorem promotionCheck_eq_stuck {fuel : Nat} {σ : State} {v : Value} {T : τ}
    {redex redex' : LoweredExpr} {r : StepResult}
    (h : promotionCheck fuel σ v T redex r = .stuck redex') :
    r = .stuck redex' ∨ redex' = redex := by
  unfold promotionCheck at h
  split at h
  · exact .inl h
  · split at h
    · obtain ⟨b, hb⟩ := withCheck_eq_stuck h
      cases b
      · -- The check failed: `if false then r else .stuck redex` is `.stuck redex`.
        simp only [Bool.false_eq_true, ite_false, StepResult.stuck.injEq] at hb
        exact .inr hb.symm
      · simp only [ite_true] at hb
        exact .inl hb
    · simp only [StepResult.stuck.injEq] at h
      exact .inr h.symm

/--
`headStep` is only ever stuck at its own argument: if it is stuck at `redex` (`h`), then
`redex = e`.
-/
theorem headStep_eq_stuck {fuel : Nat} {e redex : LoweredExpr} {σ : State}
    (h : headStep fuel e σ = .stuck redex) : redex = e := by
  unfold headStep at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [StepResult.stuck.injEq] at h; exact h.symm)
    | (rcases promotionCheck_eq_stuck h with h | h
       · cases h
       · exact h)
    | (obtain ⟨b, hb⟩ := withCheck_eq_stuck h
       cases b <;> simp at hb)
    | exact headStepCall_eq_stuck h

/--
If `headStep` reports that `e` is stuck at `redex` (`h`), then:
- `redex` is in evaluation position in `e`, trivially: `e` is `redex` in the empty evaluation
  context (`∃ K, e = fillCtx K redex`); and
- `redex` takes no head step (`∀ e' σ', ¬ HeadStep redex σ e' σ'`).
-/
theorem headStep_stuck_redex {fuel : Nat} {e redex : LoweredExpr} {σ : State}
    (h : headStep fuel e σ = .stuck redex) :
    (∃ K, e = fillCtx K redex) ∧ ∀ e' σ', ¬ HeadStep redex σ e' σ' := by
  obtain rfl := headStep_eq_stuck h
  refine ⟨⟨[], rfl⟩, fun e' σ' hstep => ?_⟩
  rcases headStep_complete hstep with hc | ⟨-, -, hd⟩
  · rcases hc.1 fuel with h' | h' <;> simp only [h] at h' <;> cases h'
  · rw [hd fuel] at h
    cases h

omit Γ [RtSubChecker τ] P in
/--
Plugging into a context with one more item on the outside (`K ++ [Ki]`, since contexts list their
items innermost first) produces the same result as plugging into `K`, then into the hole of `Ki`.
-/
theorem fillCtx_append_singleton (K : List EctxItem) (Ki : EctxItem) (m : LoweredExpr) :
    fillCtx (K ++ [Ki]) m = Ki.fill (fillCtx K m) := by
  simp [fillCtx, List.foldl_append]

omit [RtSubChecker τ] in
/--
If `r` being stuck at `redex` means that `redex` is a stuck redex of `m` (`hr`), and plugging `r`
into the hole of `Ki` is stuck at `redex` (`h`), then `redex` is a stuck redex of `Ki.fill m`:
- `redex` is in evaluation position in `Ki.fill m` (`∃ K, Ki.fill m = fillCtx K redex`); and
- `redex` takes no head step (`∀ e' σ', ¬ HeadStep redex σ e' σ'`).

`primStep_stuck_redex` uses this to carry the redex from the hole of `Ki` out to the whole
expression.
-/
theorem stepIn_stuck_redex {Ki : EctxItem} {m redex : LoweredExpr} {σ : State} {r : StepResult}
    (hr : r = .stuck redex →
      (∃ K, m = fillCtx K redex) ∧ ∀ e' σ', ¬ HeadStep redex σ e' σ')
    (h : stepIn Ki r = .stuck redex) :
    (∃ K, Ki.fill m = fillCtx K redex) ∧ ∀ e' σ', ¬ HeadStep redex σ e' σ' := by
  cases r with
  | stuck redex' =>
    simp only [stepIn, StepResult.map, StepResult.stuck.injEq] at h
    subst h
    obtain ⟨⟨K, rfl⟩, hirr⟩ := hr rfl
    exact ⟨⟨K ++ [Ki], (fillCtx_append_singleton K Ki redex').symm⟩, hirr⟩
  | next | outOfFuel => cases h

mutual

/--
**The redex of a stuck expression**: if `primStep` reports that `e` is stuck at `redex` (`h`),
then:
- `redex` is in evaluation position in `e`: `e` is `redex` plugged into some evaluation context `K`
  (`∃ K, e = fillCtx K redex`); and
- `redex` takes no head step (`∀ e' σ', ¬ HeadStep redex σ e' σ'`).
-/
public theorem primStep_stuck_redex {fuel : Nat} (e : LoweredExpr) {redex : LoweredExpr}
    {σ : State} (h : primStep fuel e σ = .stuck redex) :
    (∃ K, e = fillCtx K redex) ∧ ∀ e' σ', ¬ HeadStep redex σ e' σ' := by
  rw [primStep.eq_def] at h
  cases e <;> dsimp only at h <;>
    repeat' first
      | exact headStep_stuck_redex h
      | (have := stepIn_stuck_redex (primStep_stuck_redex _) h; exact this)
      | exact primStepArgs_stuck_redex [] _ (by simp) h
      | split at h

/--
The redex of a stuck call: if `primStepArgs` reports that the call `e`, which is
`.call f (vs.map .val ++ args) T` (`he`), is stuck at `redex` (`h`), then:
- `redex` is in evaluation position in `e` (`∃ K, e = fillCtx K redex`); and
- `redex` takes no head step (`∀ e' σ', ¬ HeadStep redex σ e' σ'`).
-/
theorem primStepArgs_stuck_redex {fuel : Nat} {e : LoweredExpr} {f : String} (vs : List Value)
    (args : List LoweredExpr) {T : τ} {σ : State} {redex : LoweredExpr}
    (he : e = .call f (vs.map .val ++ args) T)
    (h : primStepArgs fuel e f vs args T σ = .stuck redex) :
    (∃ K, e = fillCtx K redex) ∧ ∀ e' σ', ¬ HeadStep redex σ e' σ' := by
  match args with
  | [] =>
    simp only [primStepArgs] at h
    exact headStep_stuck_redex h
  | m :: ms =>
    simp only [primStepArgs] at h
    split at h
    · split at h
      · exact primStepArgs_stuck_redex (f := f) (T := T) (vs ++ [‹Value›]) ms (by simp [he]) h
      · exact headStep_stuck_redex h
    · subst he
      exact stepIn_stuck_redex (Ki := .call f vs ms T) (primStep_stuck_redex m) h

end

/--
`Steps (e, σ) (e', σ')` says that expression `e`, in state `σ`, reaches expression `e'` and state
`σ'` by zero or more steps of the semantics. Each step is a step as iris-lean defines it (a head
step of the redex inside its evaluation context; see `Language.lean`), making no observations and
forking no threads. This is the reflexive transitive closure of the step relation, used to state
what `run` computes (`run_done` and `run_stuck`).
-/
public abbrev Steps : LoweredExpr × State → LoweredExpr × State → Prop :=
  Relation.ReflTransGen fun (e, σ) (e', σ') => (e, σ) -<[]>-> (e', σ', [])

/--
Running an expression that has already completed with outcome `o` (`h`) gives its outcome, without
taking a step (`.done o σ`).
-/
theorem run_of_toOutcome? {fuel : Nat} {e : LoweredExpr} {σ : State} {o : Outcome}
    (h : e.toOutcome? = some o) : run fuel e σ = .done o σ := by
  cases fuel <;> simp [run, h]

/--
Running an expression that hasn't completed (`h`), with no fuel left, runs out of fuel
(`.outOfFuel e σ`).
-/
theorem run_zero {e : LoweredExpr} {σ : State} (h : e.toOutcome? = none) :
    run 0 e σ = .outOfFuel e σ := by
  simp [run, h]

/--
Running an expression that hasn't completed (`h`), with fuel left, takes one step with `primStep`
and runs the result with one less unit of fuel.
-/
theorem run_succ {fuel : Nat} {e : LoweredExpr} {σ : State} (h : e.toOutcome? = none) :
    run (fuel + 1) e σ =
      match primStep fuel e σ with
      | .next e' σ' => run fuel e' σ'
      | .stuck redex => .stuck e redex σ
      | .outOfFuel => .outOfFuel e σ := by
  rw [run]
  simp [h]

/--
If `run` says that a program completes with outcome `o` in state `σ'` (`h`), it does: it steps there
(`Steps (e, σ) (o.toExpr, σ')`).
-/
public theorem run_done {fuel : Nat} {e : LoweredExpr} {σ σ' : State} {o : Outcome}
    (h : run fuel e σ = .done o σ') : Steps (e, σ) (o.toExpr, σ') := by
  induction fuel generalizing e σ with
  | zero =>
    cases ho : e.toOutcome? with
    | some o' =>
      rw [run_of_toOutcome? ho] at h
      cases h
      rw [LoweredExpr.toExpr_of_toOutcome? ho]
    | none =>
      rw [run_zero ho] at h
      cases h
  | succ fuel ih =>
    cases ho : e.toOutcome? with
    | some o' =>
      rw [run_of_toOutcome? ho] at h
      cases h
      rw [LoweredExpr.toExpr_of_toOutcome? ho]
    | none =>
      rw [run_succ ho] at h
      cases hs : primStep fuel e σ <;> simp only [hs] at h
      · exact .head (primStep_sound _ hs) (ih h)
      · cases h
      · cases h

/--
If `run` says that a program gets stuck at `e'`, at redex `redex`, in state `σ'` (`h`), it does:
- it steps there (`Steps (e, σ) (e', σ')`);
- it gets stuck (`Stuck (e', σ')`);
- `redex` is in evaluation position in `e'` (`∃ K, e' = fillCtx K redex`); and
- `redex` takes no head step (`∀ e'' σ'', ¬ HeadStep redex σ' e'' σ''`).
-/
public theorem run_stuck {fuel : Nat} {e e' redex : LoweredExpr} {σ σ' : State}
    (h : run fuel e σ = .stuck e' redex σ') :
    Steps (e, σ) (e', σ') ∧ Stuck (e', σ') ∧ (∃ K, e' = fillCtx K redex) ∧
      ∀ e'' σ'', ¬ HeadStep redex σ' e'' σ'' := by
  induction fuel generalizing e σ with
  | zero =>
    cases ho : e.toOutcome? with
    | some o' =>
      rw [run_of_toOutcome? ho] at h
      cases h
    | none =>
      rw [run_zero ho] at h
      cases h
  | succ fuel ih =>
    cases ho : e.toOutcome? with
    | some o' =>
      rw [run_of_toOutcome? ho] at h
      cases h
    | none =>
      rw [run_succ ho] at h
      cases hs : primStep fuel e σ <;> simp only [hs] at h
      · obtain ⟨hsteps, hrest⟩ := ih h
        exact ⟨.head (primStep_sound _ hs) hsteps, hrest⟩
      · cases h
        exact ⟨.refl, ⟨by simpa using ho, primStep_stuck hs⟩, primStep_stuck_redex _ hs⟩
      · cases h

end DartSemantics.Interp
