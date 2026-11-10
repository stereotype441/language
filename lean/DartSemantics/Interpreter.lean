module
public import DartSemantics.InterpHead
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

The interpreter's head steps (`headStep`), and their agreement with `HeadStep`, are in
`InterpHead.lean`; this file adds the steps inside evaluation contexts (`primStep`) and runs.

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
local notation "StepResult" => StepResult (τ := τ)

variable [RtSubChecker τ] [P : SemanticParams τ]

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
  | .call f args T => primStepArgs fuel e (fun vs ms => .call f vs ms T) [] args σ
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
  | .intBin op mode m₁ m₂ =>
    if m₁.toOutcome?.isSome then
      match m₁ with
      | .val v₁ =>
        if m₂.toOutcome?.isSome then headStep fuel e σ
        else stepIn (.intBinR op mode v₁) (primStep fuel m₂ σ)
      | _ => headStep fuel e σ
    else stepIn (.intBinL op mode m₂) (primStep fuel m₁ σ)
  | .intNeg mode m =>
    if m.toOutcome?.isSome then headStep fuel e σ else stepIn (.intNeg mode) (primStep fuel m σ)
  | .primEq m₁ m₂ =>
    if m₁.toOutcome?.isSome then
      match m₁ with
      | .val v₁ =>
        if m₂.toOutcome?.isSome then headStep fuel e σ
        else stepIn (.primEqR v₁) (primStep fuel m₂ σ)
      | _ => headStep fuel e σ
    else stepIn (.primEqL m₂) (primStep fuel m₁ σ)
  | .new k args T => primStepArgs fuel e (fun vs ms => .new k vs ms T) [] args σ
  | .initCtor m k args =>
    if m.toOutcome?.isSome then
      match m with
      | .val v => primStepArgs fuel e (fun vs ms => .initCtorArgs v k vs ms) [] args σ
      | _ => headStep fuel e σ
    else stepIn (.initCtorRecv k args) (primStep fuel m σ)
  | .initField m₁ name m₂ =>
    if m₁.toOutcome?.isSome then
      match m₁ with
      | .val v₁ =>
        if m₂.toOutcome?.isSome then headStep fuel e σ
        else stepIn (.initFieldR v₁ name) (primStep fuel m₂ σ)
      | _ => headStep fuel e σ
    else stepIn (.initFieldL name m₂) (primStep fuel m₁ σ)
  | .propertySet m₁ name m₂ =>
    if m₁.toOutcome?.isSome then
      match m₁ with
      | .val v₁ =>
        if m₂.toOutcome?.isSome then headStep fuel e σ
        else stepIn (.propertySetR v₁ name) (primStep fuel m₂ σ)
      | _ => headStep fuel e σ
    else stepIn (.propertySetL name m₂) (primStep fuel m₁ σ)
  | .ctorFrame m =>
    if m.toOutcome?.isSome then headStep fuel e σ else stepIn .ctorFrame (primStep fuel m σ)
  | .methodCall m name args T =>
    if m.toOutcome?.isSome then
      match m with
      | .val v => primStepArgs fuel e (fun vs ms => .methodCallArgs v name vs ms T) [] args σ
      | _ => headStep fuel e σ
    else stepIn (.methodCallRecv name args T) (primStep fuel m σ)
  | .superCall m name slot args T =>
    if m.toOutcome?.isSome then
      match m with
      | .val v =>
        primStepArgs fuel e (fun vs ms => .superCallArgs v name slot vs ms T) [] args σ
      | _ => headStep fuel e σ
    else stepIn (.superCallRecv name slot args T) (primStep fuel m σ)
  | .superGet m name slot T =>
    if m.toOutcome?.isSome then headStep fuel e σ
    else stepIn (.superGet name slot T) (primStep fuel m σ)
  | .superSet m₁ name slot m₂ =>
    if m₁.toOutcome?.isSome then
      match m₁ with
      | .val v₁ =>
        if m₂.toOutcome?.isSome then headStep fuel e σ
        else stepIn (.superSetR v₁ name slot) (primStep fuel m₂ σ)
      | _ => headStep fuel e σ
    else stepIn (.superSetL name slot m₂) (primStep fuel m₁ σ)
  | .checkPromotion T m =>
    if m.toOutcome?.isSome then headStep fuel e σ
    else stepIn (.checkPromotion T) (primStep fuel m σ)
  | .identical m₁ m₂ =>
    if m₁.toOutcome?.isSome then
      match m₁ with
      | .val v₁ =>
        if m₂.toOutcome?.isSome then headStep fuel e σ
        else stepIn (.identicalR v₁) (primStep fuel m₂ σ)
      | _ => headStep fuel e σ
    else stepIn (.identicalL m₂) (primStep fuel m₁ σ)
  | .letIn v m₁ m₂ =>
    if m₁.toOutcome?.isSome then headStep fuel e σ else stepIn (.letIn v m₂) (primStep fuel m₁ σ)
  | .concat parts => primStepArgs fuel e (fun vs ms => .concat vs ms) [] parts σ
  | _ => headStep fuel e σ
termination_by structural e

/--
The step that `e`, an expression whose operands before `args` have evaluated to `vs`, takes in
state `σ`: the step of the first of `args` that hasn't completed, if there is one, and otherwise
the head step of `e`. `mk vs' ms` is the context item for the operand after `vs'`, followed by
`ms`. (This is for the operands of calls and instance creations, which are lists of expressions.)
-/
@[expose]
public def primStepArgs (fuel : Nat) (e : LoweredExpr)
    (mk : List Value → List LoweredExpr → EctxItem) (vs : List Value) (args : List LoweredExpr)
    (σ : State) : StepResult :=
  match args with
  | [] => headStep fuel e σ
  | m :: ms =>
    if m.toOutcome?.isSome then
      match m with
      | .val v => primStepArgs fuel e mk (vs ++ [v]) ms σ
      | _ => headStep fuel e σ
    else stepIn (mk vs ms) (primStep fuel m σ)
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
`primStepArgs` skips over operands that are values: on values `ws`, followed by `args`, it
continues with `ws` added to the values so far (`primStepArgs fuel e mk (vs ++ ws) args σ`).
-/
theorem primStepArgs_map_val_append (fuel : Nat) (e : LoweredExpr)
    (mk : List Value → List LoweredExpr → EctxItem) (vs ws : List Value)
    (args : List LoweredExpr) (σ : State) :
    primStepArgs fuel e mk vs (ws.map .val ++ args) σ =
      primStepArgs fuel e mk (vs ++ ws) args σ := by
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
  case new k vs ms T =>
    simp only [EctxItem.fill, primStep]
    rw [primStepArgs_map_val_append]
    simp [primStepArgs, he]
  case initCtorArgs v k vs ms =>
    have hv : (LoweredExpr.val v).toOutcome? = some (.normal v) := rfl
    simp only [EctxItem.fill, primStep, hv, Option.isSome_some, ite_true]
    rw [primStepArgs_map_val_append]
    simp [primStepArgs, he]
  case methodCallArgs v name vs ms T =>
    have hv : (LoweredExpr.val v).toOutcome? = some (.normal v) := rfl
    simp only [EctxItem.fill, primStep, hv, Option.isSome_some, ite_true]
    rw [primStepArgs_map_val_append]
    simp [primStepArgs, he]
  case superCallArgs v name slot vs ms T =>
    have hv : (LoweredExpr.val v).toOutcome? = some (.normal v) := rfl
    simp only [EctxItem.fill, primStep, hv, Option.isSome_some, ite_true]
    rw [primStepArgs_map_val_append]
    simp [primStepArgs, he]
  case superSetR v₁ name slot =>
    have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
    simp [EctxItem.fill, primStep, he, hv]
  case identicalR v₁ =>
    have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
    simp [EctxItem.fill, primStep, he, hv]
  case checkEqR v₁ =>
    have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
    simp [EctxItem.fill, primStep, he, hv]
  case intBinR op mode v₁ =>
    have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
    simp [EctxItem.fill, primStep, he, hv]
  case primEqR v₁ =>
    have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
    simp [EctxItem.fill, primStep, he, hv]
  case initFieldR v₁ name =>
    have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
    simp [EctxItem.fill, primStep, he, hv]
  case propertySetR v₁ name =>
    have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
    simp [EctxItem.fill, primStep, he, hv]
  case concat vs ms =>
    simp only [EctxItem.fill, primStep]
    rw [primStepArgs_map_val_append]
    simp [primStepArgs, he]
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
If every operand in `args` that could be in evaluation position has completed (`h`: for every way
of splitting `args` into values `ws`, an operand `m`, and the rest `ms`, `m` has completed), then
`primStepArgs` takes the head step of `e` (`headStep fuel e σ`).
-/
theorem primStepArgs_of_isSome (fuel : Nat) (e : LoweredExpr)
    (mk : List Value → List LoweredExpr → EctxItem) (vs : List Value)
    (args : List LoweredExpr) (σ : State)
    (h : ∀ (ws : List Value) m ms, args = ws.map .val ++ m :: ms → m.toOutcome?.isSome) :
    primStepArgs fuel e mk vs args σ = headStep fuel e σ := by
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
  | letIn v m₁ m₂ => simp [primStep, hin (.letIn v m₂) m₁ rfl]
  | concat parts =>
    simp only [primStep]
    exact primStepArgs_of_isSome _ _ _ _ _ _ fun ws m ms heq =>
      hin (.concat ws ms) m (by rw [heq]; rfl)
  | variableSetAt x ℓ m => simp [primStep, hin (.variableSetAt x ℓ) m rfl]
  | call f args T =>
    simp only [primStep]
    exact primStepArgs_of_isSome _ _ _ _ _ _ fun ws m ms heq =>
      hin (.call f ws ms T) m (by rw [heq]; rfl)
  | new k args T =>
    simp only [primStep]
    exact primStepArgs_of_isSome _ _ _ _ _ _ fun ws m ms heq =>
      hin (.new k ws ms T) m (by rw [heq]; rfl)
  | initCtor m k args =>
    have h₁ := hin (.initCtorRecv k args) m rfl
    cases m with
    | val v =>
      have hv : (LoweredExpr.val v).toOutcome? = some (.normal v) := rfl
      simp only [primStep, hv, Option.isSome_some, ite_true]
      exact primStepArgs_of_isSome _ _ _ _ _ _ fun ws m ms heq =>
        hin (.initCtorArgs v k ws ms) m (by rw [heq]; rfl)
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
  | initField m₁ name m₂ =>
    have h₁ := hin (.initFieldL name m₂) m₁ rfl
    cases m₁ with
    | val v₁ =>
      have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
      simp [primStep, hin (.initFieldR v₁ name) m₂ rfl, hv]
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
  | propertySet m₁ name m₂ =>
    have h₁ := hin (.propertySetL name m₂) m₁ rfl
    cases m₁ with
    | val v₁ =>
      have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
      simp [primStep, hin (.propertySetR v₁ name) m₂ rfl, hv]
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
  | ctorFrame m => simp [primStep, hin .ctorFrame m rfl]
  | methodCall m name args T =>
    have h₁ := hin (.methodCallRecv name args T) m rfl
    cases m with
    | val v =>
      have hv : (LoweredExpr.val v).toOutcome? = some (.normal v) := rfl
      simp only [primStep, hv, Option.isSome_some, ite_true]
      exact primStepArgs_of_isSome _ _ _ _ _ _ fun ws m ms heq =>
        hin (.methodCallArgs v name ws ms T) m (by rw [heq]; rfl)
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
  | superCall m name slot args T =>
    have h₁ := hin (.superCallRecv name slot args T) m rfl
    cases m with
    | val v =>
      have hv : (LoweredExpr.val v).toOutcome? = some (.normal v) := rfl
      simp only [primStep, hv, Option.isSome_some, ite_true]
      exact primStepArgs_of_isSome _ _ _ _ _ _ fun ws m ms heq =>
        hin (.superCallArgs v name slot ws ms T) m (by rw [heq]; rfl)
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
  | superGet m name slot T => simp [primStep, hin (.superGet name slot T) m rfl]
  | superSet m₁ name slot m₂ =>
    have h₁ := hin (.superSetL name slot m₂) m₁ rfl
    cases m₁ with
    | val v₁ =>
      have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
      simp [primStep, hin (.superSetR v₁ name slot) m₂ rfl, hv]
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
  | checkPromotion T m => simp [primStep, hin (.checkPromotion T) m rfl]
  | identical m₁ m₂ =>
    have h₁ := hin (.identicalL m₂) m₁ rfl
    cases m₁ with
    | val v₁ =>
      have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
      simp [primStep, hin (.identicalR v₁) m₂ rfl, hv]
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
  | ret m => simp [primStep, hin .ret m rfl]
  | frame m T => simp [primStep, hin (.frame T) m rfl]
  | labeled l m => simp [primStep, hin (.labeled l) m rfl]
  | intNeg mode m => simp [primStep, hin (.intNeg mode) m rfl]
  | intBin op mode m₁ m₂ =>
    have h₁ := hin (.intBinL op mode m₂) m₁ rfl
    cases m₁ with
    | val v₁ =>
      have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
      simp [primStep, hin (.intBinR op mode v₁) m₂ rfl, hv]
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
  | primEq m₁ m₂ =>
    have h₁ := hin (.primEqL m₂) m₁ rfl
    cases m₁ with
    | val v₁ =>
      have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
      simp [primStep, hin (.primEqR v₁) m₂ rfl, hv]
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
  | check kind m => simp [primStep, hin (.check kind) m rfl]
  | checkEq m₁ m₂ =>
    have h₁ := hin (.checkEqL m₂) m₁ rfl
    cases m₁ with
    | val v₁ =>
      have hv : (LoweredExpr.val v₁).toOutcome? = some (.normal v₁) := rfl
      simp [primStep, hin (.checkEqR v₁) m₂ rfl, hv]
    | _ => first | (simp [LoweredExpr.toOutcome?] at h₁; done) | rfl
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
  cases e <;> dsimp only at h
  case call f args T =>
    exact primStepArgs_sound (E := (.call f · T)) (fun _ _ _ => rfl) [] args (by simp) h
  case new k args T =>
    exact primStepArgs_sound (E := (.new k · T)) (fun _ _ _ => rfl) [] args (by simp) h
  case concat parts =>
    exact primStepArgs_sound (E := .concat) (fun _ _ _ => rfl) [] parts (by simp) h
  case initCtor m k args =>
    split at h
    · split at h
      · exact primStepArgs_sound (E := (.initCtor (.val ‹Value›) k ·)) (fun _ _ _ => rfl) []
          args (by simp) h
      · exact (headStep_sound h).primStep
    · exact stepIn_sound (Ki := .initCtorRecv k args) (primStep_sound m) h
  case methodCall m name args T =>
    split at h
    · split at h
      · exact primStepArgs_sound (E := (.methodCall (.val ‹Value›) name · T)) (fun _ _ _ => rfl)
          [] args (by simp) h
      · exact (headStep_sound h).primStep
    · exact stepIn_sound (Ki := .methodCallRecv name args T) (primStep_sound m) h
  case superCall m name slot args T =>
    split at h
    · split at h
      · exact primStepArgs_sound (E := (.superCall (.val ‹Value›) name slot · T))
          (fun _ _ _ => rfl) [] args (by simp) h
      · exact (headStep_sound h).primStep
    · exact stepIn_sound (Ki := .superCallRecv name slot args T) (primStep_sound m) h
  all_goals
    repeat' first
      | exact (headStep_sound h).primStep
      | (have := stepIn_sound (primStep_sound _) h; exact this)
      | split at h

/--
Soundness of `primStepArgs`: every step that it takes (`h`) from `e`, which is
`E (vs.map .val ++ args)` (`he`), is a step of the semantics (`(e, σ) -<[]>-> (e', σ', [])`),
if `mk vs' ms` is the context item for the operand after `vs'`, followed by `ms` (`hmk`).
-/
theorem primStepArgs_sound {fuel : Nat} {e : LoweredExpr} {E : List LoweredExpr → LoweredExpr}
    {mk : List Value → List LoweredExpr → EctxItem}
    (hmk : ∀ vs m ms, (mk vs ms).fill m = E (vs.map .val ++ m :: ms)) (vs : List Value)
    (args : List LoweredExpr) {σ : State} {e' : LoweredExpr} {σ' : State}
    (he : e = E (vs.map .val ++ args))
    (h : primStepArgs fuel e mk vs args σ = .next e' σ') :
    (e, σ) -<[]>-> (e', σ', []) := by
  match args with
  | [] =>
    simp only [primStepArgs] at h
    exact (headStep_sound h).primStep
  | m :: ms =>
    simp only [primStepArgs] at h
    split at h
    · split at h
      · exact primStepArgs_sound hmk (vs ++ [‹Value›]) ms (by simp [he]) h
      · exact (headStep_sound h).primStep
    · have := stepIn_sound (Ki := mk vs ms) (primStep_sound m) h
      rwa [hmk, ← he] at this

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
  unfold headStep propagate at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [StepResult.stuck.injEq] at h; exact h.symm)
    | (rcases promotionCheck_eq_stuck h with h | h
       · cases h
       · exact h)
    | (obtain ⟨b, hb⟩ := withCheck_eq_stuck h
       cases b <;> simp at hb)
    | (refine headStepArgs_eq_stuck (fun _ hk => ?_) h
       first
         | exact callStep_eq_stuck hk
         | exact newStep_eq_stuck hk
         | exact initCtorStep_eq_stuck hk
         | exact methodCallStep_eq_stuck hk
         | exact superCallStep_eq_stuck hk
         | exact concatStep_eq_stuck hk)

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
  cases e <;> dsimp only at h
  case call f args T =>
    exact primStepArgs_stuck_redex (E := (.call f · T)) (fun _ _ _ => rfl) [] args (by simp) h
  case new k args T =>
    exact primStepArgs_stuck_redex (E := (.new k · T)) (fun _ _ _ => rfl) [] args (by simp) h
  case concat parts =>
    exact primStepArgs_stuck_redex (E := .concat) (fun _ _ _ => rfl) [] parts (by simp) h
  case initCtor m k args =>
    split at h
    · split at h
      · exact primStepArgs_stuck_redex (E := (.initCtor (.val ‹Value›) k ·)) (fun _ _ _ => rfl)
          [] args (by simp) h
      · exact headStep_stuck_redex h
    · exact stepIn_stuck_redex (Ki := .initCtorRecv k args) (primStep_stuck_redex m) h
  case methodCall m name args T =>
    split at h
    · split at h
      · exact primStepArgs_stuck_redex (E := (.methodCall (.val ‹Value›) name · T))
          (fun _ _ _ => rfl) [] args (by simp) h
      · exact headStep_stuck_redex h
    · exact stepIn_stuck_redex (Ki := .methodCallRecv name args T) (primStep_stuck_redex m) h
  case superCall m name slot args T =>
    split at h
    · split at h
      · exact primStepArgs_stuck_redex (E := (.superCall (.val ‹Value›) name slot · T))
          (fun _ _ _ => rfl) [] args (by simp) h
      · exact headStep_stuck_redex h
    · exact stepIn_stuck_redex (Ki := .superCallRecv name slot args T) (primStep_stuck_redex m)
        h
  all_goals
    repeat' first
      | exact headStep_stuck_redex h
      | (have := stepIn_stuck_redex (primStep_stuck_redex _) h; exact this)
      | split at h

/--
The redex of a stuck expression with a list of operands: if `primStepArgs` reports that `e`, which
is `E (vs.map .val ++ args)` (`he`), is stuck at `redex` (`h`), and `mk vs' ms` is the context item
for the operand after `vs'`, followed by `ms` (`hmk`), then:
- `redex` is in evaluation position in `e` (`∃ K, e = fillCtx K redex`); and
- `redex` takes no head step (`∀ e' σ', ¬ HeadStep redex σ e' σ'`).
-/
theorem primStepArgs_stuck_redex {fuel : Nat} {e : LoweredExpr}
    {E : List LoweredExpr → LoweredExpr} {mk : List Value → List LoweredExpr → EctxItem}
    (hmk : ∀ vs m ms, (mk vs ms).fill m = E (vs.map .val ++ m :: ms)) (vs : List Value)
    (args : List LoweredExpr) {σ : State} {redex : LoweredExpr}
    (he : e = E (vs.map .val ++ args))
    (h : primStepArgs fuel e mk vs args σ = .stuck redex) :
    (∃ K, e = fillCtx K redex) ∧ ∀ e' σ', ¬ HeadStep redex σ e' σ' := by
  match args with
  | [] =>
    simp only [primStepArgs] at h
    exact headStep_stuck_redex h
  | m :: ms =>
    simp only [primStepArgs] at h
    split at h
    · split at h
      · exact primStepArgs_stuck_redex hmk (vs ++ [‹Value›]) ms (by simp [he]) h
      · exact headStep_stuck_redex h
    · have := stepIn_stuck_redex (Ki := mk vs ms) (primStep_stuck_redex m) h
      rwa [hmk, ← he] at this

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
