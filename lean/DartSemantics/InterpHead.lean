module
public import DartSemantics.HeadStep

/-!
# The interpreter's head steps

The head-step part of the interpreter (see `Interpreter.lean`): `Interp.headStep fuel e σ`, the
head step of `e` in state `σ`, with a budget of `fuel` for each run-time subtype check. It's proved
to agree with the head-step relation `HeadStep`: every step it finds is a head step
(`headStep_sound`), and it finds every head step, given enough fuel, except one that a check that
doesn't terminate would take, forever (`headStep_complete`).

Because `headStep` is a function, this also shows that the semantics is deterministic
(`HeadStep.deterministic`): two head steps of the same expression are both found by `headStep`,
so they're the same. This proof doesn't depend on the number of head-step rules, unlike a proof
that compares every pair of rules.

This file needs only `HeadStep.lean`, so that the files that make the semantics an iris-lean
language (`Language.lean`) and build the program logic on it can use `HeadStep.deterministic`.
-/

namespace DartSemantics.Interp

open DartLang

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
The head step of `e`, an expression whose operands still to be considered are `args` (such as a
call's arguments), in state `σ`: once every one of `args` is a value (`vs`), `k vs`; if one of them
has thrown, returned or broken out of a labeled statement, propagating it out of `e`. If there is
none, the result is stuck at `e`.
-/
@[expose]
public def headStepArgs (e : LoweredExpr) (args : List LoweredExpr) (σ : State)
    (k : List Value → StepResult) : StepResult :=
  match LoweredExpr.splitVals args with
  | (vs, []) => k vs
  | (_, .throwing v :: _) => .next (.throwing v) σ
  | (_, .returning v :: _) => .next (.returning v) σ
  | (_, .breaking l :: _) => .next (.breaking l) σ
  | _ => .stuck e

/--
The head step of the call `e`, which is `.call f (vs.map .val) T`, in state `σ`, once its arguments
have evaluated to `vs` (see `HeadStep.call`). If there is none, the result is stuck at `e`.
-/
@[expose]
public def callStep (e : LoweredExpr) (f : String) (vs : List Value) (T : τ) (σ : State) :
    StepResult :=
  match P.functions f with
  | some d =>
    if d.params.length = vs.length then
      let r := σ.allocAll (vs.map Cell.val)
      .next (.frame ((d.body.withIntMode (P.intModeOf f)).bindVariables (d.params.zip r.1)) T)
        r.2
    else .stuck e
  | none => .stuck e

/--
The head step of the instance creation `e`, which is `.new k (vs.map .val) T`, in state `σ`, once
its arguments have evaluated to `vs` (see `HeadStep.new`). If there is none, the result is stuck at
`e`.
-/
@[expose]
public def newStep (e : LoweredExpr) (k : String) (vs : List Value) (σ : State) : StepResult :=
  match P.constructors k with
  | some d =>
    match P.classes d.cls with
    | some c =>
      let r := σ.allocObject d.cls c.type c.instanceVariables
      .next (.seq (.ctorRun r.1 k vs) (.val (.obj r.1))) r.2
    | none => .stuck e
  | none => .stuck e

/--
The head step of the `super(args)` or `this(args)` call `e`, which is
`.initCtor (.val v) k (vs.map .val)`, in state `σ` (see `HeadStep.initCtor`). If there is none (the
receiver isn't an object), the result is stuck at `e`.
-/
@[expose]
public def initCtorStep (e : LoweredExpr) (v : Value) (k : String) (vs : List Value) (σ : State) :
    StepResult :=
  match v with
  | .obj ℓ => .next (.ctorRun ℓ k vs) σ
  | _ => .stuck e

/--
The head step of the call `e` of member `m` (as a dispatch table gives it) with receiver `v` and
arguments `vs`, in state `σ` (see `HeadStep.methodCall` and `HeadStep.superCall`), whose static type
is `T`. If there is none, the result is stuck at `e`.
-/
@[expose]
public def memberCallStep (e : LoweredExpr) (m : Option Member) (v : Value) (vs : List Value)
    (T : τ) (σ : State) : StepResult :=
  match m with
  | some (.proc key holder) =>
    match P.members key with
    | some d =>
      if d.params.length = vs.length then
        let r := σ.allocAll ((v :: vs).map Cell.val)
        .next (.frame (P.memberBody key holder (d.this :: d.params) d.body r.1) T) r.2
      else .stuck e
    | none => .stuck e
  | _ => .stuck e

/--
The head step of the method call `e`, which is `.methodCall (.val v) name (vs.map .val) T`, in state
`σ`, once its arguments have evaluated to `vs` (see `HeadStep.methodCall`). If there is none, the
result is stuck at `e`.
-/
@[expose]
public def methodCallStep (e : LoweredExpr) (v : Value) (name : String) (vs : List Value) (T : τ)
    (σ : State) : StepResult :=
  match σ.object? v with
  | some (k, _) => memberCallStep e (P.dispatch k name) v vs T σ
  | none => .stuck e

/--
The head step of the super method call `e`, which is
`.superCall (.val v) name slot (vs.map .val) T`, in state `σ`, once its arguments have evaluated to
`vs` (see `HeadStep.superCall`). If there is none, the result is stuck at `e`.
-/
@[expose]
public def superCallStep (e : LoweredExpr) (v : Value) (name : String) (slot : Option String)
    (vs : List Value) (T : τ) (σ : State) : StepResult :=
  match slot with
  | some s => memberCallStep e (P.dispatch s name) v vs T σ
  | none => .stuck e

omit [RtSubChecker τ] P in
/--
The head step of the string concatenation `e`, which is `.concat (vs.map .val)`, in state `σ`, once
its parts have evaluated to `vs` (see `HeadStep.concat`). If there is none (a part has no string
form), the result is stuck at `e`.
-/
@[expose]
public def concatStep (e : LoweredExpr) (vs : List Value) (σ : State) : StepResult :=
  match vs.mapM σ.stringPart? with
  | some cus => .next (.val (.obj σ.fresh)) (σ.alloc (.string cus.flatten))
  | none => .stuck e

/--
The step of an expression whose operand in evaluation position is `m`, if `m` has completed
abruptly: if `m` has thrown, returned or broken out of a labeled statement, propagating it outward
(see `HeadStep.bubbleException`, `HeadStep.bubbleReturn` and `HeadStep.bubbleBreak`), and otherwise
`r`. (So the expression's context item must not be one that handles returns or breaks.)
-/
@[expose]
public def propagate (m : LoweredExpr) (σ : State) (r : StepResult) : StepResult :=
  match m with
  | .throwing v => .next (.throwing v) σ
  | .returning v => .next (.returning v) σ
  | .breaking l => .next (.breaking l) σ
  | _ => r

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
  | .letIn v (.val w) m₂ => .next (m₂.resolve v σ.fresh) (σ.alloc (.val w))
  | .constant c =>
    match σ.constant? c with
    | some (v, σ') => .next (.val v) σ'
    | none => .stuck e
  | .concat parts => headStepArgs e parts σ (concatStep e · σ)
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
    match σ.object? v with
    | some (k, fs) =>
      match P.dispatch k p.name with
      | some (.field iv) =>
        match fs.lookup iv with
        | some ℓf =>
          match σ.lookup ℓf with
          | some (.val w) => promotionCheck fuel σ w T e (.next (.val w) σ)
          | _ => .stuck e
        | none => .stuck e
      | some (.proc key holder) =>
        match P.members key with
        | some d =>
          if d.params.length = 0 then
            let r := σ.allocAll ([v].map Cell.val)
            .next (.checkPromotion T (.frame (P.memberBody key holder (d.this :: d.params) d.body
              r.1) T)) r.2
          else .stuck e
        | none => .stuck e
      | none => .stuck e
    | none => .stuck e
  | .variableSetAt x ℓ (.val w) =>
    -- Inspect the cell before updating it, so that the update can be done in place.
    match σ.lookup ℓ with
    | some (.val _) => if x.isFinal then .stuck e else .next (.val w) (σ.update ℓ (.val w))
    | some .uninit => .next (.val w) (σ.update ℓ (.val w))
    | _ => .stuck e
  | .call f args T => headStepArgs e args σ (callStep e f · T σ)
  | .ret (.val v) => .next (.returning v) σ
  | .frame (.returning v) _ => .next (.val v) σ
  | .frame (.val _) _ => .next (.val .null) σ
  | .check kind (.val v) =>
    match kind.holds v with
    | true => .next (.val .null) σ
    | false => .next (.throwing (.error .expectFailed)) σ
  | .checkEq (.val v₁) (.val v₂) =>
    match σ.primEq? v₁ v₂ with
    | some true => .next (.val .null) σ
    | some false => .next (.throwing (.error .expectFailed)) σ
    | none => .stuck e
  | .loop m => .next (.seq m (.loop m)) σ
  | .labeled _ (.val _) => .next (.val .null) σ
  | .labeled l (.breaking l') => if l' = l then .next (.val .null) σ else .next (.breaking l') σ
  | .brk l => .next (.breaking l) σ
  | .intBin op (some mode) (.val (.int n₁)) (.val (.int n₂)) =>
    match op.eval mode n₁ n₂ with
    | some v => .next (.val v) σ
    | none => .stuck e
  | .intNeg (some mode) (.val (.int n)) =>
    match mode.arith (-n) with
    | some k => .next (.val (.int k)) σ
    | none => .stuck e
  | .primEq (.val v₁) (.val v₂) =>
    match σ.primEq? v₁ v₂ with
    | some b => .next (.val (.bool b)) σ
    | none => .stuck e
  | .new k args _ => headStepArgs e args σ (newStep e k · σ)
  | .initCtor (.val v) k args => headStepArgs e args σ (initCtorStep e v k · σ)
  | .ctorRun ℓ k vs =>
    match P.constructors k with
    | some d =>
      if d.params.length = vs.length then
        let r := σ.allocAll ((Value.obj ℓ :: vs).map Cell.val)
        .next (.ctorFrame (P.memberBody k d.cls (d.this :: d.params)
          (.block (d.initializers ++ [d.body])) r.1)) r.2
      else .stuck e
    | none => .stuck e
  | .initField (.val v) name (.val w) =>
    -- Inspect the cell before updating it, so that the update can be done in place.
    match σ.object? v with
    | some (_, fs) =>
      match fs.lookup name with
      | some ℓf =>
        match σ.lookup ℓf with
        | some (.val _) => .next (.val .null) (σ.update ℓf (.val w))
        | some .uninit => .next (.val .null) (σ.update ℓf (.val w))
        | _ => .stuck e
      | none => .stuck e
    | none => .stuck e
  | .propertySet (.val v) name (.val w) =>
    match σ.object? v with
    | some (k, fs) =>
      match P.dispatch k (name ++ "=") with
      | some (.field iv) =>
        match fs.lookup iv with
        | some ℓf =>
          match σ.lookup ℓf with
          | some (.val _) => .next (.val w) (σ.update ℓf (.val w))
          | some .uninit => .next (.val w) (σ.update ℓf (.val w))
          | _ => .stuck e
        | none => .stuck e
      | some (.proc key holder) =>
        match P.members key with
        | some d =>
          if d.params.length = 1 then
            let r := σ.allocAll ([v, w].map Cell.val)
            .next (.seq (.frame (P.memberBody key holder (d.this :: d.params) d.body r.1) Γ.Null)
              (.val w)) r.2
          else .stuck e
        | none => .stuck e
      | none => .stuck e
    | none => .stuck e
  | .ctorFrame (.returning _) => .next (.val .null) σ
  | .ctorFrame (.val _) => .next (.val .null) σ
  | .methodCall (.val v) name args T => headStepArgs e args σ (methodCallStep e v name · T σ)
  | .superCall (.val v) name slot args T =>
    headStepArgs e args σ (superCallStep e v name slot · T σ)
  | .superGet (.val v) name (some s) T =>
    match P.dispatch s name with
    | some (.field iv) =>
      match σ.object? v with
      | some (_, fs) =>
        match fs.lookup iv with
        | some ℓf =>
          match σ.lookup ℓf with
          | some (.val w) => promotionCheck fuel σ w T e (.next (.val w) σ)
          | _ => .stuck e
        | none => .stuck e
      | none => .stuck e
    | some (.proc key holder) =>
      match P.members key with
      | some d =>
        if d.params.length = 0 then
          let r := σ.allocAll ([v].map Cell.val)
          .next (.checkPromotion T (.frame (P.memberBody key holder (d.this :: d.params) d.body
            r.1) T)) r.2
        else .stuck e
      | none => .stuck e
    | none => .stuck e
  | .superSet (.val v) name (some s) (.val w) =>
    match P.dispatch s (name ++ "=") with
    | some (.field iv) =>
      match σ.object? v with
      | some (_, fs) =>
        match fs.lookup iv with
        | some ℓf =>
          match σ.lookup ℓf with
          | some (.val _) => .next (.val w) (σ.update ℓf (.val w))
          | some .uninit => .next (.val w) (σ.update ℓf (.val w))
          | _ => .stuck e
        | none => .stuck e
      | none => .stuck e
    | some (.proc key holder) =>
      match P.members key with
      | some d =>
        if d.params.length = 1 then
          let r := σ.allocAll ([v, w].map Cell.val)
          .next (.seq (.frame (P.memberBody key holder (d.this :: d.params) d.body r.1) Γ.Null)
            (.val w)) r.2
        else .stuck e
      | none => .stuck e
    | none => .stuck e
  | .checkPromotion T (.val w) => promotionCheck fuel σ w T e (.next (.val w) σ)
  | .identical (.val v₁) (.val v₂) =>
    match Value.identical? v₁ v₂ with
    | some b => .next (.val (.bool b)) σ
    | none => .stuck e
  -- The remaining cases propagate an abrupt completion out of the operand in evaluation position
  -- (whose other cases are above).
  | .nullCheck m => propagate m σ (.stuck e)
  | .as m _ => propagate m σ (.stuck e)
  | .is m _ => propagate m σ (.stuck e)
  | .cond m _ _ _ => propagate m σ (.stuck e)
  | .propertyGet m _ _ => propagate m σ (.stuck e)
  | .seq m _ => propagate m σ (.stuck e)
  | .variableSetAt _ _ m => propagate m σ (.stuck e)
  | .ret m => propagate m σ (.stuck e)
  -- The body of a running call or constructor handles returns, and a break gets stuck there.
  | .frame (.throwing v) _ => .next (.throwing v) σ
  | .check _ m => propagate m σ (.stuck e)
  | .checkEq (.val _) m => propagate m σ (.stuck e)
  | .checkEq m _ => propagate m σ (.stuck e)
  | .labeled _ m => propagate m σ (.stuck e)
  | .intBin _ _ (.val _) m => propagate m σ (.stuck e)
  | .intBin _ _ m _ => propagate m σ (.stuck e)
  | .intNeg _ m => propagate m σ (.stuck e)
  | .primEq (.val _) m => propagate m σ (.stuck e)
  | .primEq m _ => propagate m σ (.stuck e)
  | .initCtor m _ _ => propagate m σ (.stuck e)
  | .initField (.val _) _ m => propagate m σ (.stuck e)
  | .initField m _ _ => propagate m σ (.stuck e)
  | .propertySet (.val _) _ m => propagate m σ (.stuck e)
  | .propertySet m _ _ => propagate m σ (.stuck e)
  | .ctorFrame (.throwing v) => .next (.throwing v) σ
  | .methodCall m _ _ _ => propagate m σ (.stuck e)
  | .superCall m _ _ _ _ => propagate m σ (.stuck e)
  | .superGet m _ _ _ => propagate m σ (.stuck e)
  | .superSet (.val _) _ _ m => propagate m σ (.stuck e)
  | .superSet m _ _ _ => propagate m σ (.stuck e)
  | .checkPromotion _ m => propagate m σ (.stuck e)
  | .identical (.val _) m => propagate m σ (.stuck e)
  | .identical m _ => propagate m σ (.stuck e)
  | .letIn _ m _ => propagate m σ (.stuck e)
  | _ => .stuck e


/-! ## Agreement with the semantics -/

/--
`Converges f r`: as a function of the budget of fuel, `f` gives `r` once the budget is large
enough, and runs out of fuel otherwise.
-/
@[expose]
public def Converges (f : Nat → StepResult) (r : StepResult) : Prop :=
  (∀ fuel, f fuel = r ∨ f fuel = .outOfFuel) ∧ ∃ n, ∀ fuel, n ≤ fuel → f fuel = r

omit Γ [RtSubChecker τ] P in
/-- If `f` gives `r` regardless of its budget of fuel (`h`), then `f` converges to `r`. -/
public theorem Converges.of_eq {f : Nat → StepResult} {r : StepResult} (h : ∀ fuel, f fuel = r) :
    Converges f r :=
  ⟨fun fuel => .inl (h fuel), 0, fun fuel _ => h fuel⟩

omit Γ [RtSubChecker τ] P in
/--
If two functions of fuel `f` and `g` always produce the same result (`h`), and `g` converges to `r`
(`hg`), then `f` does too.
-/
public theorem Converges.congr {f g : Nat → StepResult} {r : StepResult}
    (h : ∀ fuel, f fuel = g fuel) (hg : Converges g r) : Converges f r :=
  funext h ▸ hg

omit Γ [RtSubChecker τ] P in
/--
Applying `g` to the expression that each step goes to preserves convergence: if `f` converges to
`r` (`h`), then `f` followed by `StepResult.map g` converges to `r.map g`.
-/
public theorem Converges.map {f : Nat → StepResult} {r : StepResult} (g : LoweredExpr → LoweredExpr)
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
public theorem withCheck_converges {S T : τ} {b : Bool} {k : Bool → StepResult} {r : StepResult}
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
public theorem withCheck_diverge {fuel : Nat} {S T : τ} {k : Bool → StepResult}
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
public theorem withCheck_eq_next {fuel : Nat} {S T : τ} {k : Bool → StepResult} {e : LoweredExpr}
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
public theorem promotionCheck_converges {σ : State} {v : Value} {T : τ} {redex : LoweredExpr}
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
public theorem promotionCheck_eq_next {fuel : Nat} {σ σ' : State} {v : Value} {T : τ}
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
public theorem headStep_complete {e e' : LoweredExpr} {σ σ' : State} (h : HeadStep e σ e' σ') :
    Converges (headStep · e σ) (.next e' σ') ∨
      (e' = e ∧ σ' = σ ∧ ∀ fuel, headStep fuel e σ = .outOfFuel) := by
  cases h with
  | null | bool | int | declare | blockNil | blockDeclare | seq | nullCheckNull | condTrue
  | condFalse | ret | frameReturning | frameVal | loop | labeledVal | brk | ctorFrameReturning
  | ctorFrameVal | letIn =>
    exact .inl (Converges.of_eq fun _ => rfl)
  | call hf hlen =>
    exact .inl (Converges.of_eq fun _ => by
      simp [headStep.eq_def, headStepArgs, callStep, hf, hlen])
  | new hk hc =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, headStepArgs, newStep, hk, hc])
  | ctorRun hk hlen => exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, hk, hlen])
  | initCtor =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, headStepArgs, initCtorStep])
  | @initField v w name k fs ℓf c σ ho hf hℓf hc =>
    cases c
    case object | string => simp [Cell.isVar] at hc
    all_goals exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, ho, hf, hℓf])
  | @propertySetField v w name k iv fs ℓf c σ ho hd hf hℓf hc =>
    cases c
    case object | string => simp [Cell.isVar] at hc
    all_goals exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, ho, hd, hf, hℓf])
  | checkPass h | checkFail h | checkEqPass h | checkEqFail h | intBin h | intNeg h
  | primEq h | identical h | constant h =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, h])
  | concat h =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, headStepArgs, concatStep, h])
  | @blockCons m ms σ h =>
    cases m
    case declare v T startsNull => exact absurd rfl (h v T startsNull)
    all_goals exact .inl (Converges.of_eq fun _ => rfl)
  | @varAt x T ℓ v σ hℓ hv =>
    exact .inl (Converges.congr (fun fuel => by simp [headStep.eq_def, hℓ])
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
  | @propertyGetField v w p T k iv fs ℓf σ ho hd hf hw hc =>
    exact .inl (Converges.congr (fun fuel => by simp [headStep.eq_def, ho, hd, hf, hw])
      (promotionCheck_converges (redex := .propertyGet (.val v) p T) hc _))
  | propertyGetGetter ho hd hm hlen =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, ho, hd, hm, hlen])
  | propertySetSetter ho hd hm hlen =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, ho, hd, hm, hlen])
  | methodCall ho hd hm hlen =>
    exact .inl (Converges.of_eq fun _ => by
      simp [headStep.eq_def, headStepArgs, methodCallStep, memberCallStep, ho, hd, hm, hlen])
  | superCall hd hm hlen =>
    exact .inl (Converges.of_eq fun _ => by
      simp [headStep.eq_def, headStepArgs, superCallStep, memberCallStep, hd, hm, hlen])
  | @superGetField v w name s k iv T fs ℓf σ hd ho hf hw hc =>
    exact .inl (Converges.congr (fun fuel => by simp [headStep.eq_def, ho, hd, hf, hw])
      (promotionCheck_converges (redex := .superGet (.val v) name (some s) T) hc _))
  | superGetGetter hd hm hlen =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, hd, hm, hlen])
  | @superSetField v w name s k iv fs ℓf c σ hd ho hf hℓf hc =>
    cases c
    case object | string => simp [Cell.isVar] at hc
    all_goals exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, ho, hd, hf, hℓf])
  | superSetSetter hd hm hlen =>
    exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, hd, hm, hlen])
  | @checkPromotion w T σ hc =>
    exact .inl (Converges.congr (fun fuel => rfl)
      (promotionCheck_converges (redex := .checkPromotion T (.val w)) hc _))
  | @variableSetAt x ℓ w c σ hℓ hc hfin =>
    cases c
    case object | string => simp [Cell.isVar] at hc
    case val u =>
      cases hx : x.isFinal
      · exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, hℓ, hx])
      · exact absurd (hfin hx) nofun
    case uninit => exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def, hℓ])
  | @bubbleException Ki v σ =>
    cases Ki
    case call f vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .throwing v :: ms) (by simp)])
    case new k vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .throwing v :: ms) (by simp)])
    case initCtorArgs u k vs ms =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .throwing v :: ms) (by simp)])
    case methodCallArgs u name vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .throwing v :: ms) (by simp)])
    case superCallArgs u name slot vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .throwing v :: ms) (by simp)])
    case concat vs ms =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .throwing v :: ms) (by simp)])
    all_goals exact .inl (Converges.of_eq fun _ => by
      -- An integer operator's (or `super` assignment's) propagation case is only reached once
      -- `headStep` has seen that it doesn't match the cases before it, which depend on its mode
      -- (or slot) and first operand.
      first
        | rfl
        | (cases ‹Option IntMode› <;> first | rfl | (cases ‹Value› <;> rfl))
        | (cases ‹Option String› <;> rfl))
  | @bubbleReturn Ki v σ hKi =>
    cases Ki
    case call f vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .returning v :: ms) (by simp)])
    case new k vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .returning v :: ms) (by simp)])
    case initCtorArgs u k vs ms =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .returning v :: ms) (by simp)])
    case methodCallArgs u name vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .returning v :: ms) (by simp)])
    case superCallArgs u name slot vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .returning v :: ms) (by simp)])
    case concat vs ms =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .returning v :: ms) (by simp)])
    case frame T => simp [EctxItem.handlesReturn] at hKi
    case ctorFrame => simp [EctxItem.handlesReturn] at hKi
    all_goals exact .inl (Converges.of_eq fun _ => by
      -- An integer operator's (or `super` assignment's) propagation case is only reached once
      -- `headStep` has seen that it doesn't match the cases before it, which depend on its mode
      -- (or slot) and first operand.
      first
        | rfl
        | (cases ‹Option IntMode› <;> first | rfl | (cases ‹Value› <;> rfl))
        | (cases ‹Option String› <;> rfl))
  | @bubbleBreak Ki l σ hKi hret =>
    cases Ki
    case call f vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .breaking l :: ms) (by simp)])
    case new k vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .breaking l :: ms) (by simp)])
    case initCtorArgs u k vs ms =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .breaking l :: ms) (by simp)])
    case methodCallArgs u name vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .breaking l :: ms) (by simp)])
    case superCallArgs u name slot vs ms T =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .breaking l :: ms) (by simp)])
    case concat vs ms =>
      exact .inl (Converges.of_eq fun _ => by
        simp [EctxItem.fill, headStep.eq_def, headStepArgs,
          LoweredExpr.splitVals_map_val_append vs (ms := .breaking l :: ms) (by simp)])
    case frame T => simp [EctxItem.handlesReturn] at hret
    case ctorFrame => simp [EctxItem.handlesReturn] at hret
    case labeled l' =>
      have hne : l ≠ l' := fun h => by subst h; simp [EctxItem.handlesBreak] at hKi
      exact .inl (Converges.of_eq fun _ => by simp [EctxItem.fill, headStep.eq_def, hne])
    all_goals exact .inl (Converges.of_eq fun _ => by
      -- An integer operator's (or `super` assignment's) propagation case is only reached once
      -- `headStep` has seen that it doesn't match the cases before it, which depend on its mode
      -- (or slot) and first operand.
      first
        | rfl
        | (cases ‹Option IntMode› <;> first | rfl | (cases ‹Value› <;> rfl))
        | (cases ‹Option String› <;> rfl))
  | labeledBreak => exact .inl (Converges.of_eq fun _ => by simp [headStep.eq_def])

omit [RtSubChecker τ] in
/--
Soundness of `headStepArgs`, for an expression `E args` whose operands still to be considered are
`args`. Suppose that:
- `mk vs ms` is the context item for the operand after `vs`, followed by `ms` (`hmk`);
- no such item handles returns (`hret`) or breaks (`hbrk`); and
- once the operands have evaluated to `vs`, every step that `k vs` finds is a head step of
  `E (vs.map .val)` (`hk`).

Then every step that `headStepArgs` finds for `E args` (`h`) is a head step
(`HeadStep (E args) σ e' σ'`).
-/
public theorem headStepArgs_sound {E : List LoweredExpr → LoweredExpr}
    {mk : List Value → List LoweredExpr → EctxItem}
    (hmk : ∀ vs m ms, (mk vs ms).fill m = E (vs.map .val ++ m :: ms))
    (hret : ∀ vs ms, (mk vs ms).handlesReturn = false)
    (hbrk : ∀ l vs ms, (mk vs ms).handlesBreak l = false) {args : List LoweredExpr}
    {k : List Value → StepResult} {e' : LoweredExpr} {σ σ' : State}
    (hk : ∀ vs, k vs = .next e' σ' → HeadStep (E (vs.map .val)) σ e' σ')
    (h : headStepArgs (E args) args σ k = .next e' σ') : HeadStep (E args) σ e' σ' := by
  have hargs := LoweredExpr.splitVals_append args
  unfold headStepArgs at h
  split at h
  · next vs heq =>
    rw [heq] at hargs
    simp only [List.append_nil] at hargs
    subst hargs
    exact hk vs h
  · next vs v ms heq =>
    rw [heq] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := StepResult.next.inj h
    rw [← hmk]
    exact .bubbleException
  · next vs v ms heq =>
    rw [heq] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := StepResult.next.inj h
    rw [← hmk]
    exact .bubbleReturn (hret _ _)
  · next vs l ms heq =>
    rw [heq] at hargs
    subst hargs
    obtain ⟨rfl, rfl⟩ := StepResult.next.inj h
    rw [← hmk]
    exact .bubbleBreak (hbrk _ _ _) (hret _ _)
  · cases h

omit [RtSubChecker τ] in
/--
Soundness of `headStep` for a call: every step that it finds for the call `.call f args T` (`h`)
is a head step (`HeadStep (.call f args T) σ e' σ'`).
-/
public theorem headStepCall_sound {f : String} {args : List LoweredExpr} {T : τ} {e' : LoweredExpr}
    {σ σ' : State}
    (h : headStepArgs (.call f args T) args σ (callStep (.call f args T) f · T σ) = .next e' σ') :
    HeadStep (.call f args T) σ e' σ' := by
  refine headStepArgs_sound (E := (.call f · T)) (mk := (.call f · · T)) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun vs hk => ?_) h
  unfold callStep at hk
  split at hk
  · next d hf =>
    split at hk
    · next hlen =>
      obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
      exact .call hf hlen
    · cases hk
  · cases hk

omit [RtSubChecker τ] in
/--
Soundness of `headStep` for an instance creation: every step that it finds for `.new k args T`
(`h`) is a head step (`HeadStep (.new k args T) σ e' σ'`).
-/
public theorem headStepNew_sound {k : String} {args : List LoweredExpr} {T : τ} {e' : LoweredExpr}
    {σ σ' : State}
    (h : headStepArgs (.new k args T) args σ (newStep (.new k args T) k · σ) = .next e' σ') :
    HeadStep (.new k args T) σ e' σ' := by
  refine headStepArgs_sound (E := (.new k · T)) (mk := (.new k · · T)) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun vs hk => ?_) h
  unfold newStep at hk
  split at hk
  · next d hd =>
    split at hk
    · next c hc =>
      obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
      exact .new hd hc
    · cases hk
  · cases hk

omit [RtSubChecker τ] in
/--
Soundness of `headStep` for a `super(args)` or `this(args)` call: every step that it finds for
`.initCtor (.val v) k args` (`h`) is a head step (`HeadStep (.initCtor (.val v) k args) σ e' σ'`).
-/
public theorem headStepInitCtor_sound {v : Value} {k : String} {args : List LoweredExpr}
    {e' : LoweredExpr} {σ σ' : State}
    (h : headStepArgs (.initCtor (.val v) k args) args σ
      (initCtorStep (.initCtor (.val v) k args) v k · σ) = .next e' σ') :
    HeadStep (.initCtor (.val v) k args) σ e' σ' := by
  refine headStepArgs_sound (E := (.initCtor (.val v) k ·)) (mk := (.initCtorArgs v k · ·))
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun vs hk => ?_) h
  unfold initCtorStep at hk
  split at hk
  · obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
    exact .initCtor
  · cases hk

omit [RtSubChecker τ] in
/--
Soundness of `headStep` for a method call: every step that it finds for
`.methodCall (.val v) name args T` (`h`) is a head step
(`HeadStep (.methodCall (.val v) name args T) σ e' σ'`).
-/
public theorem headStepMethodCall_sound {v : Value} {name : String} {args : List LoweredExpr}
    {T : τ} {e' : LoweredExpr} {σ σ' : State}
    (h : headStepArgs (.methodCall (.val v) name args T) args σ
      (methodCallStep (.methodCall (.val v) name args T) v name · T σ) = .next e' σ') :
    HeadStep (.methodCall (.val v) name args T) σ e' σ' := by
  refine headStepArgs_sound (E := (.methodCall (.val v) name · T))
    (mk := (.methodCallArgs v name · · T)) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
    (fun vs hk => ?_) h
  unfold methodCallStep memberCallStep at hk
  repeat' split at hk
  all_goals first
    | (cases hk; done)
    | (obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
       exact .methodCall ‹_› ‹_› ‹_› ‹_›)

omit [RtSubChecker τ] in
/--
Soundness of `headStep` for a super method call: every step that it finds for
`.superCall (.val v) name slot args T` (`h`) is a head step
(`HeadStep (.superCall (.val v) name slot args T) σ e' σ'`).
-/
public theorem headStepSuperCall_sound {v : Value} {name : String} {slot : Option String}
    {args : List LoweredExpr} {T : τ} {e' : LoweredExpr} {σ σ' : State}
    (h : headStepArgs (.superCall (.val v) name slot args T) args σ
      (superCallStep (.superCall (.val v) name slot args T) v name slot · T σ) = .next e' σ') :
    HeadStep (.superCall (.val v) name slot args T) σ e' σ' := by
  refine headStepArgs_sound (E := (.superCall (.val v) name slot · T))
    (mk := (.superCallArgs v name slot · · T)) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun vs hk => ?_) h
  unfold superCallStep memberCallStep at hk
  repeat' split at hk
  all_goals first
    | (cases hk; done)
    | (obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
       exact .superCall ‹_› ‹_› ‹_›)

omit [RtSubChecker τ] in
/--
Soundness of `headStep` for a string concatenation: every step that it finds for `.concat parts`
(`h`) is a head step (`HeadStep (.concat parts) σ e' σ'`).
-/
public theorem headStepConcat_sound {parts : List LoweredExpr} {e' : LoweredExpr} {σ σ' : State}
    (h : headStepArgs (.concat parts) parts σ (concatStep (.concat parts) · σ) = .next e' σ') :
    HeadStep (.concat parts) σ e' σ' := by
  refine headStepArgs_sound (E := .concat) (mk := .concat) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun vs hk => ?_) h
  unfold concatStep at hk
  split at hk
  · obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
    exact .concat ‹_›
  · cases hk

omit Γ P [RtSubChecker τ] in
/--
`headStepArgs` is only ever stuck at the expression it was given, if its continuation `k` is
(`hk`): if it is stuck at `redex` (`h`), then `redex = e`.
-/
public theorem headStepArgs_eq_stuck {e : LoweredExpr} {args : List LoweredExpr} {σ : State}
    {k : List Value → StepResult} {redex : LoweredExpr}
    (hk : ∀ vs, k vs = .stuck redex → redex = e) (h : headStepArgs e args σ k = .stuck redex) :
    redex = e := by
  unfold headStepArgs at h
  split at h
  · exact hk _ h
  all_goals first
    | (cases h; done)
    | (simp only [StepResult.stuck.injEq] at h; exact h.symm)

omit [RtSubChecker τ] in
/-- `callStep` is only ever stuck at the expression it was given (`h`; `redex = e`). -/
public theorem callStep_eq_stuck {e : LoweredExpr} {f : String} {vs : List Value} {T : τ}
    {σ : State} {redex : LoweredExpr} (h : callStep e f vs T σ = .stuck redex) : redex = e := by
  unfold callStep at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [StepResult.stuck.injEq] at h; exact h.symm)

omit Γ [RtSubChecker τ] in
/-- `newStep` is only ever stuck at the expression it was given (`h`; `redex = e`). -/
public theorem newStep_eq_stuck {e : LoweredExpr} {k : String} {vs : List Value} {σ : State}
    {redex : LoweredExpr} (h : newStep e k vs σ = .stuck redex) : redex = e := by
  unfold newStep at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [StepResult.stuck.injEq] at h; exact h.symm)

omit Γ [RtSubChecker τ] P in
/-- `initCtorStep` is only ever stuck at the expression it was given (`h`; `redex = e`). -/
public theorem initCtorStep_eq_stuck {e : LoweredExpr} {v : Value} {k : String} {vs : List Value}
    {σ : State} {redex : LoweredExpr} (h : initCtorStep e v k vs σ = .stuck redex) :
    redex = e := by
  unfold initCtorStep at h
  split at h
  · cases h
  · simp only [StepResult.stuck.injEq] at h
    exact h.symm

omit [RtSubChecker τ] in
/-- `methodCallStep` is only ever stuck at the expression it was given (`h`; `redex = e`). -/
public theorem methodCallStep_eq_stuck {e : LoweredExpr} {v : Value} {name : String}
    {vs : List Value} {T : τ} {σ : State} {redex : LoweredExpr}
    (h : methodCallStep e v name vs T σ = .stuck redex) :
    redex = e := by
  unfold methodCallStep memberCallStep at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [StepResult.stuck.injEq] at h; exact h.symm)

omit [RtSubChecker τ] in
/-- `superCallStep` is only ever stuck at the expression it was given (`h`; `redex = e`). -/
public theorem superCallStep_eq_stuck {e : LoweredExpr} {v : Value} {name : String}
    {slot : Option String} {vs : List Value} {T : τ} {σ : State} {redex : LoweredExpr}
    (h : superCallStep e v name slot vs T σ = .stuck redex) : redex = e := by
  unfold superCallStep memberCallStep at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [StepResult.stuck.injEq] at h; exact h.symm)

omit Γ [RtSubChecker τ] P in
/-- `concatStep` is only ever stuck at the expression it was given (`h`; `redex = e`). -/
public theorem concatStep_eq_stuck {e : LoweredExpr} {vs : List Value} {σ : State}
    {redex : LoweredExpr} (h : concatStep e vs σ = .stuck redex) : redex = e := by
  unfold concatStep at h
  split at h
  · cases h
  · simp only [StepResult.stuck.injEq] at h
    exact h.symm

/--
Soundness of `headStep`: every step that it finds (`h`) is a head step (`HeadStep e σ e' σ'`).
-/
public theorem headStep_sound {fuel : Nat} {e e' : LoweredExpr} {σ σ' : State}
    (h : headStep fuel e σ = .next e' σ') : HeadStep e σ e' σ' := by
  unfold headStep propagate at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (obtain ⟨rfl, rfl⟩ := StepResult.next.inj h
       first
         | (constructor <;> assumption)
         | exact .variableSetAt ‹_› rfl (by intro _; rfl)
         | exact .variableSetAt ‹_› rfl (by simp_all)
         | exact .initField ‹_› ‹_› ‹_› rfl
         | exact .propertySetField ‹_› ‹_› ‹_› ‹_› rfl
         | exact .superSetField ‹_› ‹_› ‹_› ‹_› rfl
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
         | exact .bubbleException (Ki := .intBinL _ _ _)
         | exact .bubbleException (Ki := .intBinR _ _ _)
         | exact .bubbleException (Ki := .intNeg _)
         | exact .bubbleException (Ki := .primEqL _)
         | exact .bubbleException (Ki := .primEqR _)
         | exact .bubbleException (Ki := .initCtorRecv _ _)
         | exact .bubbleException (Ki := .initFieldL _ _)
         | exact .bubbleException (Ki := .initFieldR _ _)
         | exact .bubbleException (Ki := .propertySetL _ _)
         | exact .bubbleException (Ki := .propertySetR _ _)
         | exact .bubbleException (Ki := .ctorFrame)
         | exact .bubbleException (Ki := .methodCallRecv _ _ _)
         | exact .bubbleException (Ki := .superCallRecv _ _ _ _)
         | exact .bubbleException (Ki := .superGet _ _ _)
         | exact .bubbleException (Ki := .superSetL _ _ _)
         | exact .bubbleException (Ki := .superSetR _ _ _)
         | exact .bubbleException (Ki := .checkPromotion _)
         | exact .bubbleException (Ki := .identicalL _)
         | exact .bubbleException (Ki := .identicalR _)
         | exact .bubbleException (Ki := .letIn _ _)
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
         | exact .bubbleReturn (Ki := .intBinL _ _ _) rfl
         | exact .bubbleReturn (Ki := .intBinR _ _ _) rfl
         | exact .bubbleReturn (Ki := .intNeg _) rfl
         | exact .bubbleReturn (Ki := .primEqL _) rfl
         | exact .bubbleReturn (Ki := .primEqR _) rfl
         | exact .bubbleReturn (Ki := .initCtorRecv _ _) rfl
         | exact .bubbleReturn (Ki := .initFieldL _ _) rfl
         | exact .bubbleReturn (Ki := .initFieldR _ _) rfl
         | exact .bubbleReturn (Ki := .propertySetL _ _) rfl
         | exact .bubbleReturn (Ki := .propertySetR _ _) rfl
         | exact .bubbleReturn (Ki := .methodCallRecv _ _ _) rfl
         | exact .bubbleReturn (Ki := .superCallRecv _ _ _ _) rfl
         | exact .bubbleReturn (Ki := .superGet _ _ _) rfl
         | exact .bubbleReturn (Ki := .superSetL _ _ _) rfl
         | exact .bubbleReturn (Ki := .superSetR _ _ _) rfl
         | exact .bubbleReturn (Ki := .checkPromotion _) rfl
         | exact .bubbleReturn (Ki := .identicalL _) rfl
         | exact .bubbleReturn (Ki := .identicalR _) rfl
         | exact .bubbleReturn (Ki := .letIn _ _) rfl
         | exact .bubbleBreak (Ki := .intBinL _ _ _) rfl rfl
         | exact .bubbleBreak (Ki := .intBinR _ _ _) rfl rfl
         | exact .bubbleBreak (Ki := .intNeg _) rfl rfl
         | exact .bubbleBreak (Ki := .primEqL _) rfl rfl
         | exact .bubbleBreak (Ki := .primEqR _) rfl rfl
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
         | exact .bubbleBreak (Ki := .initCtorRecv _ _) rfl rfl
         | exact .bubbleBreak (Ki := .initFieldL _ _) rfl rfl
         | exact .bubbleBreak (Ki := .initFieldR _ _) rfl rfl
         | exact .bubbleBreak (Ki := .propertySetL _ _) rfl rfl
         | exact .bubbleBreak (Ki := .propertySetR _ _) rfl rfl
         | exact .bubbleBreak (Ki := .methodCallRecv _ _ _) rfl rfl
         | exact .bubbleBreak (Ki := .superCallRecv _ _ _ _) rfl rfl
         | exact .bubbleBreak (Ki := .superGet _ _ _) rfl rfl
         | exact .bubbleBreak (Ki := .superSetL _ _ _) rfl rfl
         | exact .bubbleBreak (Ki := .superSetR _ _ _) rfl rfl
         | exact .bubbleBreak (Ki := .checkPromotion _) rfl rfl
         | exact .bubbleBreak (Ki := .identicalL _) rfl rfl
         | exact .bubbleBreak (Ki := .identicalR _) rfl rfl
         | exact .bubbleBreak (Ki := .letIn _ _) rfl rfl
         | (subst_vars; exact .labeledBreak)
         | (rename_i hne
            exact .bubbleBreak (Ki := .labeled _)
              (by simp only [EctxItem.handlesBreak, beq_eq_false_iff_ne, ne_eq]
                  exact fun h => hne h.symm) rfl))
    | exact headStepCall_sound h
    | exact headStepNew_sound h
    | exact headStepInitCtor_sound h
    | exact headStepMethodCall_sound h
    | exact headStepSuperCall_sound h
    | exact headStepConcat_sound h
    -- A case of `propagate` that an earlier case of `headStep` has already covered (a labeled
    -- statement's own break).
    | (exfalso; simp_all)
    | (obtain ⟨hc, hr⟩ := promotionCheck_eq_next h
       obtain ⟨rfl, rfl⟩ := StepResult.next.inj hr
       first
         | exact .varAt ‹_› hc
         | exact .propertyGetField ‹_› ‹_› ‹_› ‹_› hc
         | exact .superGetField ‹_› ‹_› ‹_› ‹_› hc
         | exact .checkPromotion hc)
    | (obtain ⟨b, hb, hk⟩ := withCheck_eq_next h
       first
         | (obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
            exact .is ‹_› hb)
         | (cases b <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hk <;>
            obtain ⟨rfl, rfl⟩ := StepResult.next.inj hk
            · exact .asFalse ‹_› hb
            · exact .asTrue ‹_› hb))

end DartSemantics.Interp

namespace DartSemantics

open DartLang

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "State" => State (τ := τ)

/--
A run-time subtype check algorithm for any type representation, which isn't computable: it gives,
with no fuel needed, the answer that `RtSub` allows, if there is one (it allows at most one,
`rtSub_unique`). It exists so that facts about the semantics that hold for every type
representation can be proved with the interpreter (see `HeadStep.deterministic`).
-/
@[instance_reducible]
noncomputable def classicalRtSubChecker : RtSubChecker τ where
  check fuel S T := open Classical in
    if h : ∃ b, RtSub S T b then some (h.choose, fuel) else none
  check_fuel_le {fuel S T b fuel'} h := by
    split at h
    · cases h
      exact Nat.le_refl _
    · cases h
  check_mono {fuel S T b fuel'} k h := by
    split at h
    · cases h
      simp_all
    · cases h
  check_sound {fuel S T b fuel'} h := by
    split at h
    · rename_i hb
      cases h
      exact hb.choose_spec
    · cases h
  check_complete {S T b} h := by
    have hb : ∃ b, RtSub S T b := ⟨b, h⟩
    refine ⟨0, 0, ?_⟩
    simp only [hb, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq, and_true]
    exact rtSub_unique hb.choose_spec h

variable [SemanticParams τ]

/--
The semantics is deterministic: an expression takes at most one head step. If `e`, in state `σ`,
takes head steps to `e₁` in state `σ₁` (`h₁`) and to `e₂` in state `σ₂` (`h₂`), they're the same
expression (`e₁ = e₂`) and the same state (`σ₁ = σ₂`).

The interpreter's head step (`Interp.headStep`) finds both steps (`Interp.headStep_complete`), and
it's a function, so they're the same. The interpreter needs a run-time subtype check algorithm, so
the proof uses one that exists for every type representation (`classicalRtSubChecker`). A step
that the interpreter can't find (one that a check that doesn't terminate takes, forever) leaves
the expression and the state unchanged, and it's the only step that the expression takes.
-/
public theorem HeadStep.deterministic {e e₁ e₂ : LoweredExpr} {σ σ₁ σ₂ : State}
    (h₁ : HeadStep e σ e₁ σ₁) (h₂ : HeadStep e σ e₂ σ₂) : e₁ = e₂ ∧ σ₁ = σ₂ := by
  let _ : RtSubChecker τ := classicalRtSubChecker
  rcases Interp.headStep_complete h₁ with c₁ | ⟨rfl, rfl, d₁⟩ <;>
    rcases Interp.headStep_complete h₂ with c₂ | ⟨rfl, rfl, d₂⟩
  · cases Interp.Converges.unique c₁ c₂
    exact ⟨rfl, rfl⟩
  · obtain ⟨-, n, hn⟩ := c₁
    cases (hn n (Nat.le_refl _)).symm.trans (d₂ n)
  · obtain ⟨-, n, hn⟩ := c₂
    cases (hn n (Nat.le_refl _)).symm.trans (d₁ n)
  · exact ⟨rfl, rfl⟩

end DartSemantics
