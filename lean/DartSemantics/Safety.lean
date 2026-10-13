module
public import DartSemantics.Compat

/-!
# Safety

The safety theorem for the semantic typing judgment: a semantically well-typed expression,
started in a state where the facts of its context hold, doesn't get stuck, and if it completes
normally, its value is consistent with its static type. It follows from adequacy (see
`GhostState.lean`).

When `SemanticParams.promotionChecks` is `PromotionChecks.verify`, a promotion check that fails
gets stuck, so the theorem says, in particular, that every promotion the expression relies on is
sound. The theorem holds for every choice of `SemanticParams`.
-/

namespace DartSemantics

open DartLang Iris Iris.BI Iris.ProgramLogic Iris.Std

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Cell" => Cell (τ := τ)
local notation "State" => State (τ := τ)
local notation "Fact" => Fact (τ := τ)
local notation "Ctx" => Ctx (τ := τ)

/--
What the safety theorem says about an outcome of an expression of static type `T`: a value it
completes normally with is the null object only if `Null` is a subtype of `T`, a boolean only if
`bool` is, and never an exception object (the model so far doesn't support catching exceptions) or
a captured continuation. (Whether an object satisfies `T` depends on the final state, which
adequacy doesn't describe.)
-/
@[expose]
public def OutcomeOk (T : τ) : DartLang.Outcome (τ := τ) → Prop
  | .normal .null => Γ.Null ≤ T
  | .normal (.bool _) => Γ.bool ≤ T
  | .normal (.obj _) => True
  | .normal (.error _) => False
  | .normal (.cont _) => False
  | .throwing _ => True

/-- Fact `f` holds in state `σ`, for the variables bound to cells by `bindings`. -/
@[expose]
public def FactHolds (σ : State) (bindings : List (Variable × Loc)) : Fact → Prop
  | .var x T => ∃ ℓ v S, bindings.lookup x = some ℓ ∧ σ.lookup ℓ = some (.val v) ∧
      σ.dynamicType v = some S ∧ S ≤ T ∧ ValOk v S
  | .field x name T => ∃ ℓ ℓo C fs ℓf w S, bindings.lookup x = some ℓ ∧
      σ.lookup ℓ = some (.val (.obj ℓo)) ∧ σ.lookup ℓo = some (.object C fs) ∧
      fs.lookup name = some ℓf ∧ σ.lookup ℓf = some (.val w) ∧ σ.dynamicType w = some S ∧
      S ≤ T ∧ ValOk w S

section

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]

omit Γ in
/--
Ownership of the cells a program starts with can be made persistent: no cell ever changes (the
model so far doesn't support assignment).
-/
theorem cellOwn_persist (ℓ : Loc) (c : Cell) :
    cellOwn (GF := GF) ℓ c ⊢ |==> ℓ ↦{.discard} c := by
  cases c with
  | object C fs =>
    simp only [cellOwn]
    iintro H
    imodintro
    iexact H
  | val v =>
    simp only [cellOwn]
    iintro H
    iapply pointsTo_persist $$ H
  | uninit =>
    simp only [cellOwn]
    iintro H
    iapply pointsTo_persist $$ H

omit Γ in
/-- Persistent ownership of every cell gives the object headers. -/
theorem objectHeaders_of_persist (σ : State) :
    ([∗map] ℓ ↦ c ∈ σ.toMap, ℓ ↦{.discard} c) ⊢ ObjectHeaders (GF := GF) σ := by
  unfold ObjectHeaders
  refine BigSepM.bigSepM_mono fun {ℓ c} _ => ?_
  cases c with
  | object C fs => exact .rfl
  | val v =>
    simp only [cellHeader]
    exact affine
  | uninit =>
    simp only [cellHeader]
    exact affine

omit Γ in
/-- Persistent ownership of every cell of state `σ` includes that of the cell at `ℓ`. -/
theorem pointsTo_of_persist {σ : State} {ℓ : Loc} {c : Cell} (h : σ.lookup ℓ = some c) :
    ([∗map] ℓ ↦ c ∈ σ.toMap, ℓ ↦{.discard} c) ⊢ (ℓ ↦{.discard} c : IProp GF) := by
  exact BigSepM.bigSepM_lookup (by rw [State.get?_toMap]; exact h)

/--
A value whose dynamic type `S` in state `σ` is a subtype of `T` (and which obeys `ValOk v S`)
satisfies `T` (`interpVal T v`), given persistent ownership of every cell of `σ`.
-/
theorem interpVal_of_persist {σ : State} {v : Value} {S T : τ} (hS : σ.dynamicType v = some S)
    (hT : S ≤ T) (hok : ValOk v S) :
    ([∗map] ℓ ↦ c ∈ σ.toMap, ℓ ↦{.discard} c) ⊢ interpVal (GF := GF) T v := by
  iintro #H
  ihave #Hdr := objectHeaders_of_persist σ $$ H
  iexists S
  isplitr
  · iapply HasDynamicType.of_headers hS $$ Hdr
  · ipureintro
    exact ⟨hT, hok⟩

/--
A fact that holds in state `σ` (`FactHolds σ bindings f`) also holds as an Iris proposition
(`interpFact bindings f`), given persistent ownership of every cell of `σ`.
-/
theorem interpFact_of_holds {σ : State} {bindings : List (Variable × Loc)} {f : Fact}
    (hf : FactHolds σ bindings f) :
    ([∗map] ℓ ↦ c ∈ σ.toMap, ℓ ↦{.discard} c) ⊢ interpFact (GF := GF) bindings f := by
  cases f with
  | var x T =>
    obtain ⟨ℓ, v, S, hl, hc, hS, hT, hok⟩ := hf
    iintro #H
    iexists ℓ, v
    isplitr
    · ipureintro
      exact hl
    isplitr
    · iapply pointsTo_of_persist hc $$ H
    · iapply interpVal_of_persist hS hT hok $$ H
  | field x name T =>
    obtain ⟨ℓ, ℓo, C, fs, ℓf, w, S, hl, hc, ho, hfs, hcf, hS, hT, hok⟩ := hf
    iintro #H
    iexists ℓ, ℓo, C, fs, ℓf, w
    isplitr
    · ipureintro
      exact ⟨hl, hfs⟩
    isplitr
    · iapply pointsTo_of_persist hc $$ H
    isplitr
    · iapply pointsTo_of_persist ho $$ H
    isplitr
    · iapply pointsTo_of_persist hcf $$ H
    · iapply interpVal_of_persist hS hT hok $$ H

/--
Completing normally with a value that satisfies `T` is consistent with `T`, in the sense of
`OutcomeOk` (which doesn't look at the state).
-/
theorem outcomeOk_of_interpVal {T : τ} {v : Value} :
    interpVal (GF := GF) T v ⊢ ⌜OutcomeOk T (.normal v)⌝ := by
  cases v with
  | null =>
    simp only [interpVal, HasDynamicType]
    iintro ⟨%S, %h, %hS, -⟩
    subst h
    ipureintro
    exact hS
  | bool b =>
    simp only [interpVal, HasDynamicType]
    iintro ⟨%S, %h, %hS, -⟩
    subst h
    ipureintro
    exact hS
  | obj ℓ =>
    iintro -
    ipureintro
    trivial
  | error e =>
    simp only [interpVal, HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim
  | cont k =>
    simp only [interpVal, HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim

end

/--
**Safety.** If expression `m` is semantically well typed (`SemTyped`), with type `T`, in context
`Δ`, and it starts in state `σ`, with its free variables bound to cells by `bindings`, such that
every fact in `Δ` holds, then it never gets stuck, and every outcome it completes with is
consistent with `T` (`OutcomeOk`).
-/
public theorem safety [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF] {Δ : Ctx}
    {m : LoweredExpr} {T : τ} {Δ' : Value → Ctx} (σ : State)
    (bindings : List (Variable × Loc)) (h : ∀ [DartGS τ .hasLC GF], SemTyped GF Δ m T Δ')
    (hσ : ∀ f ∈ Δ, FactHolds σ bindings f) :
    adequate .NotStuck (m.bindVariables bindings) σ (fun o _ => OutcomeOk T o) := by
  refine adequacy (GF := GF) _ σ (OutcomeOk T) ?_
  intro inst
  have hpost : ∀ o, interpOutcome (GF := GF) bindings T Δ' o ⊢ ⌜OutcomeOk T o⌝ := by
    intro o
    cases o with
    | normal v => exact sep_elim_left.trans outcomeOk_of_interpVal
    | throwing _ =>
      iintro -
      ipureintro
      trivial
  iintro Hown
  imod bigSepM_bupd (fun ℓ c => cellOwn_persist ℓ c) σ.toMap $$ Hown with #H
  iapply wp_mono hpost
  iapply h bindings
  unfold interpCtx
  imodintro
  iintro %f %hf
  iapply interpFact_of_holds (hσ f hf) $$ H

end DartSemantics
