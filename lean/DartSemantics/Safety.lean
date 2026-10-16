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
local notation "Env" => Env (τ := τ)

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

/--
`bindings` are suitable for running a program from state `σ`: each variable is bound at most once
(`nodup`), to a cell of its own (`nodup_locs`), which holds a value or is uninitialized (`cells`).
-/
public structure BindingsOk (σ : State) (bindings : List (Variable × Loc)) : Prop where
  nodup : (bindings.map (·.1)).Nodup
  nodup_locs : (bindings.map (·.2)).Nodup
  cells : ∀ b ∈ bindings, ∃ c, σ.lookup b.2 = some c ∧ ∀ C fs, c ≠ .object C fs

/--
Fact `f` holds in state `σ`, for the variables bound to cells by `bindings`. For a fact about an
instance variable, its cell must not be one of the variables' cells.
-/
@[expose]
public def FactHolds (σ : State) (bindings : List (Variable × Loc)) : Fact → Prop
  | .decl x => ∃ ℓ, bindings.lookup x = some ℓ
  | .var x T => ∃ ℓ v S, bindings.lookup x = some ℓ ∧ σ.lookup ℓ = some (.val v) ∧
      σ.dynamicType v = some S ∧ S ≤ T ∧ ValOk v S
  | .field x name T => ∃ ℓ ℓo C fs ℓf w S, bindings.lookup x = some ℓ ∧
      σ.lookup ℓ = some (.val (.obj ℓo)) ∧ σ.lookup ℓo = some (.object C fs) ∧
      fs.lookup name = some ℓf ∧ (∀ b ∈ bindings, b.2 ≠ ℓf) ∧ σ.lookup ℓf = some (.val w) ∧
      σ.dynamicType w = some S ∧ S ≤ T ∧ ValOk w S

/-- The environment of state `σ`: what the cells that `bindings` binds variables to hold. -/
@[expose]
public def envOf (σ : State) (bindings : List (Variable × Loc)) : Env :=
  fun x => match bindings.lookup x with
    | some ℓ => (σ.lookup ℓ).getD .uninit
    | none => .uninit

omit Γ in
/-- The heap `m`, without the cells that `bindings` binds variables to. -/
@[expose]
public def unbound (m : LocMap Cell) (bindings : List (Variable × Loc)) : LocMap Cell :=
  bindings.foldl (fun m b => delete m b.2) m

omit Γ in
/-- Removing the variables' cells leaves the other cells alone. -/
theorem get?_unbound {m : LocMap Cell} {bindings : List (Variable × Loc)} {ℓ : Loc}
    (h : ∀ b ∈ bindings, b.2 ≠ ℓ) : get? (unbound m bindings) ℓ = get? m ℓ := by
  induction bindings generalizing m with
  | nil => rfl
  | cons b bs ih =>
    simp only [unbound, List.foldl_cons] at ih ⊢
    rw [ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')),
      LawfulPartialMap.get?_delete_ne (h b (List.mem_cons_self ..))]

/-- A variable bound only once is bound to the cell it appears with. -/
theorem lookup_of_mem {bindings : List (Variable × Loc)} (hnd : (bindings.map (·.1)).Nodup)
    {x : Variable} {ℓ : Loc} (h : (x, ℓ) ∈ bindings) : bindings.lookup x = some ℓ := by
  induction bindings with
  | nil => simp at h
  | cons b bs ih =>
    obtain ⟨y, ℓy⟩ := b
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 h with h | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · have hxy : x ≠ y := fun hxy => hnd.1 (List.mem_map.2 ⟨(x, ℓ), h, hxy⟩)
      rw [lookup_cons_ne hxy]
      exact ih hnd.2 h

section

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]

omit Γ in
/--
The ownership of the cells a program starts with, other than the cells of its variables, can be
made persistent: no instance variable ever changes (the model so far doesn't support assignment to
instance variables).
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
/--
The ownership of the cells of a heap `m` splits into the ownership of the cells of the variables
in `bindings`, holding what `env` says, and of the other cells. The variables must have cells of
their own (`hnd`), which hold what `env` says, and aren't objects' own cells (`hc`).
-/
theorem cellOwn_split (env : Env) {bindings : List (Variable × Loc)} {m : LocMap Cell}
    (hnd : (bindings.map (·.2)).Nodup)
    (hc : ∀ b ∈ bindings, get? m b.2 = some (env b.1) ∧ ∀ C fs, env b.1 ≠ .object C fs) :
    ([∗map] ℓ ↦ c ∈ m, cellOwn (GF := GF) ℓ c) ⊢
      interpEnv bindings env ∗ [∗map] ℓ ↦ c ∈ unbound m bindings, cellOwn ℓ c := by
  induction bindings generalizing m with
  | nil =>
    simp only [interpEnv, unbound, List.foldl_nil]
    exact emp_sep.2
  | cons b bs ih =>
    obtain ⟨x, ℓ⟩ := b
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hm, hobj⟩ := hc (x, ℓ) (List.mem_cons_self ..)
    have hc' : ∀ b ∈ bs, get? (delete m ℓ) b.2 = some (env b.1) ∧
        ∀ C fs, env b.1 ≠ .object C fs := fun b hb => by
      have hne : ℓ ≠ b.2 := fun h => hnd.1 (List.mem_map.2 ⟨b, hb, h.symm⟩)
      rw [LawfulPartialMap.get?_delete_ne hne]
      exact hc b (List.mem_cons_of_mem _ hb)
    have hown : cellOwn (GF := GF) ℓ (env x) ⊢ interpCell ℓ (env x) := by
      revert hobj
      cases env x with
      | object C fs => intro hobj; exact absurd rfl (hobj C fs)
      | _ =>
        intro hobj
        simp only [cellOwn, interpCell]
        iintro H
        isplitr
        · ipureintro
          exact hobj
        · iexact H
    simp only [interpEnv, unbound, List.foldl_cons] at ih ⊢
    refine (BigSepM.bigSepM_delete hm).1.trans ?_
    iintro ⟨H, Hrest⟩
    ihave ⟨He, Hrest⟩ := ih hnd.2 hc' $$ Hrest
    isplitl [H He]
    · isplitl [H]
      · iapply hown $$ H
      · iexact He
    · iexact Hrest

omit Γ in
/-- Persistent ownership of the cells other than the variables' includes the cell at `ℓ`. -/
theorem pointsTo_of_unbound {σ : State} {bindings : List (Variable × Loc)} {ℓ : Loc} {c : Cell}
    (h : σ.lookup ℓ = some c) (hnb : ∀ b ∈ bindings, b.2 ≠ ℓ) :
    ([∗map] ℓ ↦ c ∈ unbound σ.toMap bindings, ℓ ↦{.discard} c) ⊢
      (ℓ ↦{.discard} c : IProp GF) :=
  BigSepM.bigSepM_lookup (by rw [get?_unbound hnb, State.get?_toMap]; exact h)

omit Γ in
/-- An object's own cell isn't one of the variables' cells. -/
theorem not_bound_of_object {σ : State} {bindings : List (Variable × Loc)}
    (hb : BindingsOk σ bindings)
    {ℓ : Loc} {C : τ} {fs : List (String × Loc)} (h : σ.lookup ℓ = some (.object C fs)) :
    ∀ b ∈ bindings, b.2 ≠ ℓ := by
  intro b hmem heq
  obtain ⟨c, hc, hobj⟩ := hb.cells b hmem
  rw [heq, h] at hc
  exact hobj C fs (Option.some.inj hc).symm

/--
A value whose dynamic type `S` in state `σ` is a subtype of `T` (and which obeys `ValOk v S`)
satisfies `T` (`interpVal T v`), given persistent ownership of the cells other than the variables'.
-/
theorem interpVal_of_unbound {σ : State} {bindings : List (Variable × Loc)}
    (hb : BindingsOk σ bindings) {v : Value} {S T : τ} (hS : σ.dynamicType v = some S)
    (hT : S ≤ T) (hok : ValOk v S) :
    ([∗map] ℓ ↦ c ∈ unbound σ.toMap bindings, ℓ ↦{.discard} c) ⊢ interpVal (GF := GF) T v := by
  iintro #H
  iexists S
  isplitr
  · cases v with
    | null =>
      simp only [State.dynamicType, Option.some.injEq] at hS
      subst hS
      iapply HasDynamicType.null
    | bool b =>
      simp only [State.dynamicType, Option.some.injEq] at hS
      subst hS
      iapply HasDynamicType.bool
    | obj ℓ =>
      simp only [State.dynamicType] at hS
      split at hS
      · rename_i C fs hℓ
        simp only [Option.some.injEq] at hS
        subst hS
        iapply HasDynamicType.obj
        iapply pointsTo_of_unbound hℓ (not_bound_of_object hb hℓ) $$ H
      · cases hS
    | error e => cases hS
    | cont k => cases hS
  · ipureintro
    exact ⟨hT, hok⟩

/--
A fact that holds in state `σ` (`FactHolds σ bindings f`) also holds as an Iris proposition, about
the environment of `σ` (`interpFact bindings (envOf σ bindings) f`), given persistent ownership of
the cells other than the variables'.
-/
theorem interpFact_of_holds {σ : State} {bindings : List (Variable × Loc)}
    (hb : BindingsOk σ bindings) {f : Fact} (hf : FactHolds σ bindings f) :
    ([∗map] ℓ ↦ c ∈ unbound σ.toMap bindings, ℓ ↦{.discard} c) ⊢
      interpFact (GF := GF) bindings (envOf σ bindings) f := by
  cases f with
  | decl x =>
    iintro -
    ipureintro
    exact hf
  | var x T =>
    obtain ⟨ℓ, v, S, hl, hc, hS, hT, hok⟩ := hf
    iintro #H
    iexists ℓ, v
    isplitr
    · ipureintro
      exact ⟨hl, by simp [envOf, hl, hc]⟩
    · iapply interpVal_of_unbound hb hS hT hok $$ H
  | field x name T =>
    obtain ⟨ℓ, ℓo, C, fs, ℓf, w, S, hl, hc, ho, hfs, hnb, hcf, hS, hT, hok⟩ := hf
    iintro #H
    iexists ℓ, ℓo, C, fs, ℓf, w
    isplitr
    · ipureintro
      exact ⟨hl, by simp [envOf, hl, hc], hfs⟩
    isplitr
    · iapply pointsTo_of_unbound ho (not_bound_of_object hb ho) $$ H
    isplitr
    · iapply pointsTo_of_unbound hcf hnb $$ H
    · iapply interpVal_of_unbound hb hS hT hok $$ H

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
`Δ`, and it starts in state `σ`, with its free variables bound to cells by `bindings`, which are
suitable (`BindingsOk`), such that every fact in `Δ` holds, then it never gets stuck, and every
outcome it completes with is consistent with `T` (`OutcomeOk`).
-/
public theorem safety [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF] {Δ : Ctx}
    {m : LoweredExpr} {T : τ} {Δ' : Value → Ctx} (σ : State)
    (bindings : List (Variable × Loc)) (h : ∀ [DartGS τ .hasLC GF], SemTyped GF Δ m T Δ')
    (hb : BindingsOk σ bindings) (hσ : ∀ f ∈ Δ, FactHolds σ bindings f) :
    adequate .NotStuck (m.bindVariables bindings) σ (fun o _ => OutcomeOk T o) := by
  refine adequacy (GF := GF) _ σ (OutcomeOk T) ?_
  intro inst
  have hpost : ∀ o, interpOutcome (GF := GF) bindings T Δ' o ⊢ ⌜OutcomeOk T o⌝ := by
    intro o
    cases o with
    | normal v =>
      simp only [interpOutcome]
      iintro ⟨%env', -, #Hv, -⟩
      iapply outcomeOk_of_interpVal $$ Hv
    | throwing _ =>
      iintro -
      ipureintro
      trivial
  have hcells : ∀ b ∈ bindings, get? σ.toMap b.2 = some (envOf σ bindings b.1) ∧
      ∀ C fs, envOf σ bindings b.1 ≠ .object C fs := by
    intro b hmem
    obtain ⟨c, hc, hobj⟩ := hb.cells b hmem
    have hl : bindings.lookup b.1 = some b.2 := lookup_of_mem hb.nodup hmem
    have henv : envOf σ bindings b.1 = c := by simp [envOf, hl, hc]
    rw [henv, State.get?_toMap]
    exact ⟨hc, hobj⟩
  iintro Hown
  ihave ⟨He, Hrest⟩ := cellOwn_split (envOf σ bindings) hb.nodup_locs hcells $$ Hown
  imod bigSepM_bupd (fun ℓ c => cellOwn_persist ℓ c) (unbound σ.toMap bindings) $$ Hrest with #H
  iapply wp_mono hpost
  iapply h bindings hb.nodup (envOf σ bindings)
  isplitl [He]
  · iexact He
  unfold interpCtx
  imodintro
  iintro %f %hf
  iapply interpFact_of_holds hb (hσ f hf) $$ H

end DartSemantics
