module
public import DartSemantics.SemanticTyping

/-!
# Compatibility lemmas

The typing rules of the semantic typing judgment (`SemTyped`; see `SemanticTyping.lean`), each
proved sound with respect to the semantics: one *compatibility lemma* for each kind of expression
that flow analysis produces, plus special rules for the expressions that promote a variable or a
property (`x!`, `x as T`, `x is T`, `x._f!`).

In each rule, the expression is semantically well typed with the static type that it is annotated
with (or that `LoweredExpr.typeOf` gives it). Weakening (`SemTyped.weaken`) adjusts a type to a
supertype, or forgets facts.
-/

namespace DartSemantics

open DartLang Iris Iris.BI Iris.ProgramLogic Iris.Std

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)
local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Cell" => Cell (τ := τ)
local notation "Fact" => Fact (τ := τ)
local notation "Ctx" => Ctx (τ := τ)

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF] [SemanticParams τ]

/-! ### Reading variables and instance variables -/

/--
A read of variable `x`, with static type `T`, satisfies a postcondition `Ψ`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`);
- `U` is a subtype of `T` (`U ≤ T`); and
- `Ψ` holds of completing normally with the value `v` in `x`'s cell (`Ψ (.normal v)`), given the
  following (the continuation):
  - the location `ℓ` of `x`'s cell (`bindings.lookup x = some ℓ`);
  - the fact that the cell holds `v` (`ℓ ↦{.discard} (.val v)`); and
  - the fact that `v` satisfies `U` (`interpVal U v`).
-/
public theorem wp_var_typed {bindings : List (Variable × Loc)} {Δ : Ctx} {x : Variable}
    {U T : τ} (hf : Fact.var x U ∈ Δ) (hU : U ≤ T)
    {Ψ : DartLang.Outcome (τ := τ) → IProp GF} :
    interpCtx bindings Δ ∗ (∀ ℓ v, ⌜bindings.lookup x = some ℓ⌝ -∗
        ℓ ↦{.discard} (.val v : Cell) -∗ interpVal U v -∗ Ψ (.normal v)) ⊢
      WP ((LoweredExpr.var x T).bindVariables bindings) {{ Ψ }} := by
  iintro ⟨#H, HΨ⟩
  ihave #Hx := interpCtx_elim hf $$ H
  icases Hx with ⟨%ℓ, %v, %hl, #Hl, #Hv⟩
  rw [LoweredExpr.bindVariables_var, hl]
  icases Hv with ⟨%S, #Hty, %hS, %hok⟩
  iapply wp_varAt (le_trans hS hU)
  isplitr
  · iexact Hty
  isplitr
  · inext
    iexact Hl
  · inext
    iintro -
    iapply HΨ $$ %ℓ %v %rfl Hl
    iexists S
    isplitr
    · iexact Hty
    · ipureintro
      exact ⟨hS, hok⟩

/--
A read of property `p` of variable `x`, with static type `T`, satisfies a postcondition `Ψ`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`);
- `U` is a subtype of `x`'s static type `Tx` (`U ≤ Tx`);
- the context says that `x` refers to an object with an instance variable named `p.name` that
  holds a value that satisfies `W` (`Fact.field x p.name W ∈ Δ`);
- `W` is a subtype of `T` (`W ≤ T`); and
- `Ψ` holds of completing normally with the value `w` in the instance variable (`Ψ (.normal w)`),
  given the following (the continuation):
  - the fact that `w` satisfies `W` (`interpVal W w` witnesses this fact);
  - a helper function that can be used to record the knowledge that `w` satisfies a promoted type
    `W'`. It takes a witness that `w` satisfies `W'` (`interpVal W' w`), and returns a witness of
    the fact that the instance variable holds such a value
    (`interpFact bindings (.field x p.name W')`), which can be added to the context. It is
    persistent (`□`), so it can be used any number of times. The null-check rule uses it to record
    the promotion of `x._f`.
-/
public theorem wp_field_typed {bindings : List (Variable × Loc)} {Δ : Ctx} {x : Variable}
    {p : Property} {U Tx W T : τ} (hx : Fact.var x U ∈ Δ) (hU : U ≤ Tx)
    (hf : Fact.field x p.name W ∈ Δ) (hW : W ≤ T) {Ψ : DartLang.Outcome (τ := τ) → IProp GF} :
    interpCtx bindings Δ ∗ (∀ w, interpVal W w -∗
        (□ ∀ W', interpVal W' w -∗ interpFact bindings (.field x p.name W')) -∗
        Ψ (.normal w)) ⊢
      WP ((LoweredExpr.propertyGet (.var x Tx) p T).bindVariables bindings) {{ Ψ }} := by
  rw [LoweredExpr.bindVariables_propertyGet]
  refine .trans ?_ (wp_bind_item (.propertyGet p T))
  iintro ⟨#H, HΨ⟩
  ihave #Hf := interpCtx_elim hf $$ H
  icases Hf with ⟨%ℓ, %ℓo, %C, %fs, %ℓf, %w, ⟨%hl, %hfs⟩, #Hl, #Ho, #Hlf, #Hw⟩
  iapply wp_var_typed hx hU
  isplitr
  · iexact H
  iintro %ℓ' %v %hl' #Hl' -
  have hℓ : ℓ' = ℓ := by simpa [hl] using hl'.symm
  subst hℓ
  ihave %heq : ⌜(Cell.val v : Cell) = .val (.obj ℓo)⌝ $$ [Hl' Hl]
  · iapply pointsTo_agree
    isplitl [Hl']
    · iexact Hl'
    · iexact Hl
  simp only [Cell.val.injEq] at heq
  subst heq
  simp only [DartLang.Outcome.toExpr, EctxItem.fill]
  icases Hw with ⟨%S, #Hty, %hS, %hok⟩
  iapply wp_propertyGetField (fs := fs) (w := w) hfs (le_trans hS hW)
  isplitr
  · iexact Ho
  isplitr
  · iexact Hty
  isplitr
  · inext
    iexact Hlf
  · inext
    iintro -
    iapply HΨ
    · iexists S
      isplitr
      · iexact Hty
      · ipureintro
        exact ⟨hS, hok⟩
    · imodintro
      iintro %W' #Hw'
      iexists ℓ', ℓo, C, fs, ℓf, w
      isplitr
      · ipureintro
        exact ⟨hl', hfs⟩
      isplitr
      · iexact Hl
      isplitr
      · iexact Ho
      isplitr
      · iexact Hlf
      · iexact Hw'

/-! ### Literals and variables -/

/--
The null literal is semantically well typed with type `Null`, and guarantees afterwards the facts
that held beforehand (`Δ`).
-/
public theorem SemTyped.null (Δ : Ctx) : SemTyped GF Δ .null Γ.Null (fun _ => Δ) := by
  intro bindings
  rw [LoweredExpr.bindVariables_null]
  iintro #H
  iapply wp_null
  inext
  simp only [interpOutcome]
  isplitr
  · iapply interpVal_null le_rfl
  · iexact H

/--
A reference to variable `x` is semantically well typed with its static type `T`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`); and
- `U` is a subtype of `T` (`U ≤ T`).

It guarantees afterwards the facts that held beforehand (`Δ`).
-/
public theorem SemTyped.var {Δ : Ctx} {x : Variable} {U T : τ} (hf : Fact.var x U ∈ Δ)
    (hU : U ≤ T) : SemTyped GF Δ (.var x T) T (fun _ => Δ) := by
  intro bindings
  iintro #H
  iapply wp_var_typed hf hU
  isplitr
  · iexact H
  iintro %ℓ %v %hl #Hl #Hv
  simp only [interpOutcome]
  isplitr
  · iapply interpVal_mono hU $$ Hv
  · iexact H

/--
Reading property `p` of variable `x` is semantically well typed with its static type `T`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`);
- `U` is a subtype of `x`'s static type `Tx` (`U ≤ Tx`);
- the context says that `x` refers to an object with an instance variable named `p.name` that
  holds a value that satisfies `W` (`Fact.field x p.name W ∈ Δ`); and
- `W` is a subtype of `T` (`W ≤ T`).

It guarantees afterwards the facts that held beforehand (`Δ`).
-/
public theorem SemTyped.propertyGet {Δ : Ctx} {x : Variable} {p : Property} {U Tx W T : τ}
    (hx : Fact.var x U ∈ Δ) (hU : U ≤ Tx) (hf : Fact.field x p.name W ∈ Δ) (hW : W ≤ T) :
    SemTyped GF Δ (.propertyGet (.var x Tx) p T) T (fun _ => Δ) := by
  intro bindings
  iintro #H
  iapply wp_field_typed hx hU hf hW
  isplitr
  · iexact H
  iintro %w #Hw -
  simp only [interpOutcome]
  isplitr
  · iapply interpVal_mono hW $$ Hw
  · iexact H

/-! ### Null checks -/

/--
A null check `m!` is semantically well typed with type `NonNull T`, if `m` is semantically well
typed with type `T` (`h`). It guarantees afterwards the facts that `m` guarantees (`Δ'`).
-/
public theorem SemTyped.nullCheck (L : TypeLaws τ) {Δ : Ctx} {m : LoweredExpr} {T : τ}
    {Δ' : Value → Ctx} (h : SemTyped GF Δ m T Δ') :
    SemTyped GF Δ (.nullCheck m) (Γ.NonNull T) Δ' := by
  intro bindings
  rw [LoweredExpr.bindVariables_nullCheck]
  refine wp_fill_typed (Ki := .nullCheck) (h bindings) (fun v => ?_) (fun _ => true_intro)
  by_cases hv : v = .null
  · subst hv
    refine .trans ?_ wp_nullCheck_null
    iintro -
    inext
    simp only [interpOutcome]
    itrivial
  · refine .trans ?_ (wp_nullCheck hv)
    iintro ⟨#Hv, #H⟩
    inext
    simp only [interpOutcome]
    isplitr
    · iapply interpVal_nonNull L hv $$ Hv
    · iexact H

/--
A null check `x!` of a variable `x` is semantically well typed with type `NonNull T`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`); and
- `U` is a subtype of `T` (`U ≤ T`).

It guarantees afterwards the facts that held beforehand, plus that `x` holds a value that satisfies
`NonNull T` (`.var x (Γ.NonNull T) :: Δ`): the null check promotes `x`.
-/
public theorem SemTyped.nullCheck_var (L : TypeLaws τ) {Δ : Ctx} {x : Variable} {U T : τ}
    (hf : Fact.var x U ∈ Δ) (hU : U ≤ T) :
    SemTyped GF Δ (.nullCheck (.var x T)) (Γ.NonNull T)
      (fun _ => .var x (Γ.NonNull T) :: Δ) := by
  intro bindings
  rw [LoweredExpr.bindVariables_nullCheck]
  refine .trans ?_ (wp_bind_item .nullCheck)
  iintro #H
  iapply wp_var_typed hf hU
  isplitr
  · iexact H
  iintro %ℓ %v %hl #Hl #Hv
  simp only [DartLang.Outcome.toExpr, EctxItem.fill]
  by_cases hv : v = .null
  · subst hv
    iapply wp_nullCheck_null
    inext
    simp only [interpOutcome]
    itrivial
  · iapply wp_nullCheck hv
    inext
    simp only [interpOutcome]
    ihave #Hv1 := interpVal_mono hU $$ Hv
    ihave #Hv' := interpVal_nonNull L hv $$ Hv1
    isplitr
    · iexact Hv'
    · iapply interpCtx_cons
      isplitr
      · iexists ℓ, v
        isplitr
        · ipureintro
          exact hl
        isplitr
        · iexact Hl
        · iexact Hv'
      · iexact H

/--
A null check `x._f!` of property `p` of variable `x` is semantically well typed with type
`NonNull T`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`);
- `U` is a subtype of `x`'s static type `Tx` (`U ≤ Tx`);
- the context says that `x` refers to an object with an instance variable named `p.name` that
  holds a value that satisfies `W` (`Fact.field x p.name W ∈ Δ`); and
- `W` is a subtype of `T` (`W ≤ T`).

It guarantees afterwards the facts that held beforehand, plus that the instance variable holds a
value that satisfies `NonNull T` (`.field x p.name (Γ.NonNull T) :: Δ`): the null check promotes
`x._f`.
-/
public theorem SemTyped.nullCheck_field (L : TypeLaws τ) {Δ : Ctx} {x : Variable} {p : Property}
    {U Tx W T : τ} (hx : Fact.var x U ∈ Δ) (hU : U ≤ Tx) (hf : Fact.field x p.name W ∈ Δ)
    (hW : W ≤ T) :
    SemTyped GF Δ (.nullCheck (.propertyGet (.var x Tx) p T)) (Γ.NonNull T)
      (fun _ => .field x p.name (Γ.NonNull T) :: Δ) := by
  intro bindings
  rw [LoweredExpr.bindVariables_nullCheck]
  refine .trans ?_ (wp_bind_item .nullCheck)
  iintro #H
  iapply wp_field_typed hx hU hf hW
  isplitr
  · iexact H
  iintro %w #Hw #Hfact
  simp only [DartLang.Outcome.toExpr, EctxItem.fill]
  by_cases hw : w = .null
  · subst hw
    iapply wp_nullCheck_null
    inext
    simp only [interpOutcome]
    itrivial
  · iapply wp_nullCheck hw
    inext
    simp only [interpOutcome]
    ihave #Hw1 := interpVal_mono hW $$ Hw
    ihave #Hw' := interpVal_nonNull L hw $$ Hw1
    isplitr
    · iexact Hw'
    · iapply interpCtx_cons
      isplitr
      · iapply Hfact $$ Hw'
      · iexact H

/-! ### Casts and is-expressions -/

/--
A cast `m as T` is semantically well typed with type `T`, if `m` is semantically well typed with
some type `S` (`h`). It guarantees afterwards the facts that `m` guarantees (`Δ'`).
-/
public theorem SemTyped.as {Δ : Ctx} {m : LoweredExpr} {S T : τ} {Δ' : Value → Ctx}
    (h : SemTyped GF Δ m S Δ') : SemTyped GF Δ (.as m T) T Δ' := by
  intro bindings
  rw [LoweredExpr.bindVariables_as]
  refine wp_fill_typed (Ki := .as T) (h bindings) (fun v => ?_) (fun _ => true_intro)
  simp only [EctxItem.fill]
  iintro ⟨#Hv, #H⟩
  icases Hv with ⟨%S₀, #Hty, %hS, %hok⟩
  by_cases hb : ∃ b, RtSub S₀ T b
  · obtain ⟨b, hb⟩ := hb
    cases b
    · iapply wp_as_false hb
      isplitr
      · iexact Hty
      · inext
        simp only [interpOutcome]
        itrivial
    · iapply wp_as_true hb
      isplitr
      · iexact Hty
      · inext
        simp only [interpOutcome]
        isplitr
        · iexists S₀
          isplitr
          · iexact Hty
          · ipureintro
            exact ⟨DartRuntimeTypeRepr.rtSub_true hb, hok⟩
        · iexact H
  · iapply wp_as_diverge (fun b h => hb ⟨b, h⟩)
    iexact Hty

/--
A cast `x as T` of a variable `x` is semantically well typed with type `T`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`); and
- `U` is a subtype of `x`'s static type `Tx` (`U ≤ Tx`).

It guarantees afterwards the facts that held beforehand, plus that `x` holds a value that satisfies
`T` (`.var x T :: Δ`): the cast promotes `x`.
-/
public theorem SemTyped.as_var {Δ : Ctx} {x : Variable} {U Tx T : τ} (hf : Fact.var x U ∈ Δ)
    (hU : U ≤ Tx) : SemTyped GF Δ (.as (.var x Tx) T) T (fun _ => .var x T :: Δ) := by
  intro bindings
  rw [LoweredExpr.bindVariables_as]
  refine .trans ?_ (wp_bind_item (.as T))
  iintro #H
  iapply wp_var_typed hf hU
  isplitr
  · iexact H
  iintro %ℓ %v %hl #Hl #Hv
  simp only [DartLang.Outcome.toExpr, EctxItem.fill]
  icases Hv with ⟨%S₀, #Hty, %hS, %hok⟩
  by_cases hb : ∃ b, RtSub S₀ T b
  · obtain ⟨b, hb⟩ := hb
    cases b
    · iapply wp_as_false hb
      isplitr
      · iexact Hty
      · inext
        simp only [interpOutcome]
        itrivial
    · iapply wp_as_true hb
      isplitr
      · iexact Hty
      · inext
        simp only [interpOutcome]
        ihave #Hv' : interpVal T v $$ []
        · iexists S₀
          isplitr
          · iexact Hty
          · ipureintro
            exact ⟨DartRuntimeTypeRepr.rtSub_true hb, hok⟩
        isplitr
        · iexact Hv'
        · iapply interpCtx_cons
          isplitr
          · iexists ℓ, v
            isplitr
            · ipureintro
              exact hl
            isplitr
            · iexact Hl
            · iexact Hv'
          · iexact H
  · iapply wp_as_diverge (fun b h => hb ⟨b, h⟩)
    iexact Hty

/--
An is-expression `m is T` is semantically well typed with type `bool`, if `m` is semantically well
typed with some type `S`, guaranteeing facts afterwards that don't depend on its value (`h`). It
guarantees afterwards the facts that `m` guarantees (`Δ₁`).
-/
public theorem SemTyped.is {Δ Δ₁ : Ctx} {m : LoweredExpr} {S T : τ}
    (h : SemTyped GF Δ m S (fun _ => Δ₁)) : SemTyped GF Δ (.is m T) Γ.bool (fun _ => Δ₁) := by
  intro bindings
  rw [LoweredExpr.bindVariables_is]
  refine wp_fill_typed (Ki := .is T) (h bindings) (fun v => ?_) (fun _ => true_intro)
  simp only [EctxItem.fill]
  iintro ⟨#Hv, #H⟩
  icases Hv with ⟨%S₀, #Hty, %hS, %hok⟩
  by_cases hb : ∃ b, RtSub S₀ T b
  · obtain ⟨b, hb⟩ := hb
    iapply wp_is hb
    isplitr
    · iexact Hty
    · inext
      simp only [interpOutcome]
      isplitr
      · iapply interpVal_bool b le_rfl
      · iexact H
  · iapply wp_is_diverge (fun b h => hb ⟨b, h⟩)
    iexact Hty

/--
An is-expression `x is T` of a variable `x` is semantically well typed with type `bool`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`); and
- `U` is a subtype of `x`'s static type `Tx` (`U ≤ Tx`).

It guarantees afterwards the facts that held beforehand, plus, if it evaluates to `true`, that `x`
holds a value that satisfies `T` (`Ctx.byCondition (.var x T :: Δ) Δ`): the is-expression promotes
`x` when it's `true`.
-/
public theorem SemTyped.is_var {Δ : Ctx} {x : Variable} {U Tx T : τ} (hf : Fact.var x U ∈ Δ)
    (hU : U ≤ Tx) :
    SemTyped GF Δ (.is (.var x Tx) T) Γ.bool (Ctx.byCondition (.var x T :: Δ) Δ) := by
  intro bindings
  rw [LoweredExpr.bindVariables_is]
  refine .trans ?_ (wp_bind_item (.is T))
  iintro #H
  iapply wp_var_typed hf hU
  isplitr
  · iexact H
  iintro %ℓ %v %hl #Hl #Hv
  simp only [DartLang.Outcome.toExpr, EctxItem.fill]
  icases Hv with ⟨%S₀, #Hty, %hS, %hok⟩
  by_cases hb : ∃ b, RtSub S₀ T b
  · obtain ⟨b, hb⟩ := hb
    iapply wp_is hb
    isplitr
    · iexact Hty
    · inext
      simp only [interpOutcome]
      isplitr
      · iapply interpVal_bool b le_rfl
      · cases b
        · simp only [Ctx.byCondition_false]
          iexact H
        · simp only [Ctx.byCondition_true]
          iapply interpCtx_cons
          isplitr
          · iexists ℓ, v
            isplitr
            · ipureintro
              exact hl
            isplitr
            · iexact Hl
            · iexists S₀
              isplitr
              · iexact Hty
              · ipureintro
                exact ⟨DartRuntimeTypeRepr.rtSub_true hb, hok⟩
          · iexact H
  · iapply wp_is_diverge (fun b h => hb ⟨b, h⟩)
    iexact Hty

/-! ### Conditionals -/

/--
A conditional is semantically well typed with its static type `T`, if:
- its condition is semantically well typed with type `bool` (`h₁`);
- its first branch is semantically well typed with type `T` (`h₂`), given the facts that the
  condition guarantees when it evaluates to `true` (`Δc (.bool true)`); and
- its second branch is semantically well typed with type `T` (`h₃`), given the facts that the
  condition guarantees when it evaluates to `false` (`Δc (.bool false)`).

Both branches must guarantee the same facts (`Δ'`), which the conditional then guarantees;
weakening can drop facts to make them agree.
-/
public theorem SemTyped.cond (L : TypeLaws τ) {Δ Δ' : Ctx} {Δc : Value → Ctx}
    {m₁ m₂ m₃ : LoweredExpr} {T : τ} (h₁ : SemTyped GF Δ m₁ Γ.bool Δc)
    (h₂ : SemTyped GF (Δc (.bool true)) m₂ T (fun _ => Δ'))
    (h₃ : SemTyped GF (Δc (.bool false)) m₃ T (fun _ => Δ')) :
    SemTyped GF Δ (.cond m₁ m₂ m₃ T) T (fun _ => Δ') := by
  intro bindings
  rw [LoweredExpr.bindVariables_cond]
  refine wp_fill_typed (Ki := .cond (m₂.bindVariables bindings) (m₃.bindVariables bindings) T)
    (h₁ bindings) (fun v => ?_) (fun _ => true_intro)
  simp only [EctxItem.fill]
  iintro ⟨#Hv, #H⟩
  ihave %hb := interpVal_bool_inv L $$ Hv
  obtain ⟨b, rfl⟩ := hb
  cases b
  · iapply wp_cond_false
    inext
    iapply h₃ bindings
    iexact H
  · iapply wp_cond_true
    inext
    iapply h₂ bindings
    iexact H

/-! ### Blocks and declarations -/

omit [DartGS τ hlc GF] [SemanticParams τ] in
/--
A fact remains when those about `v` are forgotten (`f ∈ Δ.forget v`) exactly when it's one of the
facts (`f ∈ Δ`) and isn't about `v` (`f.variable ≠ v`).
-/
public theorem Ctx.mem_forget {Δ : Ctx} {v : Variable} {f : Fact} :
    f ∈ Δ.forget v ↔ f ∈ Δ ∧ f.variable ≠ v := by
  simp [Ctx.forget]

/--
An empty block is semantically well typed with type `Null`, and guarantees afterwards the facts
that held beforehand (`Δ`).
-/
public theorem SemTyped.block_nil (Δ : Ctx) :
    SemTyped GF Δ (.block []) Γ.Null (fun _ => Δ) := by
  intro bindings
  rw [LoweredExpr.bindVariables_block, LoweredExpr.bindBlock_nil]
  iintro #H
  iapply wp_blockNil
  inext
  simp only [interpOutcome]
  isplitr
  · iapply interpVal_null le_rfl
  · iexact H

/--
A block that starts with anything other than a declaration (`hm`) is semantically well typed with
type `Null`, if:
- its first element is semantically well typed with some type `T` (`h`), guaranteeing facts `Δ₁`
  afterwards; and
- the rest of the block is semantically well typed with type `Null` (`hr`), given those facts.

It guarantees afterwards the facts that the rest of the block guarantees (`Δ₂`).
-/
public theorem SemTyped.block_cons {Δ Δ₁ Δ₂ : Ctx} {m : LoweredExpr} {ms : List LoweredExpr}
    {T : τ} (hm : ∀ v T sN, m ≠ .declare v T sN) (h : SemTyped GF Δ m T (fun _ => Δ₁))
    (hr : SemTyped GF Δ₁ (.block ms) Γ.Null (fun _ => Δ₂)) :
    SemTyped GF Δ (.block (m :: ms)) Γ.Null (fun _ => Δ₂) := by
  intro bindings
  rw [LoweredExpr.bindVariables_block, LoweredExpr.bindBlock_cons bindings hm]
  refine .trans ?_ (wp_blockCons (LoweredExpr.bindVariables_ne_declare bindings hm))
  refine .trans ?_ later_intro
  refine wp_fill_typed (Ki := .seq (.block (LoweredExpr.bindBlock bindings ms))) (h bindings)
    (fun v => ?_) (fun _ => true_intro)
  refine .trans ?_ wp_seq
  refine .trans ?_ later_intro
  have hr' := hr bindings
  rw [LoweredExpr.bindVariables_block] at hr'
  iintro ⟨-, #H⟩
  iapply hr'
  iexact H

/--
A block that starts with a declaration of `v` is semantically well typed with type `Null`, if the
rest of the block is semantically well typed with type `Null` (`h`), given:
- the facts that held beforehand, less those about any outer `v`, which the declaration shadows
  (`Δ.forget v`); plus
- if `v` starts out holding the null object (`sN`), that `v` holds a value that satisfies `T`
  (`Fact.var v T`).

That requires `Null` to be a subtype of `T` (`hsN`), which flow analysis ensures by setting
`startsNull` only for nullable types. It guarantees afterwards the facts that the rest of the block
guarantees, less those about `v`, since `v` goes out of scope (`Δ₂.forget v`).
-/
public theorem SemTyped.block_declare {Δ Δ₂ : Ctx} {v : Variable} {T : τ} {sN : Bool}
    {ms : List LoweredExpr} (hsN : sN = true → Γ.Null ≤ T)
    (h : SemTyped GF ((if sN then [Fact.var v T] else []) ++ Δ.forget v) (.block ms) Γ.Null
      (fun _ => Δ₂)) :
    SemTyped GF Δ (.block (.declare v T sN :: ms)) Γ.Null (fun _ => Δ₂.forget v) := by
  intro bindings
  rw [LoweredExpr.bindVariables_block, LoweredExpr.bindBlock_declare]
  iintro #H
  iapply wp_blockDeclare
  inext
  iintro %ℓ Hℓ
  have hne : ∀ b ∈ bindings.filter (fun b => b.1 ≠ v), b.1 ≠ v := fun b hb => by
    simpa using (List.mem_filter.1 hb).2
  rw [LoweredExpr.resolveBlock_bindBlock hne]
  rw [show LoweredExpr.bindBlock (bindings.filter fun b => b.1 ≠ v)
        (LoweredExpr.resolveBlock v ℓ ms)
      = LoweredExpr.bindBlock ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v) ms from rfl,
    ← LoweredExpr.bindVariables_block]
  have hlook : ∀ x, x ≠ v →
      ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v).lookup x = bindings.lookup x := fun x hx => by
    rw [lookup_cons_ne hx, lookup_filter_ne hx]
  have hpost : ∀ o, interpOutcome (GF := GF) ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v) Γ.Null
      (fun _ => Δ₂) o ⊢ interpOutcome bindings Γ.Null (fun _ => Δ₂.forget v) o := by
    intro o
    cases o with
    | normal w =>
      simp only [interpOutcome]
      refine sep_mono .rfl ((interpCtx_mono (Δ := Δ₂.forget v) (Δ₀ := Δ₂)
        fun f hf => (Ctx.mem_forget.1 hf).1).trans ?_)
      exact interpCtx_congr fun f hf => hlook _ (Ctx.mem_forget.1 hf).2
    | throwing _ => exact .rfl
  ihave #Hrest : interpCtx ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v) (Δ.forget v) $$ []
  · iapply interpCtx_congr (bindings := bindings)
      (fun f hf => (hlook _ (Ctx.mem_forget.1 hf).2).symm)
    iapply interpCtx_mono (fun f hf => (Ctx.mem_forget.1 hf).1)
    iexact H
  iapply wp_mono hpost
  cases sN with
  | false =>
    iapply h _
    simp only [Bool.false_eq_true, ite_false, List.nil_append]
    iexact Hrest
  | true =>
    imod pointsTo_persist $$ Hℓ with #Hℓ
    iapply h _
    simp only [ite_true, List.singleton_append]
    iapply interpCtx_cons
    isplitr
    · iexists ℓ, .null
      isplitr
      · ipureintro
        simp [List.lookup]
      isplitr
      · iexact Hℓ
      · iapply interpVal_null (hsN rfl)
    · iexact Hrest

/--
A declaration of `v` outside a block is semantically well typed with type `Null`, as the block
containing just that declaration is (so it has the same requirement `hsN`). It guarantees
afterwards the facts that held beforehand, less those about `v` (`Δ.forget v`).
-/
public theorem SemTyped.declare {Δ : Ctx} {v : Variable} {T : τ} {sN : Bool}
    (hsN : sN = true → Γ.Null ≤ T) :
    SemTyped GF Δ (.declare v T sN) Γ.Null (fun _ => Δ.forget v) := by
  have hb := (SemTyped.block_declare (GF := GF) (Δ := Δ) (v := v) (T := T) (ms := []) hsN
    (SemTyped.block_nil _)).weaken (Δa' := fun _ => Δ.forget v) (fun f hf => hf) le_rfl
    (fun _ f hf => ?_)
  · intro bindings
    rw [LoweredExpr.bindVariables_declare]
    refine .trans ?_ wp_declare
    refine .trans ?_ later_intro
    have hb' := hb bindings
    rw [LoweredExpr.bindVariables_block, LoweredExpr.bindBlock_declare,
      LoweredExpr.bindBlock_nil] at hb'
    exact hb'
  · obtain ⟨hf, hfv⟩ := Ctx.mem_forget.1 hf
    exact Ctx.mem_forget.2 ⟨List.mem_append_right _ (Ctx.mem_forget.2 ⟨hf, hfv⟩), hfv⟩

end DartSemantics
