module
public import DartSemantics.SemanticTyping

/-!
# Compatibility lemmas

The typing rules of the semantic typing judgment (`SemTyped`; see `SemanticTyping.lean`), each
proved sound with respect to the semantics: one *compatibility lemma* for each kind of expression
that flow analysis produces, plus special rules for the expressions that promote a variable or a
property path (`x!`, `x as T`, `x is T`, `x._f._g!`, and so on).

Reads of property paths (`x`, `x._f`, `x._f._g`, …) have a judgment of their own,
`SemTypedPath`, which records which path an expression reads, so that the promotion rules
(`SemTyped.nullCheck_path`, `SemTyped.as_path` and `SemTyped.is_path`) can record a fact about it.

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
local notation "Env" => Env (τ := τ)

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF] [SemanticParams τ]

/-! ### Reading variables and instance variables -/

/--
A read of variable `x`, with static type `T`, satisfies a postcondition `Ψ`, if:
- the cells of the variables in `bindings` (each bound at most once, `hnd`) are owned, holding what
  `env` says (`interpEnv bindings env`);
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`);
- `U` is a subtype of `T` (`U ≤ T`); and
- `Ψ` holds of completing normally with the value `v` in `x`'s cell (`Ψ (.normal v)`), given the
  following (the continuation):
  - the location `ℓ` of `x`'s cell (`bindings.lookup x = some ℓ`);
  - the fact that the cell holds `v` (`env x = .val v`);
  - the fact that `v` satisfies `U` (`interpVal U v`); and
  - the ownership of the cells, unchanged (`interpEnv bindings env`).
-/
public theorem wp_var_typed {bindings : List (Variable × Loc)} {env : Env} {Δ : Ctx}
    {x : Variable} {U T : τ} (hnd : (bindings.map (·.1)).Nodup) (hf : Fact.var x U ∈ Δ)
    (hU : U ≤ T) {Ψ : DartLang.Outcome (τ := τ) → IProp GF} :
    interpEnv bindings env ∗ interpCtx bindings env Δ ∗
        (∀ ℓ v, ⌜bindings.lookup x = some ℓ⌝ -∗ ⌜env x = .val v⌝ -∗ interpVal U v -∗
          interpEnv bindings env -∗ Ψ (.normal v)) ⊢
      WP ((LoweredExpr.var x T).bindVariables bindings) {{ Ψ }} := by
  iintro ⟨He, #H, HΨ⟩
  ihave #Hx := interpCtx_elim hf $$ H
  icases Hx with ⟨%ℓ, %v, ⟨%hl, %henv⟩, #Hv⟩
  rw [LoweredExpr.bindVariables_var, hl]
  have hacc := interpEnv_acc_read (GF := GF) (env := env) hnd hl
  rw [henv] at hacc
  icases hacc $$ He with ⟨⟨-, Hl⟩, Hback⟩
  icases Hv with ⟨%S, #Hty, %hS, %hok⟩
  iapply wp_varAt (le_trans hS hU)
  isplitr
  · iexact Hty
  isplitl [Hl]
  · inext
    iexact Hl
  · inext
    iintro Hl
    ihave He := Hback $$ [Hl]
    · isplitr
      · ipureintro
        exact fun _ _ h => by cases h
      · iexact Hl
    -- (Rewriting with `hl` above also rewrote `HΨ`'s premise, so `rfl` proves it.)
    iapply HΨ $$ %ℓ %v %rfl %henv
    · iexists S
      isplitr
      · iexact Hty
      · ipureintro
        exact ⟨hS, hok⟩
    · iexact He

/-! ### Reading property paths -/

/--
Variable `x` (bound to cell `ℓ`) holds a value `v`, and following property path `path` from `v`
reaches `w`. It is persistent, like the facts.
-/
@[expose, reducible]
public def interpPathTo (bindings : List (Variable × Loc)) (env : Env) (x : Variable)
    (path : List String) (w : Value) : IProp GF :=
  iprop(∃ ℓ v, ⌜bindings.lookup x = some ℓ ∧ env x = .val v⌝ ∗ interpFieldPath path v w)

omit [SemanticParams τ] in
/--
If following property path `path` from variable `x` reaches `w` (`interpPathTo bindings env x path
w`), and `w` satisfies `T` (`interpVal T w`), then the fact that the value at that path satisfies
`T` holds (`interpFact bindings env (Fact.atPath x path T)`).
-/
public theorem interpFact_atPath {bindings : List (Variable × Loc)} {env : Env} {x : Variable}
    {path : List String} {T : τ} {w : Value} :
    interpPathTo (GF := GF) bindings env x path w ∗ interpVal T w ⊢
      interpFact bindings env (Fact.atPath x path T) := by
  cases path with
  | nil =>
    simp only [Fact.atPath]
    iintro ⟨⟨%ℓ, %v, ⟨%hl, %henv⟩, %hvw⟩, #Hw⟩
    subst hvw
    iexists ℓ, v
    isplitr
    · ipureintro
      exact ⟨hl, henv⟩
    · iexact Hw
  | cons name path =>
    simp only [Fact.atPath]
    iintro ⟨⟨%ℓ, %v, %h, #Hp⟩, #Hw⟩
    iexists ℓ, v, w
    isplitr
    · ipureintro
      exact h
    isplitr
    · iexact Hp
    · iexact Hw

variable (GF) in
/--
The judgment for reads of property paths, `SemTypedPath Δ m x path T`: `m` reads the value at
property path `path` from variable `x` (for example, `m` is `x._f._g` and `path` is `["_f", "_g"]`).
Whatever cells the variables in scope are bound to (`bindings`, which binds each variable at most
once; `x` must be one of them), and whatever those cells hold (`env`), if the cells are owned and
the facts in `Δ` hold, then running `m` satisfies any postcondition `Ψ` that holds of completing
normally with a value `w`, given:
- that `w` satisfies `T` (`interpVal T w`);
- that following `path` from `x` reaches `w` (`interpPathTo bindings env x path w`), which a
  promotion rule can use to record a fact about the path (see `interpFact_atPath`); and
- the ownership of the cells, unchanged: reading doesn't change any variable.

So `m` doesn't get stuck, and doesn't throw.
-/
@[expose]
public def SemTypedPath (Δ : Ctx) (m : LoweredExpr) (x : Variable) (path : List String) (T : τ) :
    Prop :=
  ∀ bindings, (bindings.map (·.1)).Nodup → ∀ env (Ψ : DartLang.Outcome (τ := τ) → IProp GF),
    interpEnv bindings env ∗ interpCtx bindings env Δ ∗
        (∀ w, interpVal T w -∗ interpPathTo bindings env x path w -∗ interpEnv bindings env -∗
          Ψ (.normal w)) ⊢
      WP (m.bindVariables bindings) {{ Ψ }}

/--
A reference to variable `x` reads the value at the empty path from `x`, with its static type `T`,
if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`); and
- `U` is a subtype of `T` (`U ≤ T`).
-/
public theorem SemTypedPath.var {Δ : Ctx} {x : Variable} {U T : τ} (hf : Fact.var x U ∈ Δ)
    (hU : U ≤ T) : SemTypedPath GF Δ (.var x T) x [] T := by
  intro bindings hnd env Ψ
  iintro ⟨He, #H, HΨ⟩
  iapply wp_var_typed hnd hf hU
  isplitl [He]
  · iexact He
  isplitr
  · iexact H
  iintro %ℓ %v %hl %henv #Hv He
  iapply HΨ
  · iapply interpVal_mono hU $$ Hv
  · iexists ℓ, v
    isplitr
    · ipureintro
      exact ⟨hl, henv⟩
    · ipureintro
      rfl
  · iexact He

/--
Reading property `p` of the value at property path `path` from variable `x` reads the value at
`path ++ [p.name]`, with its static type `T`, if:
- `m` reads the value at `path` from `x`, with some static type `Tm` (`hm`);
- the context says that the value at `path ++ [p.name]` (an instance variable named `p.name` of the
  object at `path`) satisfies `W` (`Fact.field x (path ++ [p.name]) W ∈ Δ`); and
- `W` is a subtype of `T` (`W ≤ T`).
-/
public theorem SemTypedPath.propertyGet {Δ : Ctx} {m : LoweredExpr} {x : Variable}
    {path : List String} {p : Property} {Tm W T : τ} (hm : SemTypedPath GF Δ m x path Tm)
    (hf : Fact.field x (path ++ [p.name]) W ∈ Δ) (hW : W ≤ T) :
    SemTypedPath GF Δ (.propertyGet m p T) x (path ++ [p.name]) T := by
  intro bindings hnd env Ψ
  rw [LoweredExpr.bindVariables_propertyGet]
  refine .trans ?_ (wp_bind_item (.propertyGet p T))
  iintro ⟨He, #H, HΨ⟩
  ihave #Hf := interpCtx_elim hf $$ H
  icases Hf with ⟨%ℓ, %v, %w, ⟨%hl, %henv⟩, #Hpath, #Hw⟩
  ihave #Hsplit := (interpFieldPath_append path [p.name] v w).1 $$ Hpath
  icases Hsplit with ⟨%u, #Hpu, #Huw⟩
  iapply hm bindings hnd env
  isplitl [He]
  · iexact He
  isplitr
  · iexact H
  iintro %w₀ - #Hp₀ He
  icases Hp₀ with ⟨%ℓ', %v', ⟨%hl', %henv'⟩, #Hp₀'⟩
  have hv : v' = v := by rw [henv] at henv'; exact (Cell.val.inj henv').symm
  subst hv
  -- The object that `m` read is the one at `path` that the fact describes.
  ihave %hu : ⌜u = w₀⌝ $$ []
  · iapply interpFieldPath_agree path
    isplitr
    · iexact Hpu
    · iexact Hp₀'
  subst hu
  simp only [DartLang.Outcome.toExpr, EctxItem.fill]
  icases Huw with ⟨%ℓo, %C, %fs, %ℓf, %w', ⟨%hu, %hfs⟩, #Ho, #Hlf, %hw'⟩
  subst hu hw'
  icases Hw with ⟨%S, #Hty, %hS, %hok⟩
  iapply wp_propertyGetField (fs := fs) (w := w') hfs (le_trans hS hW)
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
        exact ⟨le_trans hS hW, hok⟩
    · iexists ℓ', v'
      isplitr
      · ipureintro
        exact ⟨hl', henv'⟩
      · iapply (interpFieldPath_append path [p.name] v' w').2
        iexists .obj ℓo
        isplitr
        · iexact Hpu
        · iexists ℓo, C, fs, ℓf, w'
          isplitr
          · ipureintro
            exact ⟨rfl, hfs⟩
          isplitr
          · iexact Ho
          isplitr
          · iexact Hlf
          · ipureintro
            rfl
    · iexact He

/--
An expression that reads a property path is semantically well typed with the type it reads the
value at (`T`), if it reads the value at the path with type `T` (`h`). It guarantees afterwards
the facts that held beforehand (`Δ`).
-/
public theorem SemTypedPath.toSemTyped {Δ : Ctx} {m : LoweredExpr} {x : Variable}
    {path : List String} {T : τ} (h : SemTypedPath GF Δ m x path T) :
    SemTyped GF Δ m T (fun _ => Δ) := by
  intro bindings hnd env
  iintro ⟨He, #H⟩
  iapply h bindings hnd env
  isplitl [He]
  · iexact He
  isplitr
  · iexact H
  iintro %w #Hw - He
  simp only [interpOutcome]
  iexists env
  iframe He
  isplitr
  · iexact Hw
  · iexact H

/-! ### Literals and variables -/

/--
The null literal is semantically well typed with type `Null`, and guarantees afterwards the facts
that held beforehand (`Δ`).
-/
public theorem SemTyped.null (Δ : Ctx) : SemTyped GF Δ .null Γ.Null (fun _ => Δ) := by
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_null]
  iintro ⟨He, #H⟩
  iapply wp_null
  inext
  simp only [interpOutcome]
  iexists env
  iframe He
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
    (hU : U ≤ T) : SemTyped GF Δ (.var x T) T (fun _ => Δ) :=
  (SemTypedPath.var hf hU).toSemTyped

/--
Reading property `p` of variable `x` is semantically well typed with its static type `T`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`);
- `U` is a subtype of `x`'s static type `Tx` (`U ≤ Tx`);
- the context says that `x` refers to an object with an instance variable named `p.name` that
  holds a value that satisfies `W` (`Fact.field x [p.name] W ∈ Δ`); and
- `W` is a subtype of `T` (`W ≤ T`).

It guarantees afterwards the facts that held beforehand (`Δ`). (`SemTypedPath` reads longer paths.)
-/
public theorem SemTyped.propertyGet {Δ : Ctx} {x : Variable} {p : Property} {U Tx W T : τ}
    (hx : Fact.var x U ∈ Δ) (hU : U ≤ Tx) (hf : Fact.field x [p.name] W ∈ Δ) (hW : W ≤ T) :
    SemTyped GF Δ (.propertyGet (.var x Tx) p T) T (fun _ => Δ) :=
  (SemTypedPath.propertyGet (path := []) (SemTypedPath.var hx hU) hf hW).toSemTyped

/-! ### Null checks -/

/--
A null check `m!` is semantically well typed with type `NonNull T`, if `m` is semantically well
typed with type `T` (`h`). It guarantees afterwards the facts that `m` guarantees (`Δ'`).
-/
public theorem SemTyped.nullCheck (L : TypeLaws τ) {Δ : Ctx} {m : LoweredExpr} {T : τ}
    {Δ' : Value → Ctx} (h : SemTyped GF Δ m T Δ') :
    SemTyped GF Δ (.nullCheck m) (Γ.NonNull T) Δ' := by
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_nullCheck]
  refine wp_fill_typed (Ki := .nullCheck) (h bindings hnd env) (fun v env' => ?_)
    (fun _ => true_intro)
  by_cases hv : v = .null
  · subst hv
    refine .trans ?_ wp_nullCheck_null
    iintro -
    inext
    simp only [interpOutcome]
    itrivial
  · refine .trans ?_ (wp_nullCheck hv)
    iintro ⟨He, #Hv, #H⟩
    inext
    simp only [interpOutcome]
    iexists env'
    iframe He
    isplitr
    · iapply interpVal_nonNull L hv $$ Hv
    · iexact H

/--
A null check `m!` of an expression `m` that reads the value at property path `path` from variable
`x` (such as `x!` or `x._f._g!`) is semantically well typed with type `NonNull T`, if `m` reads it
with static type `T` (`hm`).

It guarantees afterwards the facts that held beforehand, plus that the value at the path satisfies
`NonNull T` (`Fact.atPath x path (Γ.NonNull T) :: Δ`): the null check promotes the path.
-/
public theorem SemTyped.nullCheck_path (L : TypeLaws τ) {Δ : Ctx} {m : LoweredExpr}
    {x : Variable} {path : List String} {T : τ} (hm : SemTypedPath GF Δ m x path T) :
    SemTyped GF Δ (.nullCheck m) (Γ.NonNull T)
      (fun _ => Fact.atPath x path (Γ.NonNull T) :: Δ) := by
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_nullCheck]
  refine .trans ?_ (wp_bind_item .nullCheck)
  iintro ⟨He, #H⟩
  iapply hm bindings hnd env
  isplitl [He]
  · iexact He
  isplitr
  · iexact H
  iintro %w #Hw #Hp He
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
    ihave #Hw' := interpVal_nonNull L hw $$ Hw
    iexists env
    iframe He
    isplitr
    · iexact Hw'
    · iapply interpCtx_cons
      isplitr
      · iapply interpFact_atPath
        isplitr
        · iexact Hp
        · iexact Hw'
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
  simpa only [Fact.atPath] using SemTyped.nullCheck_path L (SemTypedPath.var (GF := GF) hf hU)

/--
A null check `x._f!` of property `p` of variable `x` is semantically well typed with type
`NonNull T`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`);
- `U` is a subtype of `x`'s static type `Tx` (`U ≤ Tx`);
- the context says that `x` refers to an object with an instance variable named `p.name` that
  holds a value that satisfies `W` (`Fact.field x [p.name] W ∈ Δ`); and
- `W` is a subtype of `T` (`W ≤ T`).

It guarantees afterwards the facts that held beforehand, plus that the instance variable holds a
value that satisfies `NonNull T` (`.field x [p.name] (Γ.NonNull T) :: Δ`): the null check promotes
`x._f`.
-/
public theorem SemTyped.nullCheck_field (L : TypeLaws τ) {Δ : Ctx} {x : Variable} {p : Property}
    {U Tx W T : τ} (hx : Fact.var x U ∈ Δ) (hU : U ≤ Tx) (hf : Fact.field x [p.name] W ∈ Δ)
    (hW : W ≤ T) :
    SemTyped GF Δ (.nullCheck (.propertyGet (.var x Tx) p T)) (Γ.NonNull T)
      (fun _ => .field x [p.name] (Γ.NonNull T) :: Δ) := by
  simpa only [Fact.atPath, List.nil_append] using SemTyped.nullCheck_path L
    (SemTypedPath.propertyGet (path := []) (SemTypedPath.var (GF := GF) hx hU) hf hW)

/-! ### Casts and is-expressions -/

/--
A cast `m as T` is semantically well typed with type `T`, if `m` is semantically well typed with
some type `S` (`h`). It guarantees afterwards the facts that `m` guarantees (`Δ'`).
-/
public theorem SemTyped.as {Δ : Ctx} {m : LoweredExpr} {S T : τ} {Δ' : Value → Ctx}
    (h : SemTyped GF Δ m S Δ') : SemTyped GF Δ (.as m T) T Δ' := by
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_as]
  refine wp_fill_typed (Ki := .as T) (h bindings hnd env) (fun v env' => ?_)
    (fun _ => true_intro)
  simp only [EctxItem.fill]
  iintro ⟨He, #Hv, #H⟩
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
        iexists env'
        iframe He
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
A cast `m as T` of an expression `m` that reads the value at property path `path` from variable
`x` (such as `x as T` or `x._f._g as T`) is semantically well typed with type `T`, if `m` reads it
with some static type `S` (`hm`).

It guarantees afterwards the facts that held beforehand, plus that the value at the path satisfies
`T` (`Fact.atPath x path T :: Δ`): the cast promotes the path.
-/
public theorem SemTyped.as_path {Δ : Ctx} {m : LoweredExpr} {x : Variable} {path : List String}
    {S T : τ} (hm : SemTypedPath GF Δ m x path S) :
    SemTyped GF Δ (.as m T) T (fun _ => Fact.atPath x path T :: Δ) := by
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_as]
  refine .trans ?_ (wp_bind_item (.as T))
  iintro ⟨He, #H⟩
  iapply hm bindings hnd env
  isplitl [He]
  · iexact He
  isplitr
  · iexact H
  iintro %v #Hv #Hp He
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
        iexists env
        iframe He
        isplitr
        · iexact Hv'
        · iapply interpCtx_cons
          isplitr
          · iapply interpFact_atPath
            isplitr
            · iexact Hp
            · iexact Hv'
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
  simpa only [Fact.atPath] using SemTyped.as_path (T := T) (SemTypedPath.var (GF := GF) hf hU)

/--
A cast `x._f as T` of property `p` of variable `x` is semantically well typed with type `T`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`);
- `U` is a subtype of `x`'s static type `Tx` (`U ≤ Tx`);
- the context says that `x` refers to an object with an instance variable named `p.name` that
  holds a value that satisfies `W` (`Fact.field x [p.name] W ∈ Δ`); and
- `W` is a subtype of the read's static type `Tp` (`W ≤ Tp`).

It guarantees afterwards the facts that held beforehand, plus that the instance variable holds a
value that satisfies `T` (`.field x [p.name] T :: Δ`): the cast promotes `x._f`.
-/
public theorem SemTyped.as_field {Δ : Ctx} {x : Variable} {p : Property} {U Tx W Tp T : τ}
    (hx : Fact.var x U ∈ Δ) (hU : U ≤ Tx) (hf : Fact.field x [p.name] W ∈ Δ) (hW : W ≤ Tp) :
    SemTyped GF Δ (.as (.propertyGet (.var x Tx) p Tp) T) T
      (fun _ => .field x [p.name] T :: Δ) := by
  simpa only [Fact.atPath, List.nil_append] using SemTyped.as_path (T := T)
    (SemTypedPath.propertyGet (path := []) (SemTypedPath.var (GF := GF) hx hU) hf hW)

/--
An is-expression `m is T` is semantically well typed with type `bool`, if `m` is semantically well
typed with some type `S`, guaranteeing facts afterwards that don't depend on its value (`h`). It
guarantees afterwards the facts that `m` guarantees (`Δ₁`).
-/
public theorem SemTyped.is {Δ Δ₁ : Ctx} {m : LoweredExpr} {S T : τ}
    (h : SemTyped GF Δ m S (fun _ => Δ₁)) : SemTyped GF Δ (.is m T) Γ.bool (fun _ => Δ₁) := by
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_is]
  refine wp_fill_typed (Ki := .is T) (h bindings hnd env) (fun v env' => ?_)
    (fun _ => true_intro)
  simp only [EctxItem.fill]
  iintro ⟨He, #Hv, #H⟩
  icases Hv with ⟨%S₀, #Hty, %hS, %hok⟩
  by_cases hb : ∃ b, RtSub S₀ T b
  · obtain ⟨b, hb⟩ := hb
    iapply wp_is hb
    isplitr
    · iexact Hty
    · inext
      simp only [interpOutcome]
      iexists env'
      iframe He
      isplitr
      · iapply interpVal_bool b le_rfl
      · iexact H
  · iapply wp_is_diverge (fun b h => hb ⟨b, h⟩)
    iexact Hty

/--
An is-expression `m is T` of an expression `m` that reads the value at property path `path` from
variable `x` (such as `x is T` or `x._f._g is T`) is semantically well typed with type `bool`, if
`m` reads it with some static type `S` (`hm`).

It guarantees afterwards the facts that held beforehand, plus, if it evaluates to `true`, that the
value at the path satisfies `T` (`Ctx.byCondition (Fact.atPath x path T :: Δ) Δ`): the
is-expression promotes the path when it's `true`.
-/
public theorem SemTyped.is_path {Δ : Ctx} {m : LoweredExpr} {x : Variable} {path : List String}
    {S T : τ} (hm : SemTypedPath GF Δ m x path S) :
    SemTyped GF Δ (.is m T) Γ.bool (Ctx.byCondition (Fact.atPath x path T :: Δ) Δ) := by
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_is]
  refine .trans ?_ (wp_bind_item (.is T))
  iintro ⟨He, #H⟩
  iapply hm bindings hnd env
  isplitl [He]
  · iexact He
  isplitr
  · iexact H
  iintro %v #Hv #Hp He
  simp only [DartLang.Outcome.toExpr, EctxItem.fill]
  icases Hv with ⟨%S₀, #Hty, %hS, %hok⟩
  by_cases hb : ∃ b, RtSub S₀ T b
  · obtain ⟨b, hb⟩ := hb
    iapply wp_is hb
    isplitr
    · iexact Hty
    · inext
      simp only [interpOutcome]
      iexists env
      iframe He
      isplitr
      · iapply interpVal_bool b le_rfl
      · cases b
        · simp only [Ctx.byCondition_false]
          iexact H
        · simp only [Ctx.byCondition_true]
          iapply interpCtx_cons
          isplitr
          · iapply interpFact_atPath
            isplitr
            · iexact Hp
            · iexists S₀
              isplitr
              · iexact Hty
              · ipureintro
                exact ⟨DartRuntimeTypeRepr.rtSub_true hb, hok⟩
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
  simpa only [Fact.atPath] using SemTyped.is_path (T := T) (SemTypedPath.var (GF := GF) hf hU)

/--
An is-expression `x._f is T` of property `p` of variable `x` is semantically well typed with type
`bool`, if:
- the context says that `x` holds a value that satisfies `U` (`Fact.var x U ∈ Δ`);
- `U` is a subtype of `x`'s static type `Tx` (`U ≤ Tx`);
- the context says that `x` refers to an object with an instance variable named `p.name` that
  holds a value that satisfies `W` (`Fact.field x [p.name] W ∈ Δ`); and
- `W` is a subtype of the read's static type `Tp` (`W ≤ Tp`).

It guarantees afterwards the facts that held beforehand, plus, if it evaluates to `true`, that the
instance variable holds a value that satisfies `T` (`Ctx.byCondition (.field x [p.name] T :: Δ)
Δ`): the is-expression promotes `x._f` when it's `true`.
-/
public theorem SemTyped.is_field {Δ : Ctx} {x : Variable} {p : Property} {U Tx W Tp T : τ}
    (hx : Fact.var x U ∈ Δ) (hU : U ≤ Tx) (hf : Fact.field x [p.name] W ∈ Δ) (hW : W ≤ Tp) :
    SemTyped GF Δ (.is (.propertyGet (.var x Tx) p Tp) T) Γ.bool
      (Ctx.byCondition (.field x [p.name] T :: Δ) Δ) := by
  simpa only [Fact.atPath, List.nil_append] using SemTyped.is_path (T := T)
    (SemTypedPath.propertyGet (path := []) (SemTypedPath.var (GF := GF) hx hU) hf hW)

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
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_cond]
  refine wp_fill_typed (Ki := .cond (m₂.bindVariables bindings) (m₃.bindVariables bindings) T)
    (h₁ bindings hnd env) (fun v env' => ?_) (fun _ => true_intro)
  simp only [EctxItem.fill]
  iintro ⟨He, #Hv, #H⟩
  ihave %hb := interpVal_bool_inv L $$ Hv
  obtain ⟨b, rfl⟩ := hb
  cases b
  · iapply wp_cond_false
    inext
    iapply h₃ bindings hnd env'
    iframe He
    iexact H
  · iapply wp_cond_true
    inext
    iapply h₂ bindings hnd env'
    iframe He
    iexact H

/-! ### Assignments -/

omit [DartGS τ hlc GF] [SemanticParams τ] in
/--
A fact remains when those about `v` are forgotten (`f ∈ Δ.forget v`) exactly when it's one of the
facts (`f ∈ Δ`) and isn't about `v` (`f.variable ≠ v`).
-/
public theorem Ctx.mem_forget {Δ : Ctx} {v : Variable} {f : Fact} :
    f ∈ Δ.forget v ↔ f ∈ Δ ∧ f.variable ≠ v := by
  simp [Ctx.forget]

/--
An assignment `v = m` is semantically well typed with the type `T` of its right-hand side, if:
- `v` is in scope beforehand (`Fact.decl v ∈ Δb`);
- `m` is semantically well typed with type `T` (`hm`), guaranteeing facts `Δa` afterwards; and
- if `v` is `final`, it hasn't been assigned after `m`, whatever value `m` evaluates to
  (`hfin`: `Fact.uninit v ∈ Δa w` for every `w`). The check comes after `m` because `m` runs before
  the assignment, and may itself assign to `v` (as in `x = (x = e)`).

It guarantees afterwards the facts that `m` guarantees, less those about `v` (including any
promotions of `v`, and facts about instance variables reached through `v`: `(Δa w).forget v`),
plus that `v` is in scope and holds a value that satisfies `T`:
`.var v T :: .decl v :: (Δa w).forget v`.

Flow analysis requires `T` to be a subtype of `v`'s declared type; this rule doesn't, and that
leaves no gap in soundness. The semantics doesn't associate a type with a variable: what a
variable holds only matters when it is read, and a read is only semantically well typed if the
facts beforehand say that the variable holds a value that satisfies the read's static type
(`SemTyped.var`). The proof that flow analysis is sound will have to establish those facts from
flow analysis's models, including, wherever flow analysis falls back on a variable's declared type
(for example, after a join that loses its promotions), that the variable holds a value that
satisfies its declared type. This means that the flow analysis soundness proof will have to prove
that `T` is a subtype of `v`'s declared type.
-/
public theorem SemTyped.variableSet {Δb : Ctx} {v : Variable} {m : LoweredExpr} {T : τ}
    {Δa : Value → Ctx} (hdecl : Fact.decl v ∈ Δb) (hm : SemTyped GF Δb m T Δa)
    (hfin : v.isFinal = true → ∀ w, Fact.uninit v ∈ Δa w) :
    SemTyped GF Δb (.variableSet v m) T (fun w => .var v T :: .decl v :: (Δa w).forget v) := by
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_variableSet]
  cases hl : bindings.lookup v with
  | none =>
    -- `v` is in scope, so it is bound.
    iintro ⟨-, #H⟩
    ihave %hdv := interpCtx_elim hdecl $$ H
    obtain ⟨ℓ, hl'⟩ := hdv
    rw [hl] at hl'
    cases hl'
  | some ℓ =>
  dsimp only
  refine wp_fill_typed (Ki := .variableSetAt v ℓ) (hm bindings hnd env) (fun w env' => ?_)
    (fun _ => true_intro)
  simp only [EctxItem.fill]
  iintro ⟨He, #Hw, #H'⟩
  ihave %hfin' : ⌜v.isFinal = true → env' v = .uninit⌝ $$ []
  · cases hvf : v.isFinal with
    | false =>
      ipureintro
      intro h
      cases h
    | true =>
      ihave %hu := interpCtx_elim (hfin hvf w) $$ H'
      obtain ⟨_, -, hu⟩ := hu
      ipureintro
      exact fun _ => hu
  icases interpEnv_acc (GF := GF) (env := env') hnd hl $$ He with ⟨⟨%hc, Hl⟩, Hback⟩
  iapply wp_variableSetAt hc hfin'
  isplitl [Hl]
  · inext
    iexact Hl
  inext
  iintro Hl
  ihave He := Hback $$ %(.val w) [Hl]
  · isplitr
    · ipureintro
      exact fun _ _ h => by cases h
    · iexact Hl
  simp only [interpOutcome]
  iexists env'.set v (.val w)
  iframe He
  isplitr
  · iexact Hw
  · iapply interpCtx_cons
    isplitr
    · iexists ℓ, w
      isplitr
      · ipureintro
        exact ⟨hl, Env.set_self _ _ _⟩
      · iexact Hw
    · iapply interpCtx_cons
      isplitr
      · ipureintro
        exact ⟨ℓ, hl⟩
      · iapply interpCtx_congr (bindings := bindings) (env := env') (fun _ _ => rfl)
          (fun f hf => (Env.set_ne (Ctx.mem_forget.1 hf).2 _).symm)
        iapply interpCtx_mono (fun f hf => (Ctx.mem_forget.1 hf).1)
        iexact H'

/-! ### Blocks and declarations -/

/--
An empty block is semantically well typed with type `Null`, and guarantees afterwards the facts
that held beforehand (`Δ`).
-/
public theorem SemTyped.block_nil (Δ : Ctx) :
    SemTyped GF Δ (.block []) Γ.Null (fun _ => Δ) := by
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_block, LoweredExpr.bindBlock_nil]
  iintro ⟨He, #H⟩
  iapply wp_blockNil
  inext
  simp only [interpOutcome]
  iexists env
  iframe He
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
  intro bindings hnd env
  rw [LoweredExpr.bindVariables_block, LoweredExpr.bindBlock_cons bindings hm]
  refine .trans ?_ (wp_blockCons (LoweredExpr.bindVariables_ne_declare bindings hm))
  refine .trans ?_ later_intro
  refine wp_fill_typed (Ki := .seq (.block (LoweredExpr.bindBlock bindings ms)))
    (h bindings hnd env) (fun v env' => ?_) (fun _ => true_intro)
  refine .trans ?_ wp_seq
  refine .trans ?_ later_intro
  have hr' := hr bindings hnd env'
  rw [LoweredExpr.bindVariables_block] at hr'
  iintro ⟨He, -, #H⟩
  iapply hr'
  iframe He
  iexact H

omit [SemanticParams τ] in
/--
The bindings for the body of a block that declares `v` at `ℓ` (`v` bound to `ℓ`, and the other
variables as before: `(v, ℓ) :: bindings.filter fun b => b.1 ≠ v`) bind each variable at most once
(`Nodup`), if `bindings` does (`hnd`).
-/
theorem nodup_declare {bindings : List (Variable × Loc)} (hnd : (bindings.map (·.1)).Nodup)
    (v : Variable) (ℓ : Loc) :
    (((v, ℓ) :: bindings.filter fun b => b.1 ≠ v).map (·.1)).Nodup := by
  rw [List.map_cons, List.nodup_cons]
  refine ⟨fun hmem => ?_, (List.filter_sublist.map _).nodup hnd⟩
  obtain ⟨b, hb, hbv⟩ := List.mem_map.1 hmem
  exact (by simpa using (List.mem_filter.1 hb).2 : b.1 ≠ v) hbv

/--
A block that starts with a declaration of `v` is semantically well typed with type `Null`, if the
rest of the block is semantically well typed with type `Null` (`h`), given:
- the facts that held beforehand, less those about any outer `v`, which the declaration shadows
  (`Δ.forget v`);
- that `v` is in scope (`Fact.decl v`); plus
- if `v` starts out holding the null object (`sN`), that `v` holds a value that satisfies `T`
  (`Fact.var v T`), and otherwise, that `v` hasn't been assigned (`Fact.uninit v`).

That requires `Null` to be a subtype of `T` (`hsN`), which flow analysis ensures by setting
`startsNull` only for nullable types. It guarantees afterwards the facts that the rest of the block
guarantees, less those about `v`, since `v` goes out of scope (`Δ₂.forget v`). The cell of any outer
`v` is untouched.
-/
public theorem SemTyped.block_declare {Δ Δ₂ : Ctx} {v : Variable} {T : τ} {sN : Bool}
    {ms : List LoweredExpr} (hsN : sN = true → Γ.Null ≤ T)
    (h : SemTyped GF ((if sN then [Fact.var v T] else [Fact.uninit v]) ++ Fact.decl v :: Δ.forget v)
      (.block ms) Γ.Null (fun _ => Δ₂)) :
    SemTyped GF Δ (.block (.declare v T sN :: ms)) Γ.Null (fun _ => Δ₂.forget v) := by
  intro bindings hnd env
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Cell, (if sN then .val .null else .uninit) = c₀ := ⟨_, rfl⟩
  have hc₀obj : ∀ C fs, c₀ ≠ .object C fs := by
    rw [← hc₀]
    cases sN <;> intro _ _ h <;> cases h
  rw [LoweredExpr.bindVariables_block, LoweredExpr.bindBlock_declare]
  iintro ⟨He, #H⟩
  iapply wp_blockDeclare
  inext
  rw [hc₀]
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
  have hlookv : ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v).lookup v = some ℓ := by
    simp [List.lookup]
  -- The cells of the bindings other than `v`'s don't depend on what `v`'s cell holds.
  have hother : ∀ (env₁ : Env) (c : Cell),
      interpEnv (GF := GF) (bindings.filter fun b => b.1 ≠ v) (env₁.set v c) =
        interpEnv (bindings.filter fun b => b.1 ≠ v) env₁ := fun env₁ c =>
    interpEnv_congr fun b hb => Env.set_ne (hne b hb) c
  -- The cells of the bindings of `v` (at most one, for an outer `v`) are kept aside, unchanged.
  have hvs : ∀ (env₁ : Env),
      interpEnv (GF := GF) (bindings.filter fun b => b.1 = v) (env₁.set v (env v)) =
        interpEnv (bindings.filter fun b => b.1 = v) env := fun env₁ =>
    interpEnv_congr fun b hb => by
      have : b.1 = v := by simpa using (List.mem_filter.1 hb).2
      rw [this, Env.set_self]
  -- Entering the block: `v`'s new cell, and the cells of the other variables.
  have henter : interpCell (GF := GF) ℓ c₀ ∗ interpEnv (bindings.filter fun b => b.1 ≠ v) env ⊢
      interpEnv ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v) (env.set v c₀) := by
    simp only [interpEnv, Env.set_self, hother]
    exact .rfl
  -- Leaving the block: `v`'s cell is dropped.
  have hleave : ∀ env₂ : Env,
      interpEnv (GF := GF) ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v) env₂ ⊢
        interpEnv (bindings.filter fun b => b.1 ≠ v) env₂ := fun env₂ => by
    simp only [interpEnv]
    exact sep_elim_right
  icases (interpEnv_split (GF := GF) bindings env v).1 $$ He with ⟨Hv, Hrest⟩
  -- The context for the rest of the block.
  ihave #Hfor : interpCtx ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v) (env.set v c₀)
      (Δ.forget v) $$ []
  · iapply interpCtx_congr (bindings := bindings) (env := env)
      (fun f hf => (hlook _ (Ctx.mem_forget.1 hf).2).symm)
      (fun f hf => (Env.set_ne (Ctx.mem_forget.1 hf).2 c₀).symm)
    iapply interpCtx_mono (fun f hf => (Ctx.mem_forget.1 hf).1)
    iexact H
  ihave #Hdecl : interpCtx ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v) (env.set v c₀)
      (Fact.decl v :: Δ.forget v) $$ []
  · iapply interpCtx_cons
    isplitr
    · ipureintro
      exact ⟨ℓ, hlookv⟩
    · iexact Hfor
  ihave #Hin : interpCtx ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v) (env.set v c₀)
      ((if sN then [Fact.var v T] else [Fact.uninit v]) ++ Fact.decl v :: Δ.forget v) $$ []
  · cases sN with
    | false =>
      simp only [Bool.false_eq_true, ite_false, List.singleton_append]
      simp only [Bool.false_eq_true, ite_false] at hc₀
      iapply interpCtx_cons
      isplitr
      · ipureintro
        exact ⟨ℓ, hlookv, by rw [Env.set_self, ← hc₀]⟩
      · iexact Hdecl
    | true =>
      simp only [ite_true, List.singleton_append]
      simp only [ite_true] at hc₀
      iapply interpCtx_cons
      isplitr
      · iexists ℓ, .null
        isplitr
        · ipureintro
          exact ⟨hlookv, by rw [Env.set_self, ← hc₀]⟩
        · iapply interpVal_null (hsN rfl)
      · iexact Hdecl
  ihave Hwp := h ((v, ℓ) :: bindings.filter fun b => b.1 ≠ v) (nodup_declare hnd v ℓ)
    (env.set v c₀) $$ [Hℓ Hrest]
  · isplitl [Hℓ Hrest]
    · iapply henter
      isplitl [Hℓ]
      · isplitr
        · ipureintro
          exact hc₀obj
        · iexact Hℓ
      · iexact Hrest
    · iexact Hin
  iapply wp_wand $$ Hwp
  iintro %o Ho
  cases o with
  | normal w =>
    simp only [interpOutcome]
    icases Ho with ⟨%env₂, He₂, #Hw, #H₂⟩
    iexists env₂.set v (env v)
    isplitl [He₂ Hv]
    · iapply (interpEnv_split (GF := GF) bindings (env₂.set v (env v)) v).2
      rw [hvs, hother]
      isplitl [Hv]
      · iexact Hv
      · iapply hleave $$ He₂
    isplitr
    · iexact Hw
    · iapply interpCtx_congr (bindings := (v, ℓ) :: bindings.filter fun b => b.1 ≠ v)
        (env := env₂)
        (fun f hf => hlook _ (Ctx.mem_forget.1 hf).2)
        (fun f hf => (Env.set_ne (Ctx.mem_forget.1 hf).2 _).symm)
      iapply interpCtx_mono (fun f hf => (Ctx.mem_forget.1 hf).1)
      iexact H₂
  | throwing _ =>
    simp only [interpOutcome]
    itrivial

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
  · intro bindings hnd env
    rw [LoweredExpr.bindVariables_declare]
    refine .trans ?_ wp_declare
    refine .trans ?_ later_intro
    have hb' := hb bindings hnd env
    rw [LoweredExpr.bindVariables_block, LoweredExpr.bindBlock_declare,
      LoweredExpr.bindBlock_nil] at hb'
    exact hb'
  · obtain ⟨hf, hfv⟩ := Ctx.mem_forget.1 hf
    refine Ctx.mem_forget.2 ⟨List.mem_append_right _ (List.mem_cons_of_mem _ ?_), hfv⟩
    exact Ctx.mem_forget.2 ⟨hf, hfv⟩

end DartSemantics
