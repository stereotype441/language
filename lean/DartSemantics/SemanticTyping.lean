module
public import DartSemantics.Bind
public import DartSemantics.PrimitiveLaws

/-!
# Semantic typing

A *semantic* typing judgment for `LoweredExpr`s, defined with the program logic. An expression is
semantically well typed in a context if, whenever it starts running in a state where everything
the context promises holds:
- it can't get stuck, and
- if it completes normally, its value satisfies the expression's static type (that is, the value's
  dynamic type is a subtype of it; see `interpVal`), and everything that the context promises for
  afterwards holds.

The typing rules say that an expression *has static type `T`* when it is semantically well typed
with type `T` (`SemTyped`).

The judgment is *flow-sensitive*, as flow analysis is: a context records what is known about
variables and fields, and evaluating an expression can add to that knowledge. For a condition, what
is known afterwards can depend on whether it evaluated to `true` or `false`.

`Compat.lean` proves one *compatibility lemma* for each kind of expression: a typing rule, proved
sound with respect to the semantics. `Safety.lean` derives the safety theorem from adequacy: an
expression that is semantically well typed doesn't get stuck. Since a promotion check that fails
gets stuck when `SemanticParams.promotionChecks` is `PromotionChecks.verify`, this includes the
guarantee that every promotion it relies on is sound.

Everything is stated for an arbitrary type representation `τ`, assuming only the laws in
`TypeLaws`, and for every choice of `SemanticParams`.

## Connection to flow analysis

Contexts (`Ctx`, lists of `Fact`s) are deliberately simpler than flow analysis's models: they
record only what a running program can rely on. The intended next step is to translate each flow
model to the facts it implies (an ordinary Lean function), and prove that the `LoweredExpr` that
flow analysis produces for each construct is semantically well typed, from the facts of the model
before it to the facts of the model after it. That is the soundness theorem for flow analysis.
Keeping the translation separate keeps the program logic out of reasoning about models (joins,
demotions, and so on), and keeps this file independent of how flow analysis represents them.

## Simplifications

The subset of Dart modeled so far has no assignments, so a variable's cell never changes once it
has been initialized. The judgment exploits this: a context's promises about a variable are backed
by a persistent points-to for its cell. Once the semantics has assignments, this will need iris
invariants and ghost state instead.

A property read is only typed when its receiver is a variable `x`, and the context promises that
`x` refers to an object with an instance variable of that name (`Fact.field`). Reading a property
whose getter is user code, or of an object that isn't held in a variable, waits for the semantics
to have class declarations and calls (see `SemanticParams.getterImpl`).
-/

namespace DartSemantics

open DartLang Iris Iris.BI Iris.ProgramLogic Iris.Std

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)
local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Cell" => Cell (τ := τ)

variable (τ) in
/--
Laws about the type representation that the typing rules rely on. They hold in Dart, and for
`SimpleType` (see the tests), but don't follow from `DartTypeRepr`, whose special types are
otherwise unrelated constants.
-/
public structure TypeLaws : Prop where
  /-- `bool` isn't nullable, so the null object isn't a boolean (for conditionals). -/
  not_null_le_bool : ¬ Γ.Null ≤ Γ.bool
  /-- A non-nullable subtype of `T` is a subtype of `NonNull T` (for null checks). -/
  le_nonNull {S T : τ} : ¬ Γ.Null ≤ S → S ≤ T → S ≤ Γ.NonNull T

/--
What the typing rules need to know about a value whose dynamic type is `S`, besides `S` itself: if
the value is an object (other than the null object and booleans), its class isn't nullable, and
isn't a subtype of `bool`. (In Dart, `bool` can't be extended or implemented.)
-/
@[expose]
public def ValOk : Value → τ → Prop
  | .obj _, S => ¬ Γ.Null ≤ S ∧ ¬ S ≤ Γ.bool
  | _, _ => True

/--
A fact that a context records: what is known about a variable at a point in the program.
-/
public inductive Fact where
  /-- Variable `x` holds a value that satisfies `T`. -/
  | var (x : Variable) (T : τ)
  /--
  Variable `x` refers to an object that has an instance variable named `name`, holding a value
  that satisfies `T`.

  This only describes one step from a variable, so properties of properties (`x._y._z`) can't be
  read or promoted yet. Generalizing to property paths (`x` followed by a list of instance variable
  names, like flow analysis's promotion keys) is straightforward; it is left until the semantics has
  writes, which must invalidate facts about every path through what they write.
  -/
  | field (x : Variable) (name : String) (T : τ)
  deriving DecidableEq

local notation "Fact" => Fact (τ := τ)

/-- The variable that a fact is about. -/
@[expose]
public def Fact.variable : Fact → Variable
  | .var x _ => x
  | .field x _ _ => x

/-- A context: the facts known at a point in the program. -/
public abbrev Ctx := List Fact

local notation "Ctx" => Ctx (τ := τ)

/--
Forget the facts about variable `v` (when a declaration of `v` shadows it, or it goes out of
scope).
-/
@[expose]
public def Ctx.forget (Δ : Ctx) (v : Variable) : Ctx := Δ.filter (fun f => f.variable ≠ v)

/--
The facts known after a condition, as a function of its value: `Δt` if it evaluated to `true`, and
`Δf` otherwise.
-/
@[expose]
public def Ctx.byCondition (Δt Δf : Ctx) : Value → Ctx
  | .bool true => Δt
  | _ => Δf

omit Γ in
/-- After a condition that evaluated to `true`, the facts known are `Δt`. -/
@[simp]
public theorem Ctx.byCondition_true (Δt Δf : Ctx) : Ctx.byCondition Δt Δf (.bool true) = Δt := rfl

omit Γ in
/-- After a condition that evaluated to `false`, the facts known are `Δf`. -/
@[simp]
public theorem Ctx.byCondition_false (Δt Δf : Ctx) : Ctx.byCondition Δt Δf (.bool false) = Δf :=
  rfl

section Interp

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]

/--
The value interpretation of type `T`: the values that *satisfy* `T`, that is, whose dynamic types
are subtypes of `T` (see the README's documentation conventions), and that also meet `ValOk`, which
the typing rules need. The docs below say "satisfies `T`" for this.
-/
@[expose, reducible]
public def interpVal (T : τ) (v : Value) : IProp GF :=
  iprop(∃ S, HasDynamicType v S ∗ ⌜S ≤ T ∧ ValOk v S⌝)

public instance interpVal_persistent (T : τ) (v : Value) :
    Persistent (interpVal (GF := GF) T v) := by
  unfold interpVal
  infer_instance

/--
The interpretation of a fact, given the cells that variables are bound to (`bindings`). The cells
of the variables, and of the instance variables, are owned persistently: they never change.
-/
@[expose, reducible]
public def interpFact (bindings : List (Variable × Loc)) : Fact → IProp GF
  | .var x T => iprop(∃ ℓ v, ⌜bindings.lookup x = some ℓ⌝ ∗ ℓ ↦{.discard} (.val v : Cell) ∗
      interpVal T v)
  | .field x name T => iprop(∃ ℓ ℓo C fs ℓf w,
      ⌜bindings.lookup x = some ℓ ∧ fs.lookup name = some ℓf⌝ ∗
      ℓ ↦{.discard} (.val (.obj ℓo) : Cell) ∗ ℓo ↦{.discard} (.object C fs : Cell) ∗
      ℓf ↦{.discard} (.val w : Cell) ∗ interpVal T w)

public instance interpFact_persistent (bindings : List (Variable × Loc)) (f : Fact) :
    Persistent (interpFact (GF := GF) bindings f) := by
  cases f <;> unfold interpFact <;> infer_instance

/-- The interpretation of a context: every fact in it holds. -/
@[expose]
public def interpCtx (bindings : List (Variable × Loc)) (Δ : Ctx) : IProp GF :=
  iprop(□ ∀ f, ⌜f ∈ Δ⌝ → interpFact bindings f)

public instance interpCtx_persistent (bindings : List (Variable × Loc)) (Δ : Ctx) :
    Persistent (interpCtx (GF := GF) bindings Δ) := by
  unfold interpCtx
  infer_instance

/--
What an expression of static type `T` promises when it completes with outcome `o`: if it completes
normally with value `v`, then `v` satisfies `T`, and the facts `Δa v` hold afterwards. If it
throws, nothing.
-/
@[expose]
public def interpOutcome (bindings : List (Variable × Loc)) (T : τ) (Δa : Value → Ctx) :
    DartLang.Outcome (τ := τ) → IProp GF
  | .normal v => iprop(interpVal T v ∗ interpCtx bindings (Δa v))
  | .throwing _ => iprop(True)

variable [SemanticParams τ]

variable (GF) in
/--
The semantic typing judgment `SemTyped Δb m T Δa`: whatever cells `m`'s free variables are bound
to, if the facts in `Δb` hold before, then running `m` doesn't get stuck, and if it completes
normally with value `v`, then `v` satisfies `T`, and the facts `Δa v` hold after.
-/
@[expose]
public def SemTyped (Δb : Ctx) (m : LoweredExpr) (T : τ) (Δa : Value → Ctx) : Prop :=
  ∀ bindings, interpCtx (GF := GF) bindings Δb ⊢
    WP (m.bindVariables bindings) {{ o, interpOutcome bindings T Δa o }}

/-! ### The value interpretation -/

omit [SemanticParams τ] in
/-- A value that satisfies `T` also satisfies every supertype of `T`. -/
public theorem interpVal_mono {T T' : τ} {v : Value} (h : T ≤ T') :
    interpVal (GF := GF) T v ⊢ interpVal T' v := by
  unfold interpVal
  iintro ⟨%S, #Hty, %hS, %hok⟩
  iexists S
  isplitr
  · iexact Hty
  · ipureintro
    exact ⟨le_trans hS h, hok⟩

omit [SemanticParams τ] in
/-- The null object satisfies every supertype of `Null`. -/
public theorem interpVal_null {T : τ} (h : Γ.Null ≤ T) : ⊢ interpVal (GF := GF) T .null := by
  unfold interpVal
  iexists Γ.Null
  isplitr
  · iapply HasDynamicType.null
  · ipureintro
    exact ⟨h, trivial⟩

omit [SemanticParams τ] in
/-- A boolean satisfies every supertype of `bool`. -/
public theorem interpVal_bool {T : τ} (b : Bool) (h : Γ.bool ≤ T) :
    ⊢ interpVal (GF := GF) T (.bool b) := by
  unfold interpVal
  iexists Γ.bool
  isplitr
  · iapply HasDynamicType.bool
  · ipureintro
    exact ⟨h, trivial⟩

omit [SemanticParams τ] in
/-- A value that satisfies `bool` is a boolean. -/
public theorem interpVal_bool_inv (L : TypeLaws τ) {v : Value} :
    interpVal (GF := GF) Γ.bool v ⊢ ⌜∃ b, v = .bool b⌝ := by
  unfold interpVal
  cases v with
  | null =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, %hS, -⟩
    subst h
    exact absurd hS L.not_null_le_bool
  | bool b =>
    iintro -
    ipureintro
    exact ⟨b, rfl⟩
  | obj ℓ =>
    iintro ⟨%S, -, %hS, %hok⟩
    exact absurd hS hok.2
  | error e =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim
  | cont k =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim

omit [SemanticParams τ] in
/-- A value other than the null object that satisfies `T` also satisfies `NonNull T`. -/
public theorem interpVal_nonNull (L : TypeLaws τ) {T : τ} {v : Value} (hv : v ≠ .null) :
    interpVal (GF := GF) T v ⊢ interpVal (Γ.NonNull T) v := by
  unfold interpVal
  cases v with
  | null => exact absurd rfl hv
  | bool b =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, %hS, %hok⟩
    subst h
    iexists Γ.bool
    isplitr
    · ipureintro
      rfl
    · ipureintro
      exact ⟨L.le_nonNull L.not_null_le_bool hS, hok⟩
  | obj ℓ =>
    iintro ⟨%S, #Hty, %hS, %hok⟩
    iexists S
    isplitr
    · iexact Hty
    · ipureintro
      exact ⟨L.le_nonNull hok.1 hS, hok⟩
  | error e =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim
  | cont k =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim

/-! ### Contexts -/

omit [SemanticParams τ] in
/-- A fact about `x` only depends on the cell that `x` is bound to. -/
public theorem interpFact_congr {bindings bindings' : List (Variable × Loc)} {f : Fact}
    (h : bindings.lookup f.variable = bindings'.lookup f.variable) :
    interpFact (GF := GF) bindings f ⊢ interpFact bindings' f := by
  cases f <;> simp only [Fact.variable] at h <;> simp only [interpFact, h] <;> exact .rfl

omit [SemanticParams τ] in
/-- If a context holds, every context with fewer facts holds too. -/
public theorem interpCtx_mono {bindings : List (Variable × Loc)} {Δ Δ₀ : Ctx}
    (h : ∀ f ∈ Δ, f ∈ Δ₀) : interpCtx (GF := GF) bindings Δ₀ ⊢ interpCtx bindings Δ := by
  unfold interpCtx
  iintro #H
  imodintro
  iintro %f %hf
  iapply H
  ipureintro
  exact h f hf

omit [SemanticParams τ] in
/-- A fact in a context holds if the whole context holds. -/
public theorem interpCtx_elim {bindings : List (Variable × Loc)} {Δ : Ctx} {f : Fact}
    (h : f ∈ Δ) : interpCtx (GF := GF) bindings Δ ⊢ interpFact bindings f := by
  unfold interpCtx
  iintro #H
  iapply H
  ipureintro
  exact h

omit [SemanticParams τ] in
/-- The empty context promises nothing. -/
public theorem interpCtx_nil (bindings : List (Variable × Loc)) :
    ⊢ interpCtx (GF := GF) bindings ([] : Ctx) := by
  unfold interpCtx
  imodintro
  iintro %f %hf
  exact absurd hf List.not_mem_nil

omit [SemanticParams τ] in
/-- A context holds if one of its facts holds and the rest of it holds. -/
public theorem interpCtx_cons {bindings : List (Variable × Loc)} {f : Fact} {Δ : Ctx} :
    interpFact (GF := GF) bindings f ∗ interpCtx bindings Δ ⊢ interpCtx bindings (f :: Δ) := by
  unfold interpCtx
  iintro ⟨#Hf, #H⟩
  imodintro
  iintro %f' %hf'
  rcases List.mem_cons.1 hf' with rfl | h
  · iexact Hf
  · iapply H
    ipureintro
    exact h

omit [SemanticParams τ] in
/-- A context only depends on the cells that the variables it has facts about are bound to. -/
public theorem interpCtx_congr {bindings bindings' : List (Variable × Loc)} {Δ : Ctx}
    (h : ∀ f ∈ Δ, bindings.lookup f.variable = bindings'.lookup f.variable) :
    interpCtx (GF := GF) bindings Δ ⊢ interpCtx bindings' Δ := by
  unfold interpCtx
  iintro #H
  imodintro
  iintro %f %hf
  iapply interpFact_congr (h f hf)
  iapply H
  ipureintro
  exact hf

/-! ### Structural rules -/

/--
Weakening: an expression that has static type `T` given facts `Δb` before and promising facts `Δa`
after also has every supertype `T'` of `T` as its static type given more facts `Δb'` before
(`hin`), promising fewer facts `Δa'` after (`hout`). Requiring more before and promising less
after both make the claim weaker, as for the precondition and postcondition of a Hoare triple.
-/
public theorem SemTyped.weaken {Δb Δb' : Ctx} {m : LoweredExpr} {T T' : τ}
    {Δa Δa' : Value → Ctx} (h : SemTyped GF Δb m T Δa) (hin : ∀ f ∈ Δb, f ∈ Δb')
    (hT : T ≤ T') (hout : ∀ v, ∀ f ∈ Δa' v, f ∈ Δa v) : SemTyped GF Δb' m T' Δa' := by
  intro bindings
  refine (interpCtx_mono hin).trans ((h bindings).trans (wp_mono fun o => ?_))
  cases o with
  | normal v => exact sep_mono (interpVal_mono hT) (interpCtx_mono (hout v))
  | throwing _ => exact .rfl

/--
To show that running an evaluation context item `Ki` around an expression `e` satisfies a
postcondition `Ψ`, given that `e` satisfies a typing postcondition (`H`), it suffices to show that
running `Ki` around each value `e` can complete normally with satisfies `Ψ` (`Hn`), and that `Ψ`
holds of throwing any exception (`Ht`): an exception thrown by `e` propagates out of `Ki`.
-/
public theorem wp_fill_typed {P : IProp GF} {Ki : EctxItem (τ := τ)} {e : LoweredExpr}
    {bindings : List (Variable × Loc)} {T : τ} {Δa : Value → Ctx}
    {Ψ : DartLang.Outcome (τ := τ) → IProp GF}
    (H : P ⊢ WP e {{ o, interpOutcome bindings T Δa o }})
    (Hn : ∀ v, interpVal T v ∗ interpCtx bindings (Δa v) ⊢ WP (Ki.fill (.val v)) {{ Ψ }})
    (Ht : ∀ v, ⊢ Ψ (.throwing v)) : P ⊢ WP (Ki.fill e) {{ Ψ }} := by
  refine H.trans ((wp_mono fun o => ?_).trans (wp_bind_item Ki))
  cases o with
  | normal v => exact Hn v
  | throwing v =>
    refine .trans ?_ (wp_bubble Ki v)
    iintro -
    inext
    iapply Ht

end Interp

end DartSemantics
