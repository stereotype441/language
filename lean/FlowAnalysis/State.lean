module
public import DartLang.Elements
public import FlowAnalysis.Key.Basic
public import FlowAnalysis.PromotionChain.Basic
public import DartLang.Types
public import FlowAnalysis.PromotionModel.Basic

/-!
# Flow models

This module defines `FlowModel`, the specification's model of everything flow analysis knows at a
particular point in a function: a promotion model for each promotable location it is tracking,
named by its `Key`. It follows the flow models of the "Models" section of `flow-analysis.md`, minus
reachability, which isn't modeled yet.

It defines the operations on flow models that the elaboration rules need (`set`, `eraseRooted`,
`join`, `infoFor`, `currentTypeOf`), and the well-formedness condition that elaboration preserves
(`FlowModel.WellFormed`). It also defines `ExprModel`, which packages what flow analysis learns from
analyzing an expression.
-/

namespace FlowAnalysis
open DartLang

variable {τ : Type} [DartTypeRepr τ] {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionModel" => PromotionModel (τ := τ)
local notation "Key" => Key (ℓ := ℓ)
local notation "Reference" => Reference (ℓ := ℓ)

/-- The state of a function at a particular point in its execution. -/
@[ext]
public structure FlowModel where
  /-- Partial function mapping `Key`s to type promotion information. -/
  promotionInfo : Key → Option PromotionModel

local notation "FlowModel" => FlowModel (τ := τ) (ℓ := ℓ)

/-- The initial state of flow analysis. -/
@[expose]
public def FlowModel.empty : FlowModel := ⟨fun _ => none⟩

/-- `fm.set k pm` returns a modified `FlowModel` in which the model stored at `k` is `pm`. -/
@[expose]
public def FlowModel.set (fm : FlowModel) (k : Key)
    (pm : PromotionModel) : FlowModel :=
  ⟨fun k' => if k = k' then pm else fm.promotionInfo k'⟩

/--
`fm.eraseRooted decl` is `fm` with every property target rooted at the variable declared at `decl`
removed from its domain. Mirrors the `PI'` of the specification's `assign(x, E, M)` and of its
**Local variable declaration** rule: once `decl` holds a new value, such a property target names a
property of a different value, so its promotions no longer apply.
-/
@[expose]
public def FlowModel.eraseRooted (fm : FlowModel) (decl : ℓ) : FlowModel :=
  ⟨fun k =>
    match k with
    | .var _ => fm.promotionInfo k
    | .property root _ => if root = decl then none else fm.promotionInfo k⟩

/--
`fm₁.join fm₂` is the flow model at a point where two control flow paths, whose flow models are
`fm₁` and `fm₂`, come together: each key's promotion model is the join of its promotion models on
the two paths (`PromotionModel.join`), and keys that only one path tracks are dropped. Mirrors the
specification's `join`, minus reachability.
-/
-- TODO: implement full `join` behavior.
@[expose]
public def FlowModel.join (fm₁ fm₂ : FlowModel) : FlowModel :=
  ⟨fun k =>
     match fm₁.promotionInfo k with
     | none => none
     | some pm₁ =>
         match fm₂.promotionInfo k with
         | none => none
         | some pm₂ => pm₁.join pm₂⟩

/--
`fm.infoFor r` is the promotion model of the location that `r` refers to: the one `fm` stores under
`r.key` if there is one, and otherwise a fresh promotion model, if the value read is tracked.
Mirrors Dart's `FlowModel.infoFor`.

The result is `none` only if there is no stored model and `r` isn't tracked, which happens only for
a write-captured variable (see `Reference.var`). In Dart, such a reference has a fresh version,
so `infoFor` always returns a model.
-/
@[expose]
public def FlowModel.infoFor (fm : FlowModel) (r : Reference) : Option PromotionModel :=
  match fm.promotionInfo r.key with
  | some pm => some pm
  | none => if r.tracked then some PromotionModel.fresh else none

/--
`fm.currentTypeOf ref? T` is the type of a read of the location that `ref?` refers to, given that
its declared type is `T`: the promoted type if `fm` has a promotion model for it, and `T` otherwise.

Mirrors the computation of the type in Dart's `_handleProperty`. That looks up the stored promotion
model directly rather than using `infoFor`, but the difference is unobservable, because a fresh
model has no promotions.
-/
@[expose]
public def FlowModel.currentTypeOf (fm : FlowModel) (ref? : Option Reference) (T : τ) : τ :=
  match ref?.bind fun r => fm.promotionInfo r.key with
  | some pm => pm.currentType T
  | none => T

-- FlowModel Theorems --

/--
After setting key `k` to `pm`, the promotion info for `k'` is `pm` if `k = k'`, and otherwise what
it was before.
-/
@[simp]
public theorem FlowModel.promotionInfo_set {fm : FlowModel} {k k' pm} :
    (fm.set k pm).promotionInfo k' = if k = k' then some pm else fm.promotionInfo k' := by
  simp_all [FlowModel.set]

-- Decidable equality of labels is only needed in order to compare or join keys, so omit it from
-- this lemma.
omit [DecidableEq ℓ] in
/--
Extensionality: flow models with the same promotion info for every key (`h`) are equal
(`fm = fm'`).
-/
public theorem FlowModel.extensionality {fm fm' : FlowModel}
    (h : ∀ k : Key, fm.promotionInfo k = fm'.promotionInfo k) : fm = fm' := by
  revert h
  rcases fm; rename_i promotionInfo
  rcases fm'; rename_i promotionInfo'
  simp
  apply funext

/--
Setting a key `k` to the promotion model `pm` it already has (`hlookup`) leaves the flow model
unchanged.

This is useful for reasoning about elaboration rules that unconditionally update `promotionInfo`, in
cases where the updated value turns out to be the value that was already there.
-/
@[simp]
public theorem FlowModel.set_self {fm : FlowModel} {k : Key}
    {pm : PromotionModel} (hlookup : fm.promotionInfo k = some pm) : fm.set k pm = fm := by
  apply extensionality; intro k'
  simp only [promotionInfo_set]
  split <;> simp_all

omit [DecidableEq ℓ] in
/-- Joining a flow model with itself gives the same flow model (`fm.join fm = fm`). -/
@[simp]
public theorem FlowModel.join_idempotent (fm : FlowModel) :
    fm.join fm = fm := by
  apply extensionality; intro k
  simp [FlowModel.join]
  cases fm.promotionInfo k <;> simp_all

/--
`FlowModel.join` is idempotent, as an instance of the standard library's `Std.IdempotentOp` class.
-/
public instance FlowModel.instIdempotentOpJoin :
    Std.IdempotentOp (FlowModel.join (τ := τ) (ℓ := ℓ)) where
  idempotent := join_idempotent

omit [DecidableEq ℓ] in
/-- `FlowModel.join` keeps a key exactly when both flow models have it. -/
public theorem FlowModel.promotionInfo_join {fm₁ fm₂ : FlowModel} {k : Key} :
    (fm₁.join fm₂).promotionInfo k =
      (fm₁.promotionInfo k).bind fun pm₁ => (fm₂.promotionInfo k).map pm₁.join := by
  simp only [FlowModel.join]
  cases fm₁.promotionInfo k <;> simp
  split <;> simp_all

/-- `eraseRooted` leaves every variable's promotion model alone. -/
@[simp]
public theorem FlowModel.promotionInfo_eraseRooted_var {fm : FlowModel} {decl decl' : ℓ} :
    (fm.eraseRooted decl).promotionInfo (.var decl') = fm.promotionInfo (.var decl') := rfl

/--
`eraseRooted decl` removes the property targets rooted at `decl`, and leaves the others alone.
-/
@[simp]
public theorem FlowModel.promotionInfo_eraseRooted_property {fm : FlowModel} {decl root : ℓ}
    {path : List String} :
    (fm.eraseRooted decl).promotionInfo (.property root path) =
      if root = decl then none else fm.promotionInfo (.property root path) := rfl

/--
A flow model is *well formed* if every property target it has an entry for is rooted at a variable
that it's tracking: one that has an entry, and isn't write captured.

This is what the specification's rules guarantee: an entry for a property target is only created
by promoting a reference to it, which can only be made from a tracked variable (see
`Reference.property?`), and it is removed when the variable is assigned or declared
(`FlowModel.eraseRooted`).

Elaboration preserves it: see `ElabStmt.wellFormed`.
-/
@[expose]
public def FlowModel.WellFormed (fm : FlowModel) : Prop :=
  ∀ root path pm, fm.promotionInfo (.property root path) = some pm →
    ∃ pmv, fm.promotionInfo (.var root) = some pmv ∧ pmv.writeCaptured = false

/--
A reference `r` is *valid in* the flow model `fm` if, when it's tracked, its root variable is
tracked by `fm`: it has an entry, and isn't write captured. Promoting a valid reference preserves
`FlowModel.WellFormed` (`FlowModel.WellFormed.tryPromote`).
-/
@[expose]
public def Reference.ValidIn (r : Reference) (fm : FlowModel) : Prop :=
  r.tracked → ∃ pmv, fm.promotionInfo (.var r.root) = some pmv ∧ pmv.writeCaptured = false

omit [DecidableEq ℓ] in
/-- The initial flow model is well formed, since it holds nothing at all. -/
public theorem FlowModel.WellFormed.empty : (FlowModel.empty (τ := τ) (ℓ := ℓ)).WellFormed := by
  intro _ _ _ hlookup
  simp [FlowModel.empty] at hlookup

/--
Erasing the property targets rooted at `decl` preserves well-formedness, and makes it hold whatever
`decl`'s promotion model is replaced with: if `fm` is well formed (`hwf`), so is
`(fm.eraseRooted decl).set (.var decl) pm`.
-/
public theorem FlowModel.WellFormed.eraseRooted_set {fm : FlowModel} (hwf : fm.WellFormed)
    (decl : ℓ) (pm : PromotionModel) :
    ((fm.eraseRooted decl).set (.var decl) pm).WellFormed := by
  intro root path pm' hlookup
  simp only [FlowModel.promotionInfo_set, reduceCtorEq, ↓reduceIte,
    FlowModel.promotionInfo_eraseRooted_property] at hlookup
  split at hlookup
  · simp at hlookup
  case isFalse hne =>
    obtain ⟨pmv, hpmv, hwcv⟩ := hwf root path pm' hlookup
    exact ⟨pmv, by simp [Ne.symm hne, hpmv], hwcv⟩

omit [DecidableEq ℓ] in
/--
Well-formedness is preserved by `join`: if `fm₁` and `fm₂` are well formed (`hwf₁`, `hwf₂`), so is
`fm₁.join fm₂`. A property target survives the join only if both flow models have it, so both track
its root, and so does the join.
-/
public theorem FlowModel.WellFormed.join {fm₁ fm₂ : FlowModel} (hwf₁ : fm₁.WellFormed)
    (hwf₂ : fm₂.WellFormed) : (fm₁.join fm₂).WellFormed := by
  intro root path pm hlookup
  simp only [FlowModel.promotionInfo_join, Option.bind_eq_some_iff, Option.map_eq_some_iff]
    at hlookup
  obtain ⟨pm₁, hlookup₁, pm₂, hlookup₂, -⟩ := hlookup
  obtain ⟨pmv₁, hpmv₁, hwc₁⟩ := hwf₁ root path pm₁ hlookup₁
  obtain ⟨pmv₂, hpmv₂, hwc₂⟩ := hwf₂ root path pm₂ hlookup₂
  exact ⟨pmv₁.join pmv₂, by simp [FlowModel.promotionInfo_join, hpmv₁, hpmv₂],
    by simp [hwc₁, hwc₂]⟩


/--
What flow analysis learns from analyzing an expression: its static type, the location it read (if
any), and the flow models after it for when it evaluates to `true` and to `false`. (For an
expression that isn't a condition, the two flow models are the same.) Mirrors the
specification's `true(E)` and `false(E)`, along with the expression's static type.
-/
public structure ExprModel where
  /-- The expression's static type. -/
  type : τ
  /-- The location the expression read, if it read one that flow analysis can promote. -/
  ref? : Option Reference
  /-- The flow model after the expression, if it evaluates to `true`. -/
  fm_true : FlowModel
  /-- The flow model after the expression, if it evaluates to `false`. -/
  fm_false : FlowModel

local notation "ExprModel" => ExprModel (τ := τ) (ℓ := ℓ)

/--
The flow model after the expression, whatever it evaluates to: the join of the flow models for
`true` and `false`. Mirrors the specification's `after(E)`.
-/
@[expose]
public def ExprModel.fm_after (em : ExprModel) := em.fm_true.join em.fm_false

omit [DecidableEq ℓ] in
/--
The flow model after an expression model whose flow models are both `fm` (`fm_after`) is `fm`.
-/
@[simp]
public theorem ExprModel.simple_after {ref? : Option Reference} {T : τ}
    {fm : FlowModel} :
    (ExprModel.mk T ref? fm fm).fm_after = fm := by
  simp [ExprModel.fm_after]

end FlowAnalysis
