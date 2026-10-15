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

It defines the operations on flow models that the elaboration rules need (`set`, `join`, `infoFor`,
`currentTypeOf`), and the well-formedness condition that elaboration preserves
(`FlowModel.WellFormed`). It also defines `ExprModel`, which packages what flow analysis learns from
analyzing an expression.
-/

namespace FlowAnalysis
open DartLang

variable {τ : Type} [DartTypeRepr τ] {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := ℓ)
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
`r.key` if there is one, and otherwise a fresh promotion model holding the version that was read.
Mirrors Dart's `FlowModel.infoFor`.

The result is `none` only if there is no stored model and `r` has no version, which happens only for
a write-captured variable (see `Reference.version?`). In Dart, such a reference has a fresh version,
so `infoFor` always returns a model.
-/
@[expose]
public def FlowModel.infoFor (fm : FlowModel) (r : Reference) : Option PromotionModel :=
  match fm.promotionInfo r.key with
  | some pm => some pm
  | none => r.version?.map PromotionModel.fresh

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

/--
The version stored at a property key is determined by the key itself.

This holds because the implementation allocates a promotion key for a property together with the
value version it describes, and never stores a different version under that key: a write to a
property, or a join that reaches it from two different targets, produces a *different* key rather
than a new version under the old one.

It is stated here, as a condition on the key-to-model map, rather than as an invariant of
`PromotionModel`, because it relates a key to its model rather than constraining a model on its own.

Elaboration preserves it: see `ElabStmt.wellFormed`.
-/
@[expose]
public def FlowModel.WellFormed (fm : FlowModel) : Prop :=
  ∀ r p pm, fm.promotionInfo (.loc r p) = some pm → pm.version? = some r

omit [DecidableEq ℓ] in
/-- The initial flow model is well formed, since it holds nothing at all. -/
public theorem FlowModel.WellFormed.empty : (FlowModel.empty (τ := τ) (ℓ := ℓ)).WellFormed := by
  intro _ _ _ hlookup
  simp [FlowModel.empty] at hlookup

/--
Well-formedness is preserved by `set` (`(fm.set k pm).WellFormed`, given `hwf`), provided the model
`pm` being stored carries the version named by the key `k` it is being stored at (`hkey`).
-/
public theorem FlowModel.WellFormed.set {fm : FlowModel} (hwf : fm.WellFormed) {k : Key}
    {pm : PromotionModel} (hkey : ∀ r p, k = .loc r p → pm.version? = some r) :
    (fm.set k pm).WellFormed := by
  intro r p pm' hlookup
  simp only [FlowModel.promotionInfo_set] at hlookup
  split at hlookup
  case isTrue heq => cases hlookup; exact hkey r p heq
  case isFalse => exact hwf r p pm' hlookup

/--
Well-formedness is preserved by `join`: if `fm₁` and `fm₂` are well formed (`hwf₁`, `hwf₂`), so is
`fm₁.join fm₂`.

The joined model's version is the join of the two incoming versions, and both of those are the
version named by the key, so the join is too — this is `ValueVersion.join?_self`, and it is the
first place where the idempotence of `join` does real work.
-/
public theorem FlowModel.WellFormed.join {fm₁ fm₂ : FlowModel} (hwf₁ : fm₁.WellFormed)
    (hwf₂ : fm₂.WellFormed) : (fm₁.join fm₂).WellFormed := by
  intro r p pm hlookup
  simp only [FlowModel.join] at hlookup
  split at hlookup
  case h_1 => simp at hlookup
  case h_2 pm₁ hlookup₁ =>
    split at hlookup
    case h_1 => simp at hlookup
    case h_2 pm₂ hlookup₂ =>
      cases hlookup
      simp [PromotionModel.join, hwf₁ r p pm₁ hlookup₁, hwf₂ r p pm₂ hlookup₂]

omit [DecidableEq ℓ] in
/--
In a well-formed flow model (`hwf`), the promotion model `pm` that `infoFor` supplies for a
reference `r` (`h`) carries the version named by the reference's key: if the key is a property
key with root version `v` (`hkey`), `pm`'s version is `v` (`pm.version? = some v`).

A stored model does so because the flow model is well formed, and a fresh model does so because
every reference does (`Reference.version?_of_key_loc`). This is the hypothesis
`FlowModel.WellFormed.set` needs in order to store the model back, after promoting it.
-/
public theorem FlowModel.WellFormed.infoFor {fm : FlowModel} (hwf : fm.WellFormed) {r : Reference}
    {pm : PromotionModel} (h : fm.infoFor r = some pm) (v : ValueVersion (ℓ := ℓ))
    (q : List String) (hkey : r.key = .loc v q) : pm.version? = some v := by
  simp only [FlowModel.infoFor] at h
  split at h
  case h_1 pm' hlookup =>
    cases h
    rw [hkey] at hlookup
    exact hwf v q _ hlookup
  case h_2 =>
    obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp h
    have := Reference.version?_of_key_loc hkey
    simp_all [PromotionModel.fresh]

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

/--
The flow model after an expression model whose flow models are both `fm` (`fm_after`) is `fm`.
-/
@[simp]
public theorem ExprModel.simple_after {ref? : Option Reference} {T : τ}
    {fm : FlowModel} :
    (ExprModel.mk T ref? fm fm).fm_after = fm := by
  simp [ExprModel.fm_after]

/-! ### Reading variables -/

/--
Whether the variable `v` starts out holding the null object when it's declared with no initializer:
it isn't `final`, and its type is nullable. (This follows the null-safety feature's rules for
non-`late` local variables.)
-/
@[expose]
public def _root_.DartLang.Variable.startsNull (v : Variable (τ := τ)) : Bool :=
  !v.isFinal && decide (DartTypeRepr.Null ≤ v.type)

/--
The variable `v` starts out holding the null object (`v.startsNull = true`) exactly when it isn't
`final` and its type is nullable (`v.isFinal = false ∧ DartTypeRepr.Null ≤ v.type`).
-/
@[simp]
public theorem _root_.DartLang.Variable.startsNull_eq_true {v : Variable (τ := τ)} :
    v.startsNull = true ↔ v.isFinal = false ∧ DartTypeRepr.Null ≤ v.type := by
  simp [Variable.startsNull]

/--
Whether the variable `v`, whose promotion model is `pm`, is *readable*: it's definitely assigned,
or it starts out holding the null object (`Variable.startsNull`). Reading a variable that isn't
readable is a compile-time error. (This is the null-safety feature's definite assignment rule,
rather than part of the flow analysis specification: "It is a compile time error to read a local
variable when the variable is potentially unassigned unless the variable is non-`final` and has
nullable type, or is `late`.")
-/
@[expose, reducible]
public def PromotionModel.Readable (pm : PromotionModel) (v : Variable (τ := τ)) : Prop :=
  pm.assigned = true ∨ v.startsNull = true

end FlowAnalysis
