module
public import FlowAnalysis.Elements
public import FlowAnalysis.Key.Basic
public import FlowAnalysis.PromotionChain.Basic
public import FlowAnalysis.Types
public import FlowAnalysis.PromotionModel.Basic

namespace FlowAnalysis

variable {τ : Type} [DartTypeRepr τ] {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := ℓ)
local notation "Key" => Key (τ := τ) (ℓ := ℓ)
local notation "Reference" => Reference (τ := τ) (ℓ := ℓ)

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

@[simp]
public theorem FlowModel.promotionInfo_set {fm : FlowModel} {k k' T} :
    (fm.set k T).promotionInfo k' = if k = k' then some T else fm.promotionInfo k' := by
  simp_all [FlowModel.set]

public theorem FlowModel.set_get?_neq {fm : FlowModel} {k k' : Key}
    {pm : PromotionModel} :
    k ≠ k' → (fm.set k pm).promotionInfo k' = fm.promotionInfo k' := by
  intro hNeq
  simp [hNeq]

@[simp]
public theorem FlowModel.get?_set {fm : FlowModel} {k k' T} :
    (fm.set k T).promotionInfo k' = if k = k' then some T else fm.promotionInfo k' := by
  simp_all [FlowModel.set]

-- Decidable equality of labels is only needed in order to compare or join keys, so omit it from
-- this lemma.
omit [DecidableEq ℓ] in
public theorem FlowModel.extensionality {fm fm' : FlowModel} :
    (∀ k : Key, fm.promotionInfo k = fm'.promotionInfo k) → fm = fm' := by
  rcases fm; rename_i promotionInfo
  rcases fm'; rename_i promotionInfo'
  simp
  apply funext

/--
Setting a key to the promotion model it already has leaves the flow model unchanged.

This is useful for reasoning about elaboration rules that unconditionally update `promotionInfo`, in cases
where the updated value turns out to be the value that was already there.
-/
@[simp]
public theorem FlowModel.set_self {fm : FlowModel} {k : Key}
    {pm : PromotionModel} (hlookup : fm.promotionInfo k = some pm) : fm.set k pm = fm := by
  apply extensionality; intro k'
  simp only [promotionInfo_set]
  split <;> simp_all

@[simp]
public theorem FlowModel.join_idempotent (fm : FlowModel) :
    fm.join fm = fm := by
  apply extensionality; intro k
  simp [FlowModel.join]
  cases fm.promotionInfo k <;> simp_all

instance FlowModel.instIdempotentOpJoin :
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
Well-formedness is preserved by `set`, provided the model being stored carries the version named by
the key it is being stored at.
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
Well-formedness is preserved by `join`.

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
In a well-formed flow model, the promotion model that `infoFor` supplies for a reference carries the
version named by the reference's key.

A stored model does so because the flow model is well formed, and a fresh model does so because
every reference does (`Reference.version?_of_key_loc`). This is the hypothesis
`FlowModel.WellFormed.set` needs in order to store the model back, after promoting it.
-/
public theorem FlowModel.WellFormed.infoFor {fm : FlowModel} (hwf : fm.WellFormed) {r : Reference}
    {pm : PromotionModel} (h : fm.infoFor r = some pm) :
    ∀ v q, r.key = .loc v q → pm.version? = some v := by
  intro v q hkey
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

public structure ExprModel where
  type : τ
  /-- The location the expression read, if it read one that flow analysis can promote. -/
  ref? : Option Reference
  fm_true : FlowModel
  fm_false : FlowModel

local notation "ExprModel" => ExprModel (τ := τ) (ℓ := ℓ)

@[expose]
public def ExprModel.fm_after (em : ExprModel) := em.fm_true.join em.fm_false

@[simp]
public theorem ExprModel.simple_after {ref? : Option Reference} {T : τ}
    {fm : FlowModel} :
    (ExprModel.mk T ref? fm fm).fm_after = fm := by
  simp [ExprModel.fm_after]

end FlowAnalysis
