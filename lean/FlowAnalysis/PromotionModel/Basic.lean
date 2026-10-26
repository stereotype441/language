module
public import FlowAnalysis.PromotionChain.Basic
public import FlowAnalysis.ValueVersion.Basic
public import DartLang.Types

/-!
# Promotion models

This module defines `PromotionModel`, the specification's model of what flow analysis knows about
one promotable location at a particular point in the program: the types it has been promoted to,
the types it has been tested against, whether it's definitely assigned or definitely unassigned,
the value version it holds, and whether flow analysis has given up on tracking it (write capture).
It follows the promotion models of the "Models" section of `flow-analysis.md`, except that the
declared type is stored with the variable rather than in its promotion model, and the value version
is an addition, needed for promoting properties.

The invariants that relate these components (for example, a write-captured location has no
promotions and no value version) are carried as proof fields of the structure, so that every
operation on promotion models must preserve them.

It also defines the operations on promotion models that flow analysis needs: creating one for a
newly declared variable or a newly read property (`declared`, `fresh`), promoting
(`tryPromote`), and joining two control flow paths (`join`), which is idempotent, commutative and
associative.
-/

namespace FlowAnalysis
open DartLang

open PromotionChain

variable {τ : Type} [Γ : DartTypeRepr τ] {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "ValueVersion" => ValueVersion (ℓ := ℓ)

/-- The state of a promotable value at a particular point in a function's execution. -/
@[ext]
public structure PromotionModel where
  /-- The types the value has been promoted to, in the order of promotion (`promotionChain`). -/
  promotedTypes : PromotionChain
  /-- The types the value has been tested against (`tested`), the candidate types of interest. -/
  tested : Finset τ
  /-- Whether the location is definitely assigned (`assigned`). -/
  assigned : Bool
  /-- Whether the location is definitely unassigned (`unassigned`). -/
  unassigned : Bool
  /--
  The value version the location holds, or `none` if flow analysis has given up on tracking it
  (see `writeCaptured`).
  -/
  version? : Option ValueVersion
  /--
  Whether flow analysis has given up on tracking this value, because it may be written by a closure
  or a local function at a point flow analysis can't see.
  -/
  writeCaptured : Bool
  /--
  A write-captured value has no promotions: the write that flow analysis can't see might have
  replaced it with a value of the declared type.
  -/
  writeCaptured_promotedTypes : writeCaptured → promotedTypes = ∅
  /--
  Flow analysis tracks a value version precisely when it hasn't given up on the location.  Write
  capture is the only reason it gives up, so the two conditions coincide.
  -/
  version?_eq_none_iff : version? = none ↔ writeCaptured
  /-- A location can't be both definitely assigned and definitely unassigned. -/
  not_assigned_and_unassigned : ¬(assigned ∧ unassigned)
  /--
  A write-captured location isn't definitely unassigned: write capture means an unseen write might
  have happened.
  -/
  not_writeCaptured_and_unassigned : ¬(writeCaptured ∧ unassigned)

local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := ℓ)

namespace «PromotionModel»

/--
The promotion model of a freshly declared variable: unpromoted, untested, not write captured, and
holding the value `version`. It is definitely assigned if the declaration initializes the variable
(`initialized`), and definitely unassigned otherwise.

This is a smart constructor rather than a literal because the invariants on `PromotionModel` are
carried as proof fields, and it is tidier to discharge them once here than at each construction
site.
-/
@[expose]
public def declared (initialized : Bool) (version : ValueVersion) : PromotionModel where
  promotedTypes := ∅
  tested := ∅
  assigned := initialized
  unassigned := !initialized
  version? := some version
  writeCaptured := false
  writeCaptured_promotedTypes := by simp
  version?_eq_none_iff := by simp
  not_assigned_and_unassigned := by cases initialized <;> simp
  not_writeCaptured_and_unassigned := by simp

/--
Mirrors Dart's `PromotionModel.fresh(version: version)`: the promotion model that
`FlowModel.infoFor` supplies for a reference that has no promotion model yet. It is unpromoted,
untested, not write captured, and holds the value `version`.

As in Dart, where `assigned` defaults to `false` and `unassigned` is `!assigned`, it is definitely
unassigned. Nothing modelled so far consults definite assignment for properties.
-/
@[expose]
public def fresh (version : ValueVersion) : PromotionModel where
  promotedTypes := ∅
  tested := ∅
  assigned := false
  unassigned := true
  version? := some version
  writeCaptured := false
  writeCaptured_promotedTypes := by simp
  version?_eq_none_iff := by simp
  not_assigned_and_unassigned := by simp
  not_writeCaptured_and_unassigned := by simp

/--
`pm.currentType baseType` is the type of a read of the location whose promotion model is `pm`,
given that its declared type is `baseType`: its most recent promotion, if any, and otherwise
`baseType`. (A promoted type that isn't a subtype of `baseType` is ignored too; flow analysis never
makes such a promotion.)
-/
@[expose]
public def currentType (pm : PromotionModel) (baseType : τ) :=
  match pm.promotedTypes.val.getLast? with
  | none => baseType
  | some T => if T ≤ baseType then T else baseType

/--
`pm.tryPromote T h` promotes to `T`, if doing so yields a valid promotion chain, and is the identity
otherwise.

The hypothesis `h` is what re-establishes `writeCaptured_promotedTypes`: a write-captured value has
no promotions, so it can't acquire one.  Flow analysis never tries to promote a write-captured
location, so every caller has `h` to hand.
-/
@[expose]
public def tryPromote (pm : PromotionModel) (T : τ) (h : ¬pm.writeCaptured) : PromotionModel :=
  { pm with
    promotedTypes := pm.promotedTypes.tryPromote T
    writeCaptured_promotedTypes := fun hwc => absurd hwc h }

omit [DecidableEq ℓ] in
/-- Promoting doesn't change whether a variable is write-captured. -/
@[simp]
public theorem writeCaptured_tryPromote {pm : PromotionModel} {T : τ} {h : ¬pm.writeCaptured} :
    (pm.tryPromote T h).writeCaptured = pm.writeCaptured := rfl

/--
`pm₁.join pm₂` is the promotion model at a point where two control flow paths, on which the
location's promotion models are `pm₁` and `pm₂`, come together. Mirrors the specification's
`joinPM(PM1, PM2)`: it keeps the promotions common to both paths, the union of the tested types,
and definite (un)assignment only if both paths agree; the location is write-captured if it is on
either path, and its value version is the join of the two.
-/
@[expose]
public def join (pm₁ pm₂ : PromotionModel) : PromotionModel where
  promotedTypes := pm₁.promotedTypes.join pm₂.promotedTypes
  tested := pm₁.tested ∪ pm₂.tested
  assigned := pm₁.assigned ∧ pm₂.assigned
  unassigned := pm₁.unassigned ∧ pm₂.unassigned
  version? := ValueVersion.join? pm₁.version? pm₂.version?
  writeCaptured := pm₁.writeCaptured ∨ pm₂.writeCaptured
  writeCaptured_promotedTypes := by
    -- The join of two promotion chains is a sublist of each, so if either side has given up all of
    -- its promotions, so does the join.
    intro hwc
    rcases Bool.or_eq_true _ _ |>.mp (by simpa using hwc) with hwc₁ | hwc₂
    · simp [pm₁.writeCaptured_promotedTypes hwc₁]
    · simp [pm₂.writeCaptured_promotedTypes hwc₂]
  version?_eq_none_iff := by
    simp [ValueVersion.join?, Option.map₂_eq_none_iff, pm₁.version?_eq_none_iff,
      pm₂.version?_eq_none_iff]
  not_assigned_and_unassigned := by
    have := pm₁.not_assigned_and_unassigned; simp_all
  not_writeCaptured_and_unassigned := by
    have := pm₁.not_writeCaptured_and_unassigned
    have := pm₂.not_writeCaptured_and_unassigned
    grind

/-- The join operation is idempotent (`join pm pm = pm`). -/
@[simp]
public theorem join_self (pm : PromotionModel) : pm.join pm = pm := by
  ext1 <;> simp [join]

/-- `join` is idempotent, as an instance of the standard library's `Std.IdempotentOp` class. -/
public instance join.instIdempotentOp :
    Std.IdempotentOp (join (τ := τ) (ℓ := ℓ)) where
  idempotent := join_self

/-- The join operation is commutative (`join pm₁ pm₂ = join pm₂ pm₁`). -/
public theorem join_comm (pm₁ pm₂ : PromotionModel) : pm₁.join pm₂ = pm₂.join pm₁ := by
  ext1 <;>
    simp [join, PromotionChain.join_comm, Finset.union_comm, Bool.and_comm, Bool.or_comm,
      ValueVersion.join?_comm]

/-- `join` is commutative, as an instance of the standard library's `Std.Commutative` class. -/
public instance join.instCommutative : Std.Commutative (join (τ := τ) (ℓ := ℓ)) where
  comm := join_comm

/-- The join operation is associative (`join (join pm₁ pm₂) pm₃ = join pm₁ (join pm₂ pm₃)`). -/
public theorem join_assoc (pm₁ pm₂ pm₃ : PromotionModel) :
    (pm₁.join pm₂).join pm₃ = pm₁.join (pm₂.join pm₃) := by
  ext1 <;>
    simp [join, PromotionChain.join_assoc, Finset.union_assoc, Bool.and_assoc, Bool.or_assoc,
      ValueVersion.join?_assoc]

/-- `join` is associative, as an instance of the standard library's `Std.Associative` class. -/
public instance join.instAssociative : Std.Associative (join (τ := τ) (ℓ := ℓ)) where
  assoc := join_assoc

end «PromotionModel»

end FlowAnalysis
