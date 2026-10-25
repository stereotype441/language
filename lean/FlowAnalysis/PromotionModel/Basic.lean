module
public import FlowAnalysis.PromotionChain.Basic
public import DartLang.Types

/-!
# Promotion models

This module defines `PromotionModel`, the specification's model of what flow analysis knows about
one promotable location at a particular point in the program: the types it has been promoted to,
the types it has been tested against, whether it's definitely assigned or definitely unassigned,
and whether flow analysis has given up on tracking it (write capture). It follows the promotion
models of the "Models" section of `flow-analysis.md`, except that the declared type is stored with
the variable rather than in its promotion model.

The invariants that relate these components (for example, a write-captured location has no
promotions) are carried as proof fields of the structure, so that every operation on promotion
models must preserve them.

It also defines the operations on promotion models that flow analysis needs: creating one for a
newly declared variable or a newly read property (`declared`, `fresh`), promoting
(`tryPromote`), recording an assignment (`write`), and joining two control flow paths (`join`),
which is idempotent, commutative and associative.
-/

namespace FlowAnalysis
open DartLang

open PromotionChain

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "PromotionChain" => PromotionChain (τ := τ)

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
  Whether flow analysis has given up on tracking this value, because it may be written by a closure
  or a local function at a point flow analysis can't see.
  -/
  writeCaptured : Bool
  /--
  A write-captured value has no promotions: the write that flow analysis can't see might have
  replaced it with a value of the declared type.
  -/
  writeCaptured_promotedTypes : writeCaptured → promotedTypes = ∅
  /-- A location can't be both definitely assigned and definitely unassigned. -/
  not_assigned_and_unassigned : ¬(assigned ∧ unassigned)
  /--
  A write-captured location isn't definitely unassigned: write capture means an unseen write might
  have happened.
  -/
  not_writeCaptured_and_unassigned : ¬(writeCaptured ∧ unassigned)

local notation "PromotionModel" => PromotionModel (τ := τ)

namespace «PromotionModel»

/--
The promotion model of a freshly declared variable: unpromoted, untested and not write captured.
It is definitely assigned if the declaration initializes the variable (`initialized`), and
definitely unassigned otherwise.

This is a smart constructor rather than a literal because the invariants on `PromotionModel` are
carried as proof fields, and it is tidier to discharge them once here than at each construction
site.
-/
@[expose]
public def declared (initialized : Bool) : PromotionModel where
  promotedTypes := ∅
  tested := ∅
  assigned := initialized
  unassigned := !initialized
  writeCaptured := false
  writeCaptured_promotedTypes := by simp
  not_assigned_and_unassigned := by cases initialized <;> simp
  not_writeCaptured_and_unassigned := by simp

/--
Mirrors Dart's `PromotionModel.fresh`: the promotion model that `FlowModel.infoFor` supplies for a
reference that has no promotion model yet. It is unpromoted, untested and not write captured.

As in Dart, where `assigned` defaults to `false` and `unassigned` is `!assigned`, it is definitely
unassigned. Nothing modelled so far consults definite assignment for properties.
-/
@[expose]
public def fresh : PromotionModel where
  promotedTypes := ∅
  tested := ∅
  assigned := false
  unassigned := true
  writeCaptured := false
  writeCaptured_promotedTypes := by simp
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

/-- Promoting doesn't change whether a variable is write-captured. -/
@[simp]
public theorem writeCaptured_tryPromote {pm : PromotionModel} {T : τ} {h : ¬pm.writeCaptured} :
    (pm.tryPromote T h).writeCaptured = pm.writeCaptured := rfl

/--
The promotion model after a value of static type `writtenType` is assigned. Mirrors the
specification's `assign(x, E, M)` (in the flow analysis specification's "Promotion" section), as far
as the variable's own promotion model is concerned, apart from promotion to a type of interest,
which isn't modeled yet: the promoted types are demoted (`PromotionChain.demote`), and the location
becomes definitely assigned, and not definitely unassigned. (A write-captured location has no
promotions to demote.) Forgetting the property targets rooted at the variable is the flow model's
job (`FlowModel.eraseRooted`).

TODO: promote to a type of interest (the specification's `toi_promote`), once `tested` is tracked.
-/
@[expose]
public def write (pm : PromotionModel) (writtenType : τ) : PromotionModel where
  promotedTypes := pm.promotedTypes.demote writtenType
  tested := pm.tested
  assigned := true
  unassigned := false
  writeCaptured := pm.writeCaptured
  writeCaptured_promotedTypes := by
    intro hwc
    simp [pm.writeCaptured_promotedTypes hwc]
  not_assigned_and_unassigned := by simp
  not_writeCaptured_and_unassigned := by simp

/-- Writing doesn't change whether a variable is write-captured. -/
@[simp]
public theorem writeCaptured_write {pm : PromotionModel} {writtenType : τ} :
    (pm.write writtenType).writeCaptured = pm.writeCaptured := rfl

/--
`pm₁.join pm₂` is the promotion model at a point where two control flow paths, on which the
location's promotion models are `pm₁` and `pm₂`, come together. Mirrors the specification's
`joinPM(PM1, PM2)`: it keeps the promotions common to both paths, the union of the tested types,
and definite (un)assignment only if both paths agree; the location is write-captured if it is on
either path.
-/
@[expose]
public def join (pm₁ pm₂ : PromotionModel) : PromotionModel where
  promotedTypes := pm₁.promotedTypes.join pm₂.promotedTypes
  tested := pm₁.tested ∪ pm₂.tested
  assigned := pm₁.assigned ∧ pm₂.assigned
  unassigned := pm₁.unassigned ∧ pm₂.unassigned
  writeCaptured := pm₁.writeCaptured ∨ pm₂.writeCaptured
  writeCaptured_promotedTypes := by
    -- The join of two promotion chains is a sublist of each, so if either side has given up all of
    -- its promotions, so does the join.
    intro hwc
    rcases Bool.or_eq_true _ _ |>.mp (by simpa using hwc) with hwc₁ | hwc₂
    · simp [pm₁.writeCaptured_promotedTypes hwc₁]
    · simp [pm₂.writeCaptured_promotedTypes hwc₂]
  not_assigned_and_unassigned := by
    have := pm₁.not_assigned_and_unassigned; simp_all
  not_writeCaptured_and_unassigned := by
    have := pm₁.not_writeCaptured_and_unassigned
    have := pm₂.not_writeCaptured_and_unassigned
    grind

/-- A join is write-captured if either of its operands is. -/
@[simp]
public theorem writeCaptured_join {pm₁ pm₂ : PromotionModel} :
    (pm₁.join pm₂).writeCaptured = (pm₁.writeCaptured || pm₂.writeCaptured) := by
  simp [join]

/-- The join operation is idempotent (`join pm pm = pm`). -/
@[simp]
public theorem join_self (pm : PromotionModel) : pm.join pm = pm := by
  ext1 <;> simp [join]

/-- `join` is idempotent, as an instance of the standard library's `Std.IdempotentOp` class. -/
public instance join.instIdempotentOp :
    Std.IdempotentOp (join (τ := τ)) where
  idempotent := join_self

/-- The join operation is commutative (`join pm₁ pm₂ = join pm₂ pm₁`). -/
public theorem join_comm (pm₁ pm₂ : PromotionModel) : pm₁.join pm₂ = pm₂.join pm₁ := by
  ext1 <;>
    simp [join, PromotionChain.join_comm, Finset.union_comm, Bool.and_comm, Bool.or_comm]

/-- `join` is commutative, as an instance of the standard library's `Std.Commutative` class. -/
public instance join.instCommutative : Std.Commutative (join (τ := τ)) where
  comm := join_comm

/-- The join operation is associative (`join (join pm₁ pm₂) pm₃ = join pm₁ (join pm₂ pm₃)`). -/
public theorem join_assoc (pm₁ pm₂ pm₃ : PromotionModel) :
    (pm₁.join pm₂).join pm₃ = pm₁.join (pm₂.join pm₃) := by
  ext1 <;>
    simp [join, PromotionChain.join_assoc, Finset.union_assoc, Bool.and_assoc, Bool.or_assoc]

/-- `join` is associative, as an instance of the standard library's `Std.Associative` class. -/
public instance join.instAssociative : Std.Associative (join (τ := τ)) where
  assoc := join_assoc

end «PromotionModel»

end FlowAnalysis
