module
public import FlowAnalysis.PromotionChain.Basic
public import FlowAnalysis.PromotionChain.JoinImpl
public import FlowAnalysis.ValueVersion.Basic
public import FlowAnalysis.PromotionModel.JoinTestedImpl
public import FlowAnalysis.Types

namespace FlowAnalysis

open PromotionChain

variable {τ : Type} [Γ : DartTypeRepr τ] {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "ValueVersion" => ValueVersion (ℓ := ℓ)

/-- The state of a promotable value at a particular point in a function's execution. -/
@[ext]
public structure PromotionModel where
  promotedTypes : PromotionChain
  tested : Finset τ
  assigned : Bool
  unassigned : Bool
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
holding the value `version`.

This is a smart constructor rather than a literal because the invariants on `PromotionModel` are
carried as proof fields, and it is tidier to discharge them once here than at each construction
site.
-/
@[expose]
public def declared (version : ValueVersion) : PromotionModel where
  promotedTypes := ∅
  tested := ∅
  assigned := true
  unassigned := false
  version? := some version
  writeCaptured := false
  writeCaptured_promotedTypes := by simp
  version?_eq_none_iff := by simp
  not_assigned_and_unassigned := by simp
  not_writeCaptured_and_unassigned := by simp

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
@[simp]
public theorem writeCaptured_tryPromote {pm : PromotionModel} {T : τ} {h : ¬pm.writeCaptured} :
    (pm.tryPromote T h).writeCaptured = pm.writeCaptured := rfl

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

public instance join.instIdempotentOp :
    Std.IdempotentOp (join (τ := τ) (ℓ := ℓ)) where
  idempotent := join_self

/-- The join operation is commutative (`join pm₁ pm₂ = join pm₂ pm₁`). -/
public theorem join_comm (pm₁ pm₂ : PromotionModel) : pm₁.join pm₂ = pm₂.join pm₁ := by
  ext1 <;>
    simp [join, PromotionChain.join_comm, Finset.union_comm, Bool.and_comm, Bool.or_comm,
      ValueVersion.join?_comm]

public instance join.instCommutative : Std.Commutative (join (τ := τ) (ℓ := ℓ)) where
  comm := join_comm

/-- The join operation is associative (`join (join pm₁ pm₂) pm₃ = join pm₁ (join pm₂ pm₃)`). -/
public theorem join_assoc (pm₁ pm₂ pm₃ : PromotionModel) :
    (pm₁.join pm₂).join pm₃ = pm₁.join (pm₂.join pm₃) := by
  ext1 <;>
    simp [join, PromotionChain.join_assoc, Finset.union_assoc, Bool.and_assoc, Bool.or_assoc,
      ValueVersion.join?_assoc]

public instance join.instAssociative : Std.Associative (join (τ := τ) (ℓ := ℓ)) where
  assoc := join_assoc

end «PromotionModel»

open «PromotionModel»

public structure PromotionModelImpl where
  promotedTypes : List τ
  tested : List τ
  assigned : Bool
  unassigned : Bool
  version? : Option ValueVersion

local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ) (ℓ := ℓ)

@[expose]
public def PromotionModelImpl.join (pmI₁ pmI₂ : PromotionModelImpl) : PromotionModelImpl :=
  ⟨(joinPromotedTypesImpl pmI₁.promotedTypes pmI₂.promotedTypes : Id _).run,
    joinTestedImpl pmI₁.tested pmI₂.tested,
    pmI₁.assigned ∧ pmI₂.assigned,
    pmI₁.unassigned ∧ pmI₂.unassigned,
    ValueVersion.join? pmI₁.version? pmI₂.version?
  ⟩

@[expose]
public def PromotionModelImpl.promotedType? (pmI : PromotionModelImpl) : Option τ :=
  pmI.promotedTypes.getLast?

@[expose]
public def PromotionModelImpl.currentType (pmI : PromotionModelImpl) (baseType : τ) :
    τ :=
  match pmI.promotedType? with
  | none => baseType
  | some T => if T ≤ baseType then T else baseType

/--
Whether flow analysis has given up on tracking this value.

Unlike the specification's `PromotionModel.writeCaptured`, this is *derived* rather than stored:
the implementation records write capture by dropping the value version, and reads it back with the
getter `bool get writeCaptured => version == null`.  The specification's invariant
`version?_eq_none_iff` is what makes the two agree.

Note that `join` therefore needs no `writeCaptured` component: `ValueVersion.join?` is `none`
exactly when either operand is, which is the `||` the implementation computes.
-/
@[expose]
public def PromotionModelImpl.writeCaptured (pmI : PromotionModelImpl) : Bool :=
  pmI.version?.isNone

-- Decidable equality of labels is only needed in order to join value versions, so omit it from the
-- refinement definitions and lemmas below; `PromotionModelImpl.refines.join` reintroduces it
-- explicitly.
omit [DecidableEq ℓ]

public structure PromotionModelImpl.refines (pmI : PromotionModelImpl) (pm : PromotionModel) :
    Prop where
  promotedTypes : pmI.promotedTypes = pm.promotedTypes.val
  tested : ∀ T, T ∈ pmI.tested ↔ T ∈ pm.tested
  assigned : pmI.assigned = pm.assigned
  unassigned : pmI.unassigned = pm.unassigned
  version? : pmI.version? = pm.version?

@[simp]
public theorem PromotionModelImpl.refines.promotedTypes' {pmI : PromotionModelImpl}
    {pm : PromotionModel} (h : PromotionModelImpl.refines pmI pm) :
    (pmI.promotedTypes = pm.promotedTypes.val) ↔ True := by
  simp [h.promotedTypes]

@[simp]
public theorem PromotionModelImpl.refines.tested' {pmI : PromotionModelImpl} {pm : PromotionModel}
    (h : PromotionModelImpl.refines pmI pm) : (∀ T, T ∈ pmI.tested ↔ T ∈ pm.tested) ↔ True := by
  simp [h.tested]

@[simp]
public theorem PromotionModelImpl.refines.assigned' {pmI : PromotionModelImpl} {pm : PromotionModel}
    (h : PromotionModelImpl.refines pmI pm) : (pmI.assigned = pm.assigned) ↔ True := by
  simp [h.assigned]

@[simp]
public theorem PromotionModelImpl.refines.unassigned' {pmI : PromotionModelImpl} {pm : PromotionModel}
    (h : PromotionModelImpl.refines pmI pm) : (pmI.unassigned = pm.unassigned) ↔ True := by
  simp [h.unassigned]

@[simp]
public theorem PromotionModelImpl.refines.version?' {pmI : PromotionModelImpl} {pm : PromotionModel}
    (h : PromotionModelImpl.refines pmI pm) : (pmI.version? = pm.version?) ↔ True := by
  simp [h.version?]

/--
The algorithm and the specification agree about write capture.

This is a *consequence* of refinement rather than a clause of it, because the algorithm derives
write capture from the absence of a value version, and the specification's `version?_eq_none_iff`
invariant says its stored flag agrees with the same test.
-/
public theorem PromotionModelImpl.refines.writeCaptured {pmI : PromotionModelImpl}
    {pm : PromotionModel} (h : PromotionModelImpl.refines pmI pm) :
    pmI.writeCaptured = pm.writeCaptured := by
  have hiff := pm.version?_eq_none_iff
  simp only [PromotionModelImpl.writeCaptured, h.version?]
  cases hv : pm.version? <;> simp_all

/--
The variable model that the algorithm creates for a freshly declared variable refines the variable
model that the specification creates for it.
-/
@[simp]
public theorem PromotionModelImpl.refines.declared (version : ValueVersion) :
    (⟨[], [], true, false, some version⟩ : PromotionModelImpl).refines
      (PromotionModel.declared version) := by
  constructor <;> simp [PromotionModel.declared]

public theorem PromotionModelImpl.refines.unique {pmI : PromotionModelImpl}
    {pm₁ pm₂ : PromotionModel} :
    pmI.refines pm₁ → pmI.refines pm₂ → pm₁ = pm₂ := by
  intro h₁ h₂
  ext1
  case promotedTypes => ext1; rw [←h₁.promotedTypes, ←h₂.promotedTypes]
  case tested => ext; rw [←h₁.tested, ←h₂.tested]
  case assigned => rw [←h₁.assigned, ←h₂.assigned]
  case unassigned => rw [←h₁.unassigned, ←h₂.unassigned]
  case version? => rw [←h₁.version?, ←h₂.version?]
  case writeCaptured => rw [←h₁.writeCaptured, ←h₂.writeCaptured]

public theorem PromotionModelImpl.refines.currentTypes {pmI : PromotionModelImpl} {pm : PromotionModel}
    {baseType : τ} : pmI.refines pm → pmI.currentType baseType = pm.currentType baseType := by
  intro hrefines
  simp [PromotionModelImpl.currentType, PromotionModelImpl.promotedType?, PromotionModel.currentType]
  rw [hrefines.promotedTypes]

/--
Refinement implies that `pmI` and `pm` agree about whether a promotion to `T` is possible: appending
`T` to `pmI`'s list of promoted types produces a valid promotion chain iff `pm`'s promotion chain
strictly bounds `T`.
-/
public theorem PromotionModelImpl.refines.strictly_bounds_iff {pmI : PromotionModelImpl}
    {pm : PromotionModel} {T : τ} (hrefines : pmI.refines pm) :
    isPromotionChain (pmI.promotedTypes ++ [T]) ↔ pm.promotedTypes.strictly_bounds T := by
  rw [PromotionChain.strictly_bounds, hrefines.promotedTypes]

/--
The algorithm promotes a variable to `T` by appending `T` to its list of promoted types, but only
when the resulting list is a valid promotion chain. This theorem shows that doing so refines
`PromotionModel.tryPromote`, which appends `T` under precisely the same circumstances.
-/
public theorem PromotionModelImpl.refines.promote {pmI : PromotionModelImpl} {pm : PromotionModel}
    {T : τ} (hrefines : pmI.refines pm) (hchain : isPromotionChain (pmI.promotedTypes ++ [T]))
    (hwc : ¬pm.writeCaptured) :
    {pmI with promotedTypes := pmI.promotedTypes ++ [T]}.refines (pm.tryPromote T hwc) := by
  have hbounds : pm.promotedTypes.strictly_bounds T := hrefines.strictly_bounds_iff.mp hchain
  constructor <;> simp_all [PromotionModel.tryPromote]

/--
Conversely, in the circumstances in which the algorithm declines to promote a variable to `T` (that
is, when appending `T` to its list of promoted types wouldn't produce a valid promotion chain),
`PromotionModel.tryPromote` is a no-op.
-/
public theorem PromotionModelImpl.refines.tryPromote_eq_self {pmI : PromotionModelImpl}
    {pm : PromotionModel} {T : τ} (hrefines : pmI.refines pm)
    (hchain : ¬isPromotionChain (pmI.promotedTypes ++ [T])) {hwc : ¬pm.writeCaptured} :
    pm.tryPromote T hwc = pm := by
  have hbounds : ¬pm.promotedTypes.strictly_bounds T := hrefines.strictly_bounds_iff.not.mp hchain
  ext1 <;> simp [PromotionModel.tryPromote, hbounds]

public theorem PromotionModelImpl.refines.join [DecidableEq ℓ] {pmI₁ pmI₂ : PromotionModelImpl}
    {pm₁ pm₂ : PromotionModel} :
    pmI₁.refines pm₁ → pmI₂.refines pm₂ → (pmI₁.join pmI₂).refines (pm₁.join pm₂) := by
  rintro hrefines₁ hrefines₂
  simp [PromotionModelImpl.join, PromotionModel.join]
  constructor
  case promotedTypes =>
    simp [hrefines₁.promotedTypes, hrefines₂.promotedTypes]
    rw [joinPromotedTypesImpl_pure_correct pm₁.promotedTypes pm₂.promotedTypes]
  case tested =>
    intro T; simp [joinTestedImpl, List.mem_union_iff, hrefines₁.tested, hrefines₂.tested]
  case assigned => simp [hrefines₁.assigned, hrefines₂.assigned]
  case unassigned => simp [hrefines₁.unassigned, hrefines₂.unassigned]
  case version? => simp [hrefines₁.version?, hrefines₂.version?]

end FlowAnalysis
