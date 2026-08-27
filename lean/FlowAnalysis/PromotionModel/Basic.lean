module
public import FlowAnalysis.PromotionChain.Basic
public import FlowAnalysis.PromotionChain.JoinImpl
public import FlowAnalysis.ValueVersion.Basic
public import FlowAnalysis.PromotionModel.JoinTestedImpl
public import FlowAnalysis.Types

namespace FlowAnalysis

open PromotionChain

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "PromotionChain" => PromotionChain (τ := τ)

/-- The state of a promotable value at a particular point in a function's execution. -/
@[ext]
public structure PromotionModel where
  promotedTypes : PromotionChain
  tested : Finset τ
  assigned : Bool
  unassigned : Bool
  version? : Option ValueVersion

local notation "PromotionModel" => PromotionModel (τ := τ)

namespace «PromotionModel»

@[expose]
public def currentType (pm : PromotionModel) (baseType : τ) :=
  match pm.promotedTypes.val.getLast? with
  | none => baseType
  | some T => if T ≤ baseType then T else baseType

@[expose]
public def join (pm₁ pm₂ : PromotionModel) :
    PromotionModel :=
  ⟨pm₁.promotedTypes.join pm₂.promotedTypes,
    pm₁.tested ∪ pm₂.tested,
    pm₁.assigned ∧ pm₂.assigned,
    pm₁.unassigned ∧ pm₂.unassigned,
    ValueVersion.join pm₁.version? pm₂.version?⟩

/-- The join operation is idempotent (`join pm pm = pm`). -/
@[simp]
public theorem join_self (pm : PromotionModel) : pm.join pm = pm := by
  rcases pm; simp [join]

public instance join.instIdempotentOp :
    Std.IdempotentOp (join (τ := τ)) where
  idempotent := join_self

/-- The join operation is commutative (`join pm₁ pm₂ = join pm₂ pm₁`). -/
public theorem join_comm (pm₁ pm₂ : PromotionModel) : pm₁.join pm₂ = pm₂.join pm₁ := by
  simp [join, PromotionChain.join_comm, Finset.union_comm, Bool.and_comm, ValueVersion.join_comm]

public instance join.instCommutative : Std.Commutative (join (τ := τ)) where
  comm := join_comm

/-- The join operation is associative (`join (join pm₁ pm₂) pm₃ = join pm₁ (join pm₂ pm₃)`). -/
public theorem join_assoc (pm₁ pm₂ pm₃ : PromotionModel) :
    (pm₁.join pm₂).join pm₃ = pm₁.join (pm₂.join pm₃) := by
  simp [join, PromotionChain.join_assoc, Finset.union_assoc, Bool.and_assoc, ValueVersion.join_assoc]

public instance join.instAssociative : Std.Associative (join (τ := τ)) where
  assoc := join_assoc

end «PromotionModel»

open «PromotionModel»

public structure PromotionModelImpl where
  promotedTypes : List τ
  tested : List τ
  assigned : Bool
  unassigned : Bool
  version? : Option ValueVersion

local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ)

@[expose]
public def PromotionModelImpl.join (pmI₁ pmI₂ : PromotionModelImpl) : PromotionModelImpl :=
  ⟨(joinPromotedTypesImpl pmI₁.promotedTypes pmI₂.promotedTypes : Id _).run,
    joinTestedImpl pmI₁.tested pmI₂.tested,
    pmI₁.assigned ∧ pmI₂.assigned,
    pmI₁.unassigned ∧ pmI₂.unassigned,
    ValueVersion.join pmI₁.version? pmI₂.version?
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
The promotion model that the algorithm creates for a freshly declared variable refines the
promotion model that the specification creates for it.
-/
@[simp]
public theorem PromotionModelImpl.refines.declared :
    (⟨[], [], true, false, some ⟨⟩⟩ : PromotionModelImpl).refines
      ⟨∅, ∅, true, false, some ⟨⟩⟩ := by
  constructor <;> simp

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
`PromotionChain.tryPromote`, which appends `T` under precisely the same circumstances.
-/
public theorem PromotionModelImpl.refines.promote {pmI : PromotionModelImpl} {pm : PromotionModel}
    {T : τ} (hrefines : pmI.refines pm) (hchain : isPromotionChain (pmI.promotedTypes ++ [T])) :
    {pmI with promotedTypes := pmI.promotedTypes ++ [T]}.refines
      {pm with promotedTypes := pm.promotedTypes.tryPromote T} := by
  have hbounds : pm.promotedTypes.strictly_bounds T := hrefines.strictly_bounds_iff.mp hchain
  constructor <;> simp_all

/--
Conversely, in the circumstances in which the algorithm declines to promote a variable to `T` (that
is, when appending `T` to its list of promoted types wouldn't produce a valid promotion chain),
`PromotionChain.tryPromote` is a no-op.
-/
public theorem PromotionModelImpl.refines.tryPromote_eq_self {pmI : PromotionModelImpl}
    {pm : PromotionModel} {T : τ} (hrefines : pmI.refines pm)
    (hchain : ¬isPromotionChain (pmI.promotedTypes ++ [T])) :
    pm.promotedTypes.tryPromote T = pm.promotedTypes := by
  have hbounds : ¬pm.promotedTypes.strictly_bounds T := hrefines.strictly_bounds_iff.not.mp hchain
  simp [hbounds]

public theorem PromotionModelImpl.refines.join {pmI₁ pmI₂ : PromotionModelImpl}
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
