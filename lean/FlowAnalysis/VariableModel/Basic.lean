module
public import FlowAnalysis.PromotionChain.Basic
public import FlowAnalysis.PromotionChain.JoinImpl
public import FlowAnalysis.SsaNode.Basic
public import FlowAnalysis.VariableModel.JoinTestedImpl
public import FlowAnalysis.Types

namespace FlowAnalysis

open PromotionChain

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "PromotionChain" => PromotionChain (τ := τ)

/-- The state of a promotable value at a particular point in a function's execution. -/
@[ext]
public structure VariableModel where
  promotedTypes : PromotionChain
  tested : Finset τ
  assigned : Bool
  unassigned : Bool
  ssaNode? : Option SsaNode

local notation "VariableModel" => VariableModel (τ := τ)

namespace «VariableModel»

@[expose]
public def currentType (vm : VariableModel) (baseType : τ) :=
  match vm.promotedTypes.val.getLast? with
  | none => baseType
  | some T => if T ≤ baseType then T else baseType

@[expose]
public def join (vm₁ vm₂ : VariableModel) :
    VariableModel :=
  ⟨vm₁.promotedTypes.join vm₂.promotedTypes,
    vm₁.tested ∪ vm₂.tested,
    vm₁.assigned ∧ vm₂.assigned,
    vm₁.unassigned ∧ vm₂.unassigned,
    SsaNode.join vm₁.ssaNode? vm₂.ssaNode?⟩

/-- The join operation is idempotent (`join vm vm = vm`). -/
@[simp]
public theorem join_self (vm : VariableModel) : vm.join vm = vm := by
  rcases vm; simp [join]

public instance join.instIdempotentOp :
    Std.IdempotentOp (join (τ := τ)) where
  idempotent := join_self

/-- The join operation is commutative (`join vm₁ vm₂ = join vm₂ vm₁`). -/
public theorem join_comm (vm₁ vm₂ : VariableModel) : vm₁.join vm₂ = vm₂.join vm₁ := by
  simp [join, PromotionChain.join_comm, Finset.union_comm, Bool.and_comm, SsaNode.join_comm]

public instance join.instCommutative : Std.Commutative (join (τ := τ)) where
  comm := join_comm

/-- The join operation is associative (`join (join vm₁ vm₂) vm₃ = join vm₁ (join vm₂ vm₃)`). -/
public theorem join_assoc (vm₁ vm₂ vm₃ : VariableModel) :
    (vm₁.join vm₂).join vm₃ = vm₁.join (vm₂.join vm₃) := by
  simp [join, PromotionChain.join_assoc, Finset.union_assoc, Bool.and_assoc, SsaNode.join_assoc]

public instance join.instAssociative : Std.Associative (join (τ := τ)) where
  assoc := join_assoc

end «VariableModel»

open «VariableModel»

public structure VariableModelImpl where
  promotedTypes : List τ
  tested : List τ
  assigned : Bool
  unassigned : Bool
  ssaNode? : Option SsaNode

local notation "VariableModelImpl" => VariableModelImpl (τ := τ)

@[expose]
public def VariableModelImpl.join (vmI₁ vmI₂ : VariableModelImpl) : VariableModelImpl :=
  ⟨(joinPromotedTypesImpl vmI₁.promotedTypes vmI₂.promotedTypes : Id _).run,
    joinTestedImpl vmI₁.tested vmI₂.tested,
    vmI₁.assigned ∧ vmI₂.assigned,
    vmI₁.unassigned ∧ vmI₂.unassigned,
    SsaNode.join vmI₁.ssaNode? vmI₂.ssaNode?
  ⟩

@[expose]
public def VariableModelImpl.promotedType? (vmI : VariableModelImpl) : Option τ :=
  vmI.promotedTypes.getLast?

@[expose]
public def VariableModelImpl.currentType (vmI : VariableModelImpl) (baseType : τ) :
    τ :=
  match vmI.promotedType? with
  | none => baseType
  | some T => if T ≤ baseType then T else baseType

public structure VariableModelImpl.refines (vmI : VariableModelImpl) (vm : VariableModel) :
    Prop where
  promotedTypes : vmI.promotedTypes = vm.promotedTypes.val
  tested : ∀ T, T ∈ vmI.tested ↔ T ∈ vm.tested
  assigned : vmI.assigned = vm.assigned
  unassigned : vmI.unassigned = vm.unassigned
  ssaNode? : vmI.ssaNode? = vm.ssaNode?

@[simp]
public theorem VariableModelImpl.refines.promotedTypes' {vmI : VariableModelImpl}
    {vm : VariableModel} (h : VariableModelImpl.refines vmI vm) :
    (vmI.promotedTypes = vm.promotedTypes.val) ↔ True := by
  simp [h.promotedTypes]

@[simp]
public theorem VariableModelImpl.refines.tested' {vmI : VariableModelImpl} {vm : VariableModel}
    (h : VariableModelImpl.refines vmI vm) : (∀ T, T ∈ vmI.tested ↔ T ∈ vm.tested) ↔ True := by
  simp [h.tested]

@[simp]
public theorem VariableModelImpl.refines.assigned' {vmI : VariableModelImpl} {vm : VariableModel}
    (h : VariableModelImpl.refines vmI vm) : (vmI.assigned = vm.assigned) ↔ True := by
  simp [h.assigned]

@[simp]
public theorem VariableModelImpl.refines.unassigned' {vmI : VariableModelImpl} {vm : VariableModel}
    (h : VariableModelImpl.refines vmI vm) : (vmI.unassigned = vm.unassigned) ↔ True := by
  simp [h.unassigned]

@[simp]
public theorem VariableModelImpl.refines.ssaNode?' {vmI : VariableModelImpl} {vm : VariableModel}
    (h : VariableModelImpl.refines vmI vm) : (vmI.ssaNode? = vm.ssaNode?) ↔ True := by
  simp [h.ssaNode?]

/--
The variable model that the algorithm creates for a freshly declared variable refines the variable
model that the specification creates for it.
-/
@[simp]
public theorem VariableModelImpl.refines.declared :
    (⟨[], [], true, false, some ⟨⟩⟩ : VariableModelImpl).refines
      ⟨∅, ∅, true, false, some ⟨⟩⟩ := by
  constructor <;> simp

public theorem VariableModelImpl.refines.unique {vmI : VariableModelImpl}
    {vm₁ vm₂ : VariableModel} :
    vmI.refines vm₁ → vmI.refines vm₂ → vm₁ = vm₂ := by
  intro h₁ h₂
  ext1
  case promotedTypes => ext1; rw [←h₁.promotedTypes, ←h₂.promotedTypes]
  case tested => ext; rw [←h₁.tested, ←h₂.tested]
  case assigned => rw [←h₁.assigned, ←h₂.assigned]
  case unassigned => rw [←h₁.unassigned, ←h₂.unassigned]
  case ssaNode? => rw [←h₁.ssaNode?, ←h₂.ssaNode?]

public theorem VariableModelImpl.refines.currentTypes {vmI : VariableModelImpl} {vm : VariableModel}
    {baseType : τ} : vmI.refines vm → vmI.currentType baseType = vm.currentType baseType := by
  intro hrefines
  simp [VariableModelImpl.currentType, VariableModelImpl.promotedType?, VariableModel.currentType]
  rw [hrefines.promotedTypes]

/--
Refinement implies that `vmI` and `vm` agree about whether a promotion to `T` is possible: appending
`T` to `vmI`'s list of promoted types produces a valid promotion chain iff `vm`'s promotion chain
strictly bounds `T`.
-/
public theorem VariableModelImpl.refines.strictly_bounds_iff {vmI : VariableModelImpl}
    {vm : VariableModel} {T : τ} (hrefines : vmI.refines vm) :
    isPromotionChain (vmI.promotedTypes ++ [T]) ↔ vm.promotedTypes.strictly_bounds T := by
  rw [PromotionChain.strictly_bounds, hrefines.promotedTypes]

/--
The algorithm promotes a variable to `T` by appending `T` to its list of promoted types, but only
when the resulting list is a valid promotion chain. This theorem shows that doing so refines
`PromotionChain.tryPromote`, which appends `T` under precisely the same circumstances.
-/
public theorem VariableModelImpl.refines.promote {vmI : VariableModelImpl} {vm : VariableModel}
    {T : τ} (hrefines : vmI.refines vm) (hchain : isPromotionChain (vmI.promotedTypes ++ [T])) :
    {vmI with promotedTypes := vmI.promotedTypes ++ [T]}.refines
      {vm with promotedTypes := vm.promotedTypes.tryPromote T} := by
  have hbounds : vm.promotedTypes.strictly_bounds T := hrefines.strictly_bounds_iff.mp hchain
  constructor <;> simp_all

/--
Conversely, in the circumstances in which the algorithm declines to promote a variable to `T` (that
is, when appending `T` to its list of promoted types wouldn't produce a valid promotion chain),
`PromotionChain.tryPromote` is a no-op.
-/
public theorem VariableModelImpl.refines.tryPromote_eq_self {vmI : VariableModelImpl}
    {vm : VariableModel} {T : τ} (hrefines : vmI.refines vm)
    (hchain : ¬isPromotionChain (vmI.promotedTypes ++ [T])) :
    vm.promotedTypes.tryPromote T = vm.promotedTypes := by
  have hbounds : ¬vm.promotedTypes.strictly_bounds T := hrefines.strictly_bounds_iff.not.mp hchain
  simp [hbounds]

public theorem VariableModelImpl.refines.join {vmI₁ vmI₂ : VariableModelImpl}
    {vm₁ vm₂ : VariableModel} :
    vmI₁.refines vm₁ → vmI₂.refines vm₂ → (vmI₁.join vmI₂).refines (vm₁.join vm₂) := by
  rintro hrefines₁ hrefines₂
  simp [VariableModelImpl.join, VariableModel.join]
  constructor
  case promotedTypes =>
    simp [hrefines₁.promotedTypes, hrefines₂.promotedTypes]
    rw [joinPromotedTypesImpl_pure_correct vm₁.promotedTypes vm₂.promotedTypes]
  case tested =>
    intro T; simp [joinTestedImpl, List.mem_union_iff, hrefines₁.tested, hrefines₂.tested]
  case assigned => simp [hrefines₁.assigned, hrefines₂.assigned]
  case unassigned => simp [hrefines₁.unassigned, hrefines₂.unassigned]
  case ssaNode? => simp [hrefines₁.ssaNode?, hrefines₂.ssaNode?]

end FlowAnalysis
