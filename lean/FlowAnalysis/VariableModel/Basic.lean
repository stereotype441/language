module
public import FlowAnalysis.PromotionChain.Basic
public import FlowAnalysis.PromotionChain.JoinImpl
public import FlowAnalysis.Types

namespace FlowAnalysis

open PromotionChain

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "PromotionChain" => PromotionChain (τ := τ)

/-- The state of a promotable value at a particular point in a function's execution. -/
@[ext]
public structure VariableModel where
  promotedTypes : PromotionChain

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
  ⟨vm₁.promotedTypes.join vm₂.promotedTypes⟩

end «VariableModel»

public structure VariableModelImpl where
  promotedTypes : List τ

local notation "VariableModelImpl" => VariableModelImpl (τ := τ)

@[expose]
public def VariableModelImpl.join (vmI₁ vmI₂ : VariableModelImpl) : VariableModelImpl :=
  ⟨(joinPromotedTypesImpl vmI₁.promotedTypes vmI₂.promotedTypes : Id _).run⟩

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
  types : vmI.promotedTypes = vm.promotedTypes.val

public theorem VariableModelImpl.refines.unique {vmI : VariableModelImpl}
    {vm₁ vm₂ : VariableModel} :
    vmI.refines vm₁ → vmI.refines vm₂ → vm₁ = vm₂ := by
  intro h₁ h₂
  ext
  rw [←h₁.types, ←h₂.types]

@[simp]
public theorem VariableModelImpl.refines.empty :
    (⟨[]⟩ : VariableModelImpl).refines ⟨∅⟩ := by
  constructor
  · simp

@[simp]
public theorem VariableModelImpl.refines.single {T : τ} :
    (⟨[T]⟩ : VariableModelImpl).refines ⟨.single T⟩ := by
  constructor
  · simp

public theorem VariableModelImpl.refines.currentTypes {vmI : VariableModelImpl} {vm : VariableModel}
    {baseType : τ} : vmI.refines vm → vmI.currentType baseType = vm.currentType baseType := by
  intro hrefines
  simp [VariableModelImpl.currentType, VariableModelImpl.promotedType?, VariableModel.currentType]
  rw [hrefines.types]

/--
Refinement implies that `vmI` and `vm` agree about whether a promotion to `T` is possible: appending
`T` to `vmI`'s list of promoted types produces a valid promotion chain iff `vm`'s promotion chain
strictly bounds `T`.
-/
public theorem VariableModelImpl.refines.strictly_bounds_iff {vmI : VariableModelImpl}
    {vm : VariableModel} {T : τ} (hrefines : vmI.refines vm) :
    isPromotionChain (vmI.promotedTypes ++ [T]) ↔ vm.promotedTypes.strictly_bounds T := by
  rw [PromotionChain.strictly_bounds, hrefines.types]

/--
The algorithm promotes a variable to `T` by appending `T` to its list of promoted types, but only
when the resulting list is a valid promotion chain. This theorem shows that doing so refines
`PromotionChain.tryPromote`, which appends `T` under precisely the same circumstances.
-/
public theorem VariableModelImpl.refines.promote {vmI : VariableModelImpl} {vm : VariableModel}
    {T : τ} (hrefines : vmI.refines vm) (hchain : isPromotionChain (vmI.promotedTypes ++ [T])) :
    (⟨vmI.promotedTypes ++ [T]⟩ : VariableModelImpl).refines ⟨vm.promotedTypes.tryPromote T⟩ := by
  have hbounds : vm.promotedTypes.strictly_bounds T := hrefines.strictly_bounds_iff.mp hchain
  constructor
  simp [hbounds, hrefines.types]

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
  simp [hrefines₁.types, hrefines₂.types]
  rw [joinPromotedTypesImpl_pure_correct vm₁.promotedTypes vm₂.promotedTypes]
  constructor; simp

end FlowAnalysis
