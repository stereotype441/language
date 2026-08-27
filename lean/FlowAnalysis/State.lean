module
public import FlowAnalysis.Elements
public import FlowAnalysis.PromotionChain
public import FlowAnalysis.Types

namespace FlowAnalysis

variable {τ : Type} [DartTypeRepr τ]

local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "Variable" => Variable (τ := τ)

/-- A part of the program being analyzed that is a candidate for type promotion. -/
public inductive Reference where
  /-- A local variable. -/
  | var (v : Variable)
  /- TODO: promotable field, `this`, `super`. -/
  deriving Repr, BEq

local notation "Reference" => Reference (τ := τ)

/-- The state of a promotable value at a particular point in a function's execution. -/
@[ext]
public structure ValueModel where
  promotedTypes : PromotionChain

local notation "ValueModel" => ValueModel (τ := τ)

@[expose]
public def ValueModel.currentType (vm : ValueModel) (baseType : τ) :=
  match vm.promotedTypes.val.getLast? with
  | none => baseType
  | some T => if T ≤ baseType then T else baseType

@[expose]
public def ValueModel.join (vm₁ vm₂ : ValueModel) :
    ValueModel :=
  ⟨vm₁.promotedTypes.join vm₂.promotedTypes⟩

/-- The state of a function at a particular point in its execution. -/
@[ext]
public structure FlowModel where
  /-- Partial function mapping `Variable`s to type promotion information. -/
  env : Variable → Option ValueModel

local notation "FlowModel" => FlowModel (τ := τ)

/-- The initial state of flow analysis. -/
@[expose]
public def FlowModel.empty : FlowModel := ⟨fun _ => none⟩

/-- `fm.set v T` returns a modified `FlowModel` in which the type of `v` has been changed to `T`. -/
@[expose]
public def FlowModel.set (fm : FlowModel) (v : Variable)
    (vm : ValueModel) : FlowModel :=
  ⟨fun v' => if v = v' then vm else fm.env v'⟩

-- TODO: implement full `join` behavior.
@[expose]
public def FlowModel.join (fm₁ fm₂ : FlowModel) : FlowModel :=
  ⟨fun v =>
     match fm₁.env v with
     | none => none
     | some vm₁ =>
         match fm₂.env v with
         | none => none
         | some vm₂ => vm₁.join vm₂⟩

-- FlowModel Theorems --

@[simp]
public theorem FlowModel.env_set {fm : FlowModel} {v v' T} :
    (fm.set v T).env v' = if v = v' then some T else fm.env v' := by
  simp_all [FlowModel.set]

public theorem FlowModel.set_get?_neq {fm : FlowModel} {v v' : Variable}
    {vm : ValueModel} :
    v ≠ v' → (fm.set v vm).env v' = fm.env v' := by
  intro hNeq
  simp [hNeq]

@[simp]
public theorem FlowModel.get?_set {fm : FlowModel} {v v' T} :
    (fm.set v T).env v' = if v = v' then some T else fm.env v' := by
  simp_all [FlowModel.set]

public theorem FlowModel.extensionality {fm fm' : FlowModel} :
    (∀ v : Variable, fm.env v = fm'.env v) → fm = fm' := by
  rcases fm; rename_i env
  rcases fm'; rename_i env'
  simp
  apply funext

@[simp]
public theorem FlowModel.join_idempotent (fm : FlowModel) :
    fm.join fm = fm := by
  apply extensionality; intro v
  simp [FlowModel.join]
  cases fm.env v <;> simp_all
  case some vm =>
    ext; simp [ValueModel.join]

instance FlowModel.instIdempotentOpJoin : Std.IdempotentOp (FlowModel.join (τ := τ)) where
  idempotent := join_idempotent

public structure ExprModel where
  type : τ
  ref? : Option Reference
  fm_true : FlowModel
  fm_false : FlowModel

local notation "ExprModel" => ExprModel (τ := τ)

@[expose]
public def ExprModel.fm_after (em : ExprModel) := em.fm_true.join em.fm_false

@[simp]
public theorem ExprModel.simple_after {ref? : Option Reference} {T : τ}
    {fm : FlowModel} :
    (ExprModel.mk T ref? fm fm).fm_after = fm := by
  simp [ExprModel.fm_after]

end FlowAnalysis
