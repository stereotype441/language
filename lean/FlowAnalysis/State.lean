module
public import FlowAnalysis.Elements
public import FlowAnalysis.PromotionChain.Basic
public import FlowAnalysis.Types
public import FlowAnalysis.PromotionModel.Basic

namespace FlowAnalysis

variable {τ : Type} [DartTypeRepr τ] {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := ℓ)
local notation "Variable" => Variable (τ := τ)

/-- A part of the program being analyzed that is a candidate for type promotion. -/
public inductive Reference where
  /-- A local variable. -/
  | var (v : Variable)
  /- TODO: promotable field, `this`, `super`. -/
  deriving Repr, BEq

local notation "Reference" => Reference (τ := τ)

/-- The state of a function at a particular point in its execution. -/
@[ext]
public structure FlowModel where
  /-- Partial function mapping `Variable`s to type promotion information. -/
  promotionInfo : Variable → Option PromotionModel

local notation "FlowModel" => FlowModel (τ := τ) (ℓ := ℓ)

/-- The initial state of flow analysis. -/
@[expose]
public def FlowModel.empty : FlowModel := ⟨fun _ => none⟩

/-- `fm.set v T` returns a modified `FlowModel` in which the type of `v` has been changed to `T`. -/
@[expose]
public def FlowModel.set (fm : FlowModel) (v : Variable)
    (pm : PromotionModel) : FlowModel :=
  ⟨fun v' => if v = v' then pm else fm.promotionInfo v'⟩

-- TODO: implement full `join` behavior.
@[expose]
public def FlowModel.join (fm₁ fm₂ : FlowModel) : FlowModel :=
  ⟨fun v =>
     match fm₁.promotionInfo v with
     | none => none
     | some pm₁ =>
         match fm₂.promotionInfo v with
         | none => none
         | some pm₂ => pm₁.join pm₂⟩

-- FlowModel Theorems --

-- Decidable equality of labels is only needed in order to join flow models, so omit it from the
-- lemmas below; the declarations that do join reintroduce it explicitly.
omit [DecidableEq ℓ]

@[simp]
public theorem FlowModel.promotionInfo_set {fm : FlowModel} {v v' T} :
    (fm.set v T).promotionInfo v' = if v = v' then some T else fm.promotionInfo v' := by
  simp_all [FlowModel.set]

public theorem FlowModel.set_get?_neq {fm : FlowModel} {v v' : Variable}
    {pm : PromotionModel} :
    v ≠ v' → (fm.set v pm).promotionInfo v' = fm.promotionInfo v' := by
  intro hNeq
  simp [hNeq]

@[simp]
public theorem FlowModel.get?_set {fm : FlowModel} {v v' T} :
    (fm.set v T).promotionInfo v' = if v = v' then some T else fm.promotionInfo v' := by
  simp_all [FlowModel.set]

public theorem FlowModel.extensionality {fm fm' : FlowModel} :
    (∀ v : Variable, fm.promotionInfo v = fm'.promotionInfo v) → fm = fm' := by
  rcases fm; rename_i promotionInfo
  rcases fm'; rename_i promotionInfo'
  simp
  apply funext

/--
Setting a variable to the variable model it already has leaves the flow model unchanged.

This is useful for reasoning about elaboration rules that unconditionally update `promotionInfo`, in cases
where the updated value turns out to be the value that was already there.
-/
@[simp]
public theorem FlowModel.set_self {fm : FlowModel} {v : Variable}
    {pm : PromotionModel} (hlookup : fm.promotionInfo v = some pm) : fm.set v pm = fm := by
  apply extensionality; intro v'
  simp only [promotionInfo_set]
  split <;> simp_all

@[simp]
public theorem FlowModel.join_idempotent [DecidableEq ℓ] (fm : FlowModel) :
    fm.join fm = fm := by
  apply extensionality; intro v
  simp [FlowModel.join]
  cases fm.promotionInfo v <;> simp_all

instance FlowModel.instIdempotentOpJoin :
    Std.IdempotentOp (FlowModel.join (τ := τ) (ℓ := ℓ)) where
  idempotent := join_idempotent

public structure ExprModel where
  type : τ
  ref? : Option Reference
  fm_true : FlowModel
  fm_false : FlowModel

local notation "ExprModel" => ExprModel (τ := τ) (ℓ := ℓ)

@[expose]
public def ExprModel.fm_after (em : ExprModel) := em.fm_true.join em.fm_false

@[simp]
public theorem ExprModel.simple_after [DecidableEq ℓ] {ref? : Option Reference} {T : τ}
    {fm : FlowModel} :
    (ExprModel.mk T ref? fm fm).fm_after = fm := by
  simp [ExprModel.fm_after]

end FlowAnalysis
