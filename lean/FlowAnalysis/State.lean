module
public import FlowAnalysis.Elements
public import FlowAnalysis.PromotionChain.Basic
public import FlowAnalysis.Types
public import FlowAnalysis.VariableModel.Basic

namespace FlowAnalysis

variable {τ : Type} [DartTypeRepr τ]

local notation "VariableModel" => VariableModel (τ := τ)
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
  env : Variable → Option VariableModel

local notation "FlowModel" => FlowModel (τ := τ)

/-- The initial state of flow analysis. -/
@[expose]
public def FlowModel.empty : FlowModel := ⟨fun _ => none⟩

/-- `fm.set v T` returns a modified `FlowModel` in which the type of `v` has been changed to `T`. -/
@[expose]
public def FlowModel.set (fm : FlowModel) (v : Variable)
    (vm : VariableModel) : FlowModel :=
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
    {vm : VariableModel} :
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

/--
Setting a variable to the variable model it already has leaves the flow model unchanged.

This is useful for reasoning about elaboration rules that unconditionally update `env`, in cases
where the updated value turns out to be the value that was already there.
-/
@[simp]
public theorem FlowModel.set_self {fm : FlowModel} {v : Variable}
    {vm : VariableModel} (hlookup : fm.env v = some vm) : fm.set v vm = fm := by
  apply extensionality; intro v'
  simp only [env_set]
  split <;> simp_all

@[simp]
public theorem FlowModel.join_idempotent (fm : FlowModel) :
    fm.join fm = fm := by
  apply extensionality; intro v
  simp [FlowModel.join]
  cases fm.env v <;> simp_all

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
