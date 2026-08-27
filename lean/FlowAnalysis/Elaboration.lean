module
import FlowAnalysis.Types
public import FlowAnalysis.State
public import FlowAnalysis.Syntax
public import FlowAnalysis.Lowered

namespace FlowAnalysis

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "ExprModel" => ExprModel (τ := τ)
local notation "FlowModel" => FlowModel (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Reference" => Reference (τ := τ)

/--
`fm.tryPromote ref T` returns an updated flow model in which the referent of `ref` has been
promoted to `T`, assuming such a promotion is valid. Otherwise it returns `fm` unchanged.
-/
@[expose]
public def FlowModel.tryPromote (ref : Option Reference) (T : τ)
    (fm : FlowModel) :
    FlowModel :=
  match ref with
  | some (Reference.var v) =>
    match fm.env v with
    | some vm =>
      if T < vm.currentType v.type then fm.set v ⟨.single T⟩ else fm
    | none => fm
  | none => fm

/-- Expression elaboration rules. -/
public inductive ElabExpr : FlowModel → Expr →
    LoweredExpr → ExprModel -> Prop where
  /-- Read of variable `v`. -/
  | var {fm v vm T} :
      (fm : FlowModel).env v = some vm →
      T = vm.currentType v.type →
      ElabExpr fm (.var v) (.var v T) ⟨T, some (.var v), fm, fm⟩
  /-- Null check operator (`e₁!`). -/
  | nullCheck {fm₀ e₁ m₁ em₁ fm} :
      ElabExpr fm₀ e₁ m₁ em₁ →
      fm = em₁.fm_after.tryPromote em₁.ref? (NonNull em₁.type) →
      ElabExpr fm₀ e₁.nullCheck m₁.nullCheck ⟨NonNull em₁.type, none, fm, fm⟩
  /-- Type cast (`e₁ as T`). -/
  | asExpr {fm₀ e₁ m₁ em₁ fm T} :
      ElabExpr fm₀ e₁ m₁ em₁ →
      fm = em₁.fm_after.tryPromote em₁.ref? T →
      ElabExpr fm₀ (e₁.as T) (m₁.as T) ⟨T, none, fm, fm⟩
  /-- Null literal (`null`). -/
  | nullLiteral {fm} :
      ElabExpr fm .null .null ⟨Γ.Null, none, fm, fm⟩

mutual

/-- Statement elaboration rules. -/
public inductive ElabStmt : FlowModel → Stmt →
    LoweredExpr → FlowModel -> Prop where
  /-- Variable declaration statement. TODO: support more than one variable. -/
  | declare fm n T :
      ElabStmt fm (.declare n T) (.declare ⟨n, T⟩ T) (fm.set ⟨n, T⟩ ⟨∅⟩)
  /-- Expression statement. -/
  | exprStmt {fm₀ e m em} :
      ElabExpr fm₀ e m em →
      ElabStmt fm₀ (.exprStmt e) m em.fm_after
  /-- If statement. -/
  | ifStmt {fm₀ e₁ m₁ em₁ s₂ m₂ fm₂ s₃ m₃ fm₃} :
      ElabExpr fm₀ e₁ m₁ em₁ →
      -- TODO: support dynamic downcast
      em₁.type = Γ.bool →
      ElabStmt em₁.fm_true s₂ m₂ fm₂ →
      ElabStmt em₁.fm_false s₃ m₃ fm₃ →
      ElabStmt fm₀ (.ifStmt e₁ s₂ s₃) (.cond m₁ m₂ m₃ Γ.Null) (fm₂.join fm₃)
  /-- Block statement. -/
  | block {fm₀ ss ms fm} :
      ElabStmts fm₀ ss ms fm →
      ElabStmt fm₀ (.block ss) (.block ms) fm

/-- Statement list elaboration rules. -/
public inductive ElabStmts : FlowModel → List Stmt →
    List (LoweredExpr) → FlowModel → Prop where
  | nil {fm} : ElabStmts fm [] [] fm
  | cons {s ss fm₀ fm₁ fm m ms} :
      ElabStmt fm₀ s m fm₁ →
      ElabStmts fm₁ ss ms fm →
      ElabStmts fm₀ (s :: ss) (m :: ms) fm

end

-- Theorems --

public theorem ElabExpr.boolInfo_onlyIf_bool {fm e m em} :
    ElabExpr fm e m em → em.fm_true ≠ em.fm_false → em.type = Γ.bool := by
  intro hDeriv hHasInfo
  induction hDeriv <;> simp_all

end FlowAnalysis
