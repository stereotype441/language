module
public import FlowAnalysis.Elements
public import FlowAnalysis.Types

namespace FlowAnalysis

variable {τ : Type} [DartTypeRepr τ]

local notation "Variable" => Variable (τ := τ)

public inductive Expr where
  | var (v : Variable)
  | nullCheck (e₁ : Expr)
  | as (e₁ : Expr) (T : τ)
  | null
  deriving Repr

local notation "Expr" => Expr (τ := τ)

public instance Expr.instToString : ToString Expr where
  toString e := (repr e).pretty

public inductive Stmt where
  | declare (n : String) (T : τ)
  | exprStmt (e : Expr)
  | ifStmt (e₁ : Expr) (s₂ s₃ : Stmt)
  | block (ss : List Stmt)

end FlowAnalysis
