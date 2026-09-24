module
public import FlowAnalysis.Elements
public import FlowAnalysis.Types

namespace FlowAnalysis

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)

/--
Lowered, fully type-checked AST form.

Note that we make no distinction between statements and expressions. This is for future
compatibility with the Iris framework.
-/
public inductive LoweredExpr where
  | var (v : Variable) (T : τ)
  | nullCheck (m : LoweredExpr)
  | as (m : LoweredExpr) (T : τ)
  | is (m : LoweredExpr) (T : τ)
  | null
  | declare (v : Variable) (T : τ)
  | cond (m₁ m₂ m₃ : LoweredExpr) (T : τ)
  | block (exprs : List LoweredExpr)
  /-- A read of property `p` of the value of `m`, whose type (after any promotion) is `T`. -/
  | propertyGet (m : LoweredExpr) (p : Property) (T : τ)
  deriving Repr, BEq

local notation "LoweredExpr" => LoweredExpr (τ := τ)

@[expose]
public def LoweredExpr.typeOf :
    LoweredExpr -> τ
  | var _ T => T
  | nullCheck m => NonNull m.typeOf
  | as _ T => T
  | is _ _ => Γ.bool
  | null => Γ.Null
  | declare _ _ => Γ.Null
  | cond _ _ _ T => T
  | block _ => Γ.Null
  | propertyGet _ _ T => T

end FlowAnalysis
