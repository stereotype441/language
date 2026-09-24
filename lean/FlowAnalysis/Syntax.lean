module
public import FlowAnalysis.Elements
public import FlowAnalysis.Types

namespace FlowAnalysis

variable {τ : Type} [DartTypeRepr τ]

/--
The position of a node in the syntax tree, as the list of child indices leading to it from the root,
innermost first.

The elaboration rules and the algorithm label each value version by the path of the node that
creates it (see `ValueVersion.root`), in place of the object identity that Dart's `ValueVersion`
has. Distinct nodes have distinct paths, so distinct nodes mint distinct versions.

Children are numbered as follows:

- `Expr.nullCheck e₁`, `Expr.as e₁ T` and `Stmt.exprStmt e₁`: `e₁` is child `0`.
- `Stmt.ifStmt e₁ s₂ s₃`: `e₁`, `s₂` and `s₃` are children `0`, `1` and `2`.
- `Stmt.block ss`: the list `ss` is child `0`.
- A nonempty statement list `s :: ss`: `s` is child `0`, and the list `ss` is child `1`.
-/
public abbrev AstPath := List Nat

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
