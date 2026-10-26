module
public import DartLang.Elements
public import DartLang.Types

/-!
# The surface syntax that flow analysis analyzes

This module defines the subset of surface Dart that the specification of flow analysis
(`FlowAnalysis.Elaboration`) covers: expressions (`Expr`) and statements (`Stmt`), after type
inference, so that every type in them is known. It also defines how nodes and variables are
identified: by their positions in the syntax tree (`AstPath`), and by the scopes in which names are
resolved (`Scope`).
-/

namespace FlowAnalysis
open DartLang

variable {τ : Type} [DartTypeRepr τ]

/--
The position of a node in the syntax tree, as the list of child indices leading to it from the root,
innermost first.

The elaboration rules and the algorithm label each value version by the path of the node that
creates it (see `ValueVersion.root`), in place of the object identity that Dart's `ValueVersion`
has. Distinct nodes have distinct paths, so distinct nodes mint distinct versions. Likewise, a
variable is identified by the path of the statement that declares it (see `Scope`).

Children are numbered as follows:

- `Expr.nullCheck e₁`, `Expr.as e₁ T`, `Expr.property e₁ p` and `Stmt.exprStmt e₁`: `e₁` is child
  `0`.
- `Stmt.ifStmt e₁ s₂ s₃`: `e₁`, `s₂` and `s₃` are children `0`, `1` and `2`.
- `Stmt.block ss`: the list `ss` is child `0`.
- A nonempty statement list `s :: ss`: `s` is child `0`, and the list `ss` is child `1`.
-/
public abbrev AstPath := List Nat

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)

/-- A surface Dart expression. -/
public inductive Expr where
  /--
  A read of the variable named `n`. Which variable that is depends on the scope (see `Scope`): the
  innermost declaration of `n` that is in scope.
  -/
  | var (n : String)
  /-- A null check (`e₁!`). -/
  | nullCheck (e₁ : Expr)
  /-- A cast (`e₁ as T`). -/
  | as (e₁ : Expr) (T : τ)
  /-- The null literal (`null`). -/
  | null
  /-- A read of property `p` of the value of `e₁` (`e₁.p`). -/
  | property (e₁ : Expr) (p : Property)
  deriving Repr

local notation "Expr" => Expr (τ := τ)

/-- Expressions are converted to strings via `Repr`, for test output. -/
public instance Expr.instToString : ToString Expr where
  toString e := (repr e).pretty

/-- A surface Dart statement. -/
public inductive Stmt where
  /-- A local variable declaration, `T n;`, with no initializer. -/
  | declare (n : String) (T : τ)
  /-- An expression statement (`e;`). -/
  | exprStmt (e : Expr)
  /-- An `if` statement (`if (e₁) s₂ else s₃`). -/
  | ifStmt (e₁ : Expr) (s₂ s₃ : Stmt)
  /-- A block (`{ ss }`). -/
  | block (ss : List Stmt)

local notation "Stmt" => Stmt (τ := τ)

/--
The variables in scope at some point in the program, innermost first. Each entry gives a variable's
name, the variable itself, and the AST path of the statement that declares it.

The AST path is the variable's identity: flow analysis records what it knows about the variable
under it (see `Key.var`), in place of the identity of the variable's element that Dart's
`PromotionKeyStore` uses. So an inner declaration that shadows an outer one, even with the same name
and type, is a distinct variable.

A declaration's scope starts at the statement after it (see `Stmt.extendScope`). This departs from
the language specification, where every declaration in a block is in scope throughout the block,
and it's a compile-time error to refer to a local variable before its declaration. So a program
such as `int x; { x; int x; }` is an error in Dart, but here the first inner read of `x` refers to
the outer `x`. This only matters for programs that Dart rejects, so it doesn't affect soundness.
TODO: reject a reference to a variable before its declaration in the same block.
-/
public abbrev Scope := List (String × Variable × AstPath)

local notation "Scope" => Scope (τ := τ)

/--
`s.extendScope σ π` is the scope that statements following `s` (at AST path `π`) in the same
statement list are analyzed in: `σ`, plus the variable that `s` declares, if any.
-/
@[expose]
public def Stmt.extendScope (σ : Scope) (π : AstPath) : Stmt → Scope
  | .declare n T => (n, ⟨n, T⟩, π) :: σ
  | _ => σ

end FlowAnalysis
