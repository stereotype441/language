module
public meta import FlowAnalysis.Algorithm
public meta import FlowAnalysis.Lowered
import FlowAnalysis
public meta import FlowAnalysis.SimpleTypes
import FlowAnalysis.SimpleTypes

open FlowAnalysis
open SimpleType

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Stmt" => Stmt (τ := SimpleType)
local notation "Variable" => Variable (τ := SimpleType)

def runFlowAnalysis (s : Stmt) : LoweredExpr ⊕ String :=
  let loweredResult := do
    -- `s` is the root of the syntax tree, so its AST path is `[]`.
    let runResult ← elabStmtImpl s ⟨[]⟩ AlgState.initial
    pure runResult.fst
  match loweredResult with
    | .ok m => .inl m
    | .error s => .inr s

@[simp]
def x : Variable := ⟨"x", ObjectQ⟩

def testNullAssertAST : Stmt :=
  Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (Expr.nullCheck (Expr.var x)),
    Stmt.exprStmt (Expr.var x)
  ]

def expectedNullAssertLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ,
    LoweredExpr.nullCheck (LoweredExpr.var x ObjectQ),
    LoweredExpr.var x Object
  ]

#guard runFlowAnalysis testNullAssertAST == .inl expectedNullAssertLowered

def testAsExprAST : Stmt :=
  Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var x).as Object),
    Stmt.exprStmt (Expr.var x)
  ]

def expectedAsExprLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ,
    (LoweredExpr.var x ObjectQ).as Object,
    LoweredExpr.var x Object
  ]

#guard runFlowAnalysis testAsExprAST == .inl expectedAsExprLowered

def testNullLiteralAST : Stmt :=
  Stmt.block [
    Stmt.exprStmt .null
  ]

def expectedNullLiteralLowered : LoweredExpr :=
  LoweredExpr.block [
    .null
  ]

#guard runFlowAnalysis testNullLiteralAST == .inl expectedNullLiteralLowered

def testNullAssertAsIntAST : Stmt :=
  Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var x).nullCheck.as int),
    Stmt.exprStmt (Expr.var x)
  ]

def expectedNullAssertAsIntLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ,
    (LoweredExpr.nullCheck (LoweredExpr.var x ObjectQ)).as int,
    -- The fact that `x` is typed as `Object` here rather than `int` demonstrates a sound but
    -- limiting design choice in Dart's current flow analysis. Because `x!` outputs `none` as
    -- its reference rather than retaining the variable reference, the outer `as int` check
    -- cannot promote `x` any further.
    LoweredExpr.var x Object
  ]

#guard runFlowAnalysis testNullAssertAsIntAST == .inl expectedNullAssertAsIntLowered

def testAsObjectAsIntAST : Stmt :=
  Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (((Expr.var x).as Object).as int),
    Stmt.exprStmt (Expr.var x)
  ]

def expectedAsObjectAsIntLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ,
    ((LoweredExpr.var x ObjectQ).as Object).as int,
    -- Just like with `x!`, `x as Object` outputs `none` as its reference. Thus, the outer
    -- `as int` check receives no reference and cannot promote `x` to `int`. This is a limitation
    -- that prevents chained promotions.
    LoweredExpr.var x Object
  ]

#guard runFlowAnalysis testAsObjectAsIntAST == .inl expectedAsObjectAsIntLowered

@[simp]
def y : Variable := ⟨"y", ObjectQ⟩

@[simp]
def b : Variable := ⟨"b", bool⟩

/-- A promotable property. Its name is private, since Dart only promotes private fields. -/
def f : Property (τ := SimpleType) := ⟨"_f", ObjectQ, true⟩

/-- Another promotable property. -/
def g : Property (τ := SimpleType) := ⟨"_g", ObjectQ, true⟩

/-- A property that isn't promotable. -/
def h : Property (τ := SimpleType) := ⟨"h", ObjectQ, false⟩

def testPropertyNullAssertAST : Stmt :=
  Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var x).property f).nullCheck,
    Stmt.exprStmt ((Expr.var x).property f)
  ]

def expectedPropertyNullAssertLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ,
    ((LoweredExpr.var x ObjectQ).propertyGet f ObjectQ).nullCheck,
    -- The first promotion of a property starts from a fresh promotion model, so it succeeds.
    (LoweredExpr.var x ObjectQ).propertyGet f Object
  ]

#guard runFlowAnalysis testPropertyNullAssertAST == .inl expectedPropertyNullAssertLowered

/-- The type of the last statement of a block, if flow analysis succeeds. -/
def lastType (s : Stmt) : Option SimpleType :=
  match runFlowAnalysis s with
  | .inl (.block ms) => ms.getLast?.map (·.typeOf)
  | _ => none

-- Promoting `x._f` doesn't promote `y._f`.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.declare "y" ObjectQ,
    Stmt.exprStmt ((Expr.var x).property f).nullCheck,
    Stmt.exprStmt ((Expr.var y).property f)
  ]) == some ObjectQ

-- A non-promotable property isn't promoted.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var x).property h).nullCheck,
    Stmt.exprStmt ((Expr.var x).property h)
  ]) == some ObjectQ

-- Nested properties are promoted.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (((Expr.var x).property f).property g).nullCheck,
    Stmt.exprStmt (((Expr.var x).property f).property g)
  ]) == some Object

-- Promoting `x._f._g` doesn't promote `x._g`: they are at different paths.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (((Expr.var x).property f).property g).nullCheck,
    Stmt.exprStmt ((Expr.var x).property g)
  ]) == some ObjectQ

-- Redeclaring `x` gives it a new value version, so the promotion of the old value's `_f` is lost.
--
-- TODO(stage 6): this test is a stand-in. Dart doesn't allow two variables with the same name to be
-- declared in the same block, so the second `declare` should be an assignment to `x`. Rewrite the
-- test that way once `Expr` can model assignments.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var x).property f).nullCheck,
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var x).property f)
  ]) == some ObjectQ

-- A property promoted on only one branch of an `if` isn't promoted after it.
#guard lastType (Stmt.block [
    Stmt.declare "b" bool,
    Stmt.declare "x" ObjectQ,
    Stmt.ifStmt (Expr.var b)
      (Stmt.block [Stmt.exprStmt ((Expr.var x).property f).nullCheck])
      (Stmt.block []),
    Stmt.exprStmt ((Expr.var x).property f)
  ]) == some ObjectQ

-- A property promoted on both branches of an `if` is promoted after it.
#guard lastType (Stmt.block [
    Stmt.declare "b" bool,
    Stmt.declare "x" ObjectQ,
    Stmt.ifStmt (Expr.var b)
      (Stmt.block [Stmt.exprStmt ((Expr.var x).property f).nullCheck])
      (Stmt.block [Stmt.exprStmt ((Expr.var x).property f).nullCheck]),
    Stmt.exprStmt ((Expr.var x).property f)
  ]) == some Object

-- TODO: switch to tests so I don't need this.
public def main : IO Unit := do
  IO.println "All proofs and declarations checked successfully!"
