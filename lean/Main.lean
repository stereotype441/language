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
    let runResult ← elabStmtA s ⟨⟩ FlowModelA.empty
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

-- TODO: switch to tests so I don't need this.
public def main : IO Unit := do
  IO.println "All proofs and declarations checked successfully!"
