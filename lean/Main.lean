module
public meta import FlowAnalysis.Algorithm
public meta import DartLang.Lowered
import FlowAnalysis
public meta import DartLang.SimpleTypes
import DartLang.SimpleTypes

open FlowAnalysis
open DartLang
open SimpleType

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Stmt" => Stmt (τ := SimpleType)
local notation "Variable" => Variable (τ := SimpleType)

def runFlowAnalysis (s : Stmt) : LoweredExpr ⊕ String :=
  let loweredResult := do
    -- `s` is the root of the syntax tree, so its AST path is `[]`, and no variables are in scope.
    let runResult ← elabStmtImpl s ⟨[], []⟩ AlgState.initial
    pure runResult.fst
  match loweredResult with
    | .ok m => .inl m
    | .error s => .inr s

@[simp]
def x : Variable := { name := "x", type := ObjectQ }

def testNullAssertAST : Stmt :=
  Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (Expr.nullCheck (Expr.var "x")),
    Stmt.exprStmt (Expr.var "x")
  ]

def expectedNullAssertLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ true,
    LoweredExpr.nullCheck (LoweredExpr.var x ObjectQ),
    LoweredExpr.var x Object
  ]

#guard runFlowAnalysis testNullAssertAST == .inl expectedNullAssertLowered

def testAsExprAST : Stmt :=
  Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var "x").as Object),
    Stmt.exprStmt (Expr.var "x")
  ]

def expectedAsExprLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ true,
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
    Stmt.exprStmt ((Expr.var "x").nullCheck.as int),
    Stmt.exprStmt (Expr.var "x")
  ]

def expectedNullAssertAsIntLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ true,
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
    Stmt.exprStmt (((Expr.var "x").as Object).as int),
    Stmt.exprStmt (Expr.var "x")
  ]

def expectedAsObjectAsIntLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ true,
    ((LoweredExpr.var x ObjectQ).as Object).as int,
    -- Just like with `x!`, `x as Object` outputs `none` as its reference. Thus, the outer
    -- `as int` check receives no reference and cannot promote `x` to `int`. This is a limitation
    -- that prevents chained promotions.
    LoweredExpr.var x Object
  ]

#guard runFlowAnalysis testAsObjectAsIntAST == .inl expectedAsObjectAsIntLowered

/-- A promotable property. Its name is private, since Dart only promotes private fields. -/
def f : Property (τ := SimpleType) := ⟨"_f", ObjectQ, true⟩

/-- Another promotable property. -/
def g : Property (τ := SimpleType) := ⟨"_g", ObjectQ, true⟩

/-- A property that isn't promotable. -/
def h : Property (τ := SimpleType) := ⟨"h", ObjectQ, false⟩

def testPropertyNullAssertAST : Stmt :=
  Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var "x").property f).nullCheck,
    Stmt.exprStmt ((Expr.var "x").property f)
  ]

def expectedPropertyNullAssertLowered : LoweredExpr :=
  LoweredExpr.block [
    LoweredExpr.declare x ObjectQ true,
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
    Stmt.exprStmt ((Expr.var "x").property f).nullCheck,
    Stmt.exprStmt ((Expr.var "y").property f)
  ]) == some ObjectQ

-- A non-promotable property isn't promoted.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var "x").property h).nullCheck,
    Stmt.exprStmt ((Expr.var "x").property h)
  ]) == some ObjectQ

-- Nested properties are promoted.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (((Expr.var "x").property f).property g).nullCheck,
    Stmt.exprStmt (((Expr.var "x").property f).property g)
  ]) == some Object

-- Promoting `x._f._g` doesn't promote `x._g`: they are at different paths.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (((Expr.var "x").property f).property g).nullCheck,
    Stmt.exprStmt ((Expr.var "x").property g)
  ]) == some ObjectQ

-- Assigning to `x` gives it a new value version, so the promotion of the old value's `_f` is lost.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.declare "y" ObjectQ,
    Stmt.exprStmt ((Expr.var "x").property f).nullCheck,
    Stmt.exprStmt (Expr.assign "x" (Expr.var "y")),
    Stmt.exprStmt ((Expr.var "x").property f)
  ]) == some ObjectQ

-- A property promoted on only one branch of an `if` isn't promoted after it.
#guard lastType (Stmt.block [
    Stmt.declare "c" ObjectQ,
    Stmt.declare "b" bool,
    -- `b` must be definitely assigned before it's read.
    Stmt.exprStmt (Expr.assign "b" ((Expr.var "c").as bool)),
    Stmt.declare "x" ObjectQ,
    Stmt.ifStmt (Expr.var "b")
      (Stmt.block [Stmt.exprStmt ((Expr.var "x").property f).nullCheck])
      (Stmt.block []),
    Stmt.exprStmt ((Expr.var "x").property f)
  ]) == some ObjectQ

-- A property promoted on both branches of an `if` is promoted after it.
#guard lastType (Stmt.block [
    Stmt.declare "c" ObjectQ,
    Stmt.declare "b" bool,
    -- `b` must be definitely assigned before it's read.
    Stmt.exprStmt (Expr.assign "b" ((Expr.var "c").as bool)),
    Stmt.declare "x" ObjectQ,
    Stmt.ifStmt (Expr.var "b")
      (Stmt.block [Stmt.exprStmt ((Expr.var "x").property f).nullCheck])
      (Stmt.block [Stmt.exprStmt ((Expr.var "x").property f).nullCheck]),
    Stmt.exprStmt ((Expr.var "x").property f)
  ]) == some Object

/-! ### Shadowing

A declaration in an inner block that shadows an outer variable, even one with the same name and
type, is a distinct variable: promotions of either don't affect the other.
-/

-- `Object? x; { Object? x; x!; } x;`: the inner `x!` doesn't promote the outer `x`.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.block [Stmt.declare "x" ObjectQ, Stmt.exprStmt (Expr.var "x").nullCheck],
    Stmt.exprStmt (Expr.var "x")
  ]) == some ObjectQ

-- `Object? x; { Object? x; x as Null; } x;`
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.block [Stmt.declare "x" ObjectQ, Stmt.exprStmt ((Expr.var "x").as Null)],
    Stmt.exprStmt (Expr.var "x")
  ]) == some ObjectQ

-- `Object? x; { Object? x; x._f!; } x._f;`: nor does a promotion of the inner `x._f`.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.block [Stmt.declare "x" ObjectQ, Stmt.exprStmt ((Expr.var "x").property f).nullCheck],
    Stmt.exprStmt ((Expr.var "x").property f)
  ]) == some ObjectQ

-- `bool b; Object? x; if (b) { Object? x; x!; } else { Object? x; x!; } x;`
#guard lastType (Stmt.block [
    Stmt.declare "c" ObjectQ,
    Stmt.declare "b" bool,
    -- `b` must be definitely assigned before it's read.
    Stmt.exprStmt (Expr.assign "b" ((Expr.var "c").as bool)),
    Stmt.declare "x" ObjectQ,
    Stmt.ifStmt (Expr.var "b")
      (Stmt.block [Stmt.declare "x" ObjectQ, Stmt.exprStmt (Expr.var "x").nullCheck])
      (Stmt.block [Stmt.declare "x" ObjectQ, Stmt.exprStmt (Expr.var "x").nullCheck]),
    Stmt.exprStmt (Expr.var "x")
  ]) == some ObjectQ

-- `Object? x; x!; { Object? x; x; } x;`: the inner read sees the inner `x`, which isn't promoted,
-- and the inner declaration doesn't undo the outer `x`'s promotion.
#guard runFlowAnalysis (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (Expr.var "x").nullCheck,
    Stmt.block [Stmt.declare "x" ObjectQ, Stmt.exprStmt (Expr.var "x")],
    Stmt.exprStmt (Expr.var "x")
  ]) == .inl (LoweredExpr.block [
    LoweredExpr.declare x ObjectQ true,
    LoweredExpr.nullCheck (LoweredExpr.var x ObjectQ),
    LoweredExpr.block [LoweredExpr.declare x ObjectQ true, LoweredExpr.var x ObjectQ],
    LoweredExpr.var x Object
  ])

-- `bool b; Object? x; x!; if (b) { Object? x; } else {} x;`
#guard lastType (Stmt.block [
    Stmt.declare "c" ObjectQ,
    Stmt.declare "b" bool,
    -- `b` must be definitely assigned before it's read.
    Stmt.exprStmt (Expr.assign "b" ((Expr.var "c").as bool)),
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (Expr.var "x").nullCheck,
    Stmt.ifStmt (Expr.var "b") (Stmt.block [Stmt.declare "x" ObjectQ]) (Stmt.block []),
    Stmt.exprStmt (Expr.var "x")
  ]) == some Object

-- An inner variable with a different declared type: `Object? x; x!; { dynamic x; x; } x;`
#guard runFlowAnalysis (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (Expr.var "x").nullCheck,
    Stmt.block [Stmt.declare "x" dynamic, Stmt.exprStmt (Expr.var "x")],
    Stmt.exprStmt (Expr.var "x")
  ]) == .inl (LoweredExpr.block [
    LoweredExpr.declare x ObjectQ true,
    LoweredExpr.nullCheck (LoweredExpr.var x ObjectQ),
    LoweredExpr.block [LoweredExpr.declare ⟨"x", dynamic, false⟩ dynamic true,
      LoweredExpr.var ⟨"x", dynamic, false⟩ dynamic],
    LoweredExpr.var x Object
  ])

-- A variable declared in a block is out of scope after it.
#guard (runFlowAnalysis (Stmt.block [
    Stmt.block [Stmt.declare "x" ObjectQ],
    Stmt.exprStmt (Expr.var "x")
  ])).isRight

/-! ### Assignments -/

def y : Variable := { name := "y", type := ObjectQ }

-- `Object? x; Object? y; x = y; x`: an assignment lowers to `variableSet`, and has the static type
-- of its right-hand side.
#guard runFlowAnalysis (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.declare "y" ObjectQ,
    Stmt.exprStmt (Expr.assign "x" (Expr.var "y")),
    Stmt.exprStmt (Expr.var "x")
  ]) == .inl (LoweredExpr.block [
    LoweredExpr.declare x ObjectQ true,
    LoweredExpr.declare y ObjectQ true,
    LoweredExpr.variableSet x (LoweredExpr.var y ObjectQ),
    LoweredExpr.var x ObjectQ
  ])

-- `Object? x; x as int; x = null; x`: assigning `null` demotes `x` all the way.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt ((Expr.var "x").as int),
    Stmt.exprStmt (Expr.assign "x" .null),
    Stmt.exprStmt (Expr.var "x")
  ]) == some ObjectQ

-- `Object? x; Object? y; x as Object; x as int; x = y as Object; x`: assigning an `Object` demotes
-- `x` from `int`, but keeps its promotion to `Object`.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.declare "y" ObjectQ,
    Stmt.exprStmt ((Expr.var "x").as Object),
    Stmt.exprStmt ((Expr.var "x").as int),
    Stmt.exprStmt (Expr.assign "x" ((Expr.var "y").as Object)),
    Stmt.exprStmt (Expr.var "x")
  ]) == some Object

-- `Object? x; Object? y; x = y as int; x`: no promotion. The flow analysis specification would
-- promote `x` to `Object`, a type of interest (its non-nullable declared type), but promotion to
-- types of interest isn't modeled yet.
-- TODO: expect `Object` once `PromotionModel.write` promotes to types of interest.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.declare "y" ObjectQ,
    Stmt.exprStmt (Expr.assign "x" ((Expr.var "y").as int)),
    Stmt.exprStmt (Expr.var "x")
  ]) == some ObjectQ

-- `Object? x; x!; { x = null; } x`: an assignment in a nested block demotes the outer variable.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (Expr.var "x").nullCheck,
    Stmt.block [Stmt.exprStmt (Expr.assign "x" .null)],
    Stmt.exprStmt (Expr.var "x")
  ]) == some ObjectQ

-- `Object? x; x!; { Object? x; x = null; } x`: an assignment to an inner variable doesn't affect
-- an outer variable with the same name.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (Expr.var "x").nullCheck,
    Stmt.block [Stmt.declare "x" ObjectQ, Stmt.exprStmt (Expr.assign "x" .null)],
    Stmt.exprStmt (Expr.var "x")
  ]) == some Object

-- `int i; Object? y; i = y`: the right-hand side's static type must be a subtype of the variable's
-- declared type.
#guard (runFlowAnalysis (Stmt.block [
    Stmt.declare "i" int,
    Stmt.declare "y" ObjectQ,
    Stmt.exprStmt (Expr.assign "i" (Expr.var "y"))
  ])).isRight

/-! ### Definite assignment -/

-- `Object o; o`: a variable whose type isn't nullable can't be read before it's assigned.
#guard (runFlowAnalysis (Stmt.block [
    Stmt.declare "o" Object,
    Stmt.exprStmt (Expr.var "o")
  ])).isRight

-- `Object? x; x`: a variable whose type is nullable can be (it starts out holding `null`).
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (Expr.var "x")
  ]) == some ObjectQ

-- `Object o; Object? y; o = y as Object; o`: after an assignment, it can be read.
#guard lastType (Stmt.block [
    Stmt.declare "o" Object,
    Stmt.declare "y" ObjectQ,
    Stmt.exprStmt (Expr.assign "o" ((Expr.var "y").as Object)),
    Stmt.exprStmt (Expr.var "o")
  ]) == some Object

-- `Object o; Object? y; bool b = …; if (b) { o = y as Object; } else { o = y as Object; } o`: a
-- variable assigned on both branches of an `if` is definitely assigned after it.
#guard lastType (Stmt.block [
    Stmt.declare "o" Object,
    Stmt.declare "y" ObjectQ,
    Stmt.declare "b" bool,
    Stmt.exprStmt (Expr.assign "b" ((Expr.var "y").as bool)),
    Stmt.ifStmt (Expr.var "b")
      (Stmt.block [Stmt.exprStmt (Expr.assign "o" ((Expr.var "y").as Object))])
      (Stmt.block [Stmt.exprStmt (Expr.assign "o" ((Expr.var "y").as Object))]),
    Stmt.exprStmt (Expr.var "o")
  ]) == some Object

-- `Object o; Object? y; bool b = …; if (b) { o = y as Object; } else {} o`: but not if it's
-- assigned on only one of them.
#guard (runFlowAnalysis (Stmt.block [
    Stmt.declare "o" Object,
    Stmt.declare "y" ObjectQ,
    Stmt.declare "b" bool,
    Stmt.exprStmt (Expr.assign "b" ((Expr.var "y").as bool)),
    Stmt.ifStmt (Expr.var "b")
      (Stmt.block [Stmt.exprStmt (Expr.assign "o" ((Expr.var "y").as Object))])
      (Stmt.block []),
    Stmt.exprStmt (Expr.var "o")
  ])).isRight

/-! ### `final` local variables -/

-- `final Object? x;`: a `final` variable starts out unassigned at run time, even if its type is
-- nullable (`startsNull` is `false`).
#guard runFlowAnalysis (Stmt.block [Stmt.declare "x" ObjectQ true]) ==
  .inl (LoweredExpr.block [LoweredExpr.declare ⟨"x", ObjectQ, true⟩ ObjectQ false])

-- `final Object? x; x`: so it can't be read before it's assigned, although its type is nullable.
#guard (runFlowAnalysis (Stmt.block [
    Stmt.declare "x" ObjectQ true,
    Stmt.exprStmt (Expr.var "x")
  ])).isRight

-- `final Object? x; x = null; x`: it can be assigned once, and then read.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ true,
    Stmt.exprStmt (Expr.assign "x" .null),
    Stmt.exprStmt (Expr.var "x")
  ]) == some ObjectQ

-- `final Object? x; x = null; x = null;`: but not assigned again.
#guard (runFlowAnalysis (Stmt.block [
    Stmt.declare "x" ObjectQ true,
    Stmt.exprStmt (Expr.assign "x" .null),
    Stmt.exprStmt (Expr.assign "x" .null)
  ])).isRight

-- `final Object? x; x = (x = null);`: the right-hand side runs first, so `x` isn't definitely
-- unassigned when the outer assignment happens.
#guard (runFlowAnalysis (Stmt.block [
    Stmt.declare "x" ObjectQ true,
    Stmt.exprStmt (Expr.assign "x" (Expr.assign "x" .null))
  ])).isRight

-- `Object? x; x = (x = null);`: that's fine for a variable that isn't `final`.
#guard (runFlowAnalysis (Stmt.block [
    Stmt.declare "x" ObjectQ,
    Stmt.exprStmt (Expr.assign "x" (Expr.assign "x" .null))
  ])).isLeft

-- `final Object? x; Object? y; bool b = …; if (b) { x = null; } else { x = null; } x`: a `final`
-- variable can be assigned once on each branch of an `if`, and is definitely assigned after it.
#guard lastType (Stmt.block [
    Stmt.declare "x" ObjectQ true,
    Stmt.declare "y" ObjectQ,
    Stmt.declare "b" bool,
    Stmt.exprStmt (Expr.assign "b" ((Expr.var "y").as bool)),
    Stmt.ifStmt (Expr.var "b")
      (Stmt.block [Stmt.exprStmt (Expr.assign "x" .null)])
      (Stmt.block [Stmt.exprStmt (Expr.assign "x" .null)]),
    Stmt.exprStmt (Expr.var "x")
  ]) == some ObjectQ

-- `final Object? x; Object? y; bool b = …; if (b) { x = null; } else {} x = null;`: after an `if`
-- that assigns it on only one branch, it's neither definitely assigned nor definitely unassigned,
-- so it can't be assigned.
#guard (runFlowAnalysis (Stmt.block [
    Stmt.declare "x" ObjectQ true,
    Stmt.declare "y" ObjectQ,
    Stmt.declare "b" bool,
    Stmt.exprStmt (Expr.assign "b" ((Expr.var "y").as bool)),
    Stmt.ifStmt (Expr.var "b")
      (Stmt.block [Stmt.exprStmt (Expr.assign "x" .null)])
      (Stmt.block []),
    Stmt.exprStmt (Expr.assign "x" .null)
  ])).isRight

-- TODO: switch to tests so I don't need this.
public def main : IO Unit := do
  IO.println "All proofs and declarations checked successfully!"
