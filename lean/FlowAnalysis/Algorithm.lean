/-
This module contains an algorithmic implementation of the flow analysis rules defined in
`FlowAnalysis.Elaboration`.
-/

module
public import Std.Data.HashMap
import FlowAnalysis.Elaboration
public import FlowAnalysis.Lowered
public import FlowAnalysis.PromotionChain.JoinImpl
public import FlowAnalysis.State
public import FlowAnalysis.Syntax
public import FlowAnalysis.Types

open FlowAnalysis

namespace FlowAnalysis

open DartTypeRepr
open PromotionChain

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "Expr" => Expr (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Reference" => Reference (τ := τ)
local notation "Stmt" => Stmt (τ := τ)
local notation "VariableModelImpl" => VariableModelImpl (τ := τ)
local notation "Variable" => Variable (τ := τ)

/-- Not exposed so that proofs can't rely on it -/
public def unspecifiedPromotionChain : List τ := []

-- TODO: use a more PromotionInfo-like structure
@[ext]
public structure FlowModelA where
  env : Std.HashMap Variable VariableModelImpl
deriving Inhabited

local notation "FlowModelA" => FlowModelA (τ := τ)

@[expose]
public def FlowModelA.empty : FlowModelA := ⟨∅⟩

@[expose]
public def mergeMaps {α β : Type} [BEq α] [Hashable α]
    (f : β → β → β) (m₁ m₂ : Std.HashMap α β) : Std.HashMap α β :=
  m₁.filterMap fun k v₁ =>
    match m₂[k]? with
     | none => none
     | some v₂ => f v₁ v₂

@[expose]
public def FlowModelA.join (fmA₁ fmA₂ : FlowModelA) :
    FlowModelA :=
  -- TODO: reachability
  -- TODO: identical check
  if fmA₁.env.isEmpty then fmA₁ else
  if fmA₂.env.isEmpty then fmA₂ else
  ⟨mergeMaps VariableModelImpl.join fmA₁.env fmA₂.env⟩

public structure ExprModelA where
  type : τ
  ref? : Option Reference
  boolInfo : Option (FlowModelA × FlowModelA)

local notation "ExprModelA" => ExprModelA (τ := τ)

public structure Config where

/--
Elaboration algorithms are defined using a state monad that records the current flow analysis
state. This state is updated as we recursively traverse the code being analyzed.
-/
public abbrev AlgM :=
  ReaderT Config (StateT FlowModelA (ExceptT String Id))

local notation "AlgM" => AlgM (τ := τ)

@[expose]
public def tryPromoteA (ref : Option Reference) (T : τ) :
    AlgM Unit := do
  match ref with
  | some (Reference.var v) =>
    match (<- get).env[v]? with
    | some vmI =>
      if T < vmI.currentType v.type ∧ isPromotionChain (vmI.promotedTypes ++ [T]) then
        modify (fun s => {
          s with env := s.env.insert v {vmI with promotedTypes := vmI.promotedTypes ++ [T]}})
    | none => pure ()
  | none => pure ()

mutual

@[expose]
public def elabExprA (e : Expr) :
    AlgM
      (LoweredExpr × ExprModelA) := do
  match e with
  | .var v =>
    match (<- get).env[v]? with
    | some vm =>
        let T := vm.currentType v.type
        pure (LoweredExpr.var v T, ⟨T, some (Reference.var v), none⟩)
    | none => throw s!"Undefined variable {v.name}"
  | .nullCheck eInner =>
    let (m, emA) <- elabExprA eInner
    let T' := NonNull emA.type
    tryPromoteA emA.ref? T'
    pure (m.nullCheck, ⟨T', none, none⟩)
  | .as eInner T =>
    let (m, emA) <- elabExprA eInner
    tryPromoteA emA.ref? T
    pure (m.as T, ⟨T, none, none⟩)
  | .null =>
    pure (.null, ⟨Γ.Null, none, none⟩)

public def elabStmtA (s : Stmt) :
    AlgM LoweredExpr := do
  match s with
  | .declare n T =>
    modify (fun s => { s with env := s.env.insert ⟨n, T⟩ ⟨[], [], true, false, some ⟨⟩⟩ })
    pure (LoweredExpr.declare ⟨n, T⟩ T)
  | .exprStmt e =>
    let (m, _) <- elabExprA e
    pure m
  | .ifStmt e₁ s₂ s₃ =>
    let (m₁, em₁) <- elabExprA e₁
    -- TODO: handle dynamic
    if em₁.type != Γ.bool then throw s!"Type of {e₁} is {em₁.type}, expected bool" else
    -- TODO: make a helper function for some of this logic?
    let fm₁ <- get
    let (fm₁_true, fm₁_false) := em₁.boolInfo.getD (fm₁, fm₁)
    set fm₁_true
    let m₂ <- elabStmtA s₂
    let fm₂ <- get
    set fm₁_false
    let m₃ <- elabStmtA s₃
    let fm₃ <- get
    set (fm₂.join fm₃)
    pure (.cond m₁ m₂ m₃ Γ.Null)
  | .block stmts =>
    let loweredStmts <- elabStmtsA stmts
    pure (LoweredExpr.block loweredStmts)

public def elabStmtsA (ss : List Stmt) :
    AlgM (List LoweredExpr) := do
  match ss with
  | [] => pure []
  | s :: ss' =>
    let loweredS <- elabStmtA s
    let loweredSS <- elabStmtsA ss'
    pure (loweredS :: loweredSS)

end

end FlowAnalysis
