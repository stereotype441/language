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

variable {τ : Type} [Γ : DartTypeRepr τ] {ℓ : Type} [DecidableEq ℓ] [Inhabited ℓ]

local notation "Expr" => Expr (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Key" => Key (τ := τ) (ℓ := ℓ)
local notation "Stmt" => Stmt (τ := τ)
local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ) (ℓ := ℓ)
local notation "Variable" => Variable (τ := τ)

/-- Not exposed so that proofs can't rely on it -/
public def unspecifiedPromotionChain : List τ := []

-- TODO: use a more PromotionInfo-like structure
@[ext]
public structure FlowModelImpl where
  promotionInfo : Std.HashMap Variable PromotionModelImpl
deriving Inhabited

local notation "FlowModelImpl" => FlowModelImpl (τ := τ) (ℓ := ℓ)

@[expose]
public def FlowModelImpl.empty : FlowModelImpl := ⟨∅⟩

@[expose]
public def mergeMaps {α β : Type} [BEq α] [Hashable α]
    (f : β → β → β) (m₁ m₂ : Std.HashMap α β) : Std.HashMap α β :=
  m₁.filterMap fun k v₁ =>
    match m₂[k]? with
     | none => none
     | some v₂ => f v₁ v₂

@[expose]
public def FlowModelImpl.join (fmI₁ fmI₂ : FlowModelImpl) :
    FlowModelImpl :=
  -- TODO: reachability
  -- TODO: identical check
  if fmI₁.promotionInfo.isEmpty then fmI₁ else
  if fmI₂.promotionInfo.isEmpty then fmI₂ else
  ⟨mergeMaps PromotionModelImpl.join fmI₁.promotionInfo fmI₂.promotionInfo⟩

public structure ExprModelImpl where
  type : τ
  ref? : Option Key
  boolInfo : Option (FlowModelImpl × FlowModelImpl)

local notation "ExprModelImpl" => ExprModelImpl (τ := τ) (ℓ := ℓ)

public structure Config where

/--
Elaboration algorithms are defined using a state monad that records the current flow analysis
state. This state is updated as we recursively traverse the code being analyzed.
-/
public abbrev AlgM :=
  ReaderT Config (StateT FlowModelImpl (ExceptT String Id))

local notation "AlgM" => AlgM (τ := τ) (ℓ := ℓ)

@[expose]
public def tryPromoteImpl (ref : Option Key) (T : τ) :
    AlgM Unit := do
  match ref with
  | some (Key.var v) =>
    match (<- get).promotionInfo[v]? with
    | some pmI =>
      if ¬pmI.writeCaptured ∧ T < pmI.currentType v.type ∧
          isPromotionChain (pmI.promotedTypes ++ [T]) then
        modify (fun s => {
          s with promotionInfo := s.promotionInfo.insert v {pmI with promotedTypes := pmI.promotedTypes ++ [T]}})
    | none => pure ()
  | _ => pure ()

mutual

@[expose]
public def elabExprImpl (e : Expr) :
    AlgM
      (LoweredExpr × ExprModelImpl) := do
  match e with
  | .var v =>
    match (<- get).promotionInfo[v]? with
    | some pm =>
        let T := pm.currentType v.type
        pure (LoweredExpr.var v T, ⟨T, some (Key.var v), none⟩)
    | none => throw s!"Undefined variable {v.name}"
  | .nullCheck eInner =>
    let (m, emI) <- elabExprImpl eInner
    let T' := NonNull emI.type
    tryPromoteImpl emI.ref? T'
    pure (m.nullCheck, ⟨T', none, none⟩)
  | .as eInner T =>
    let (m, emI) <- elabExprImpl eInner
    tryPromoteImpl emI.ref? T
    pure (m.as T, ⟨T, none, none⟩)
  | .null =>
    pure (.null, ⟨Γ.Null, none, none⟩)

public def elabStmtImpl (s : Stmt) :
    AlgM LoweredExpr := do
  match s with
  | .declare n T =>
    modify (fun s =>
      { s with
        promotionInfo :=
          s.promotionInfo.insert ⟨n, T⟩ ⟨[], [], true, false, some ValueVersion.unspecified⟩ })
    pure (LoweredExpr.declare ⟨n, T⟩ T)
  | .exprStmt e =>
    let (m, _) <- elabExprImpl e
    pure m
  | .ifStmt e₁ s₂ s₃ =>
    let (m₁, em₁) <- elabExprImpl e₁
    -- TODO: handle dynamic
    if em₁.type != Γ.bool then throw s!"Type of {e₁} is {em₁.type}, expected bool" else
    -- TODO: make a helper function for some of this logic?
    let fm₁ <- get
    let (fm₁_true, fm₁_false) := em₁.boolInfo.getD (fm₁, fm₁)
    set fm₁_true
    let m₂ <- elabStmtImpl s₂
    let fm₂ <- get
    set fm₁_false
    let m₃ <- elabStmtImpl s₃
    let fm₃ <- get
    set (fm₂.join fm₃)
    pure (.cond m₁ m₂ m₃ Γ.Null)
  | .block stmts =>
    let loweredStmts <- elabStmtsImpl stmts
    pure (LoweredExpr.block loweredStmts)

public def elabStmtsImpl (ss : List Stmt) :
    AlgM (List LoweredExpr) := do
  match ss with
  | [] => pure []
  | s :: ss' =>
    let loweredS <- elabStmtImpl s
    let loweredSS <- elabStmtsImpl ss'
    pure (loweredS :: loweredSS)

end

end FlowAnalysis
