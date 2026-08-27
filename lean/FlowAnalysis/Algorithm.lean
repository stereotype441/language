/-
This module contains an algorithmic implementation of the flow analysis rules defined in
`FlowAnalysis.Elaboration`.
-/

module
public import Std.Data.HashMap
import FlowAnalysis.Elaboration
public import FlowAnalysis.Lowered
public import FlowAnalysis.State
public import FlowAnalysis.Syntax
public import FlowAnalysis.Types

open FlowAnalysis

namespace FlowAnalysis

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "Expr" => Expr (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Reference" => Reference (τ := τ)
local notation "Stmt" => Stmt (τ := τ)
local notation "Variable" => Variable (τ := τ)

public structure ValueModelA where
  promotedTypes : List τ

local notation "ValueModelA" => ValueModelA (τ := τ)

/--
If `a?` is `some a`, returns the value `a`. Otherwise throws an exception.
-/
@[expose]
public def _root_.Option.assert {m α} [Monad m] [MonadExcept String m] (a? : Option α) : m α :=
  match a? with
    | none => throw "No value"
    | some a => pure a

@[expose]
public def joinPromotedTypesA' {m} [Monad m] [MonadExcept String m] (ts₁ ts₂ : List τ) :
    m (List τ) := do
  let mut i₁ := 0
  let mut i₂ := 0
  let mut T₁ ← ts₁[0]?.assert
  let mut T₂ ← ts₂[0]?.assert
  let mut result : Option (List τ) := none
  repeat do
    let mut advance_i₁ : Option Bool := none
    let mut advance_i₂ : Option Bool := none
    if T₁ = T₂ then
      result := result.map (· ++ [T₁])
      advance_i₁ := true
      advance_i₂ := true
    else if T₁ ≤ T₂ then
      advance_i₁ := false
      advance_i₂ := true
    else
      result := result.getD (ts₁.take i₁)
      advance_i₁ := true
      advance_i₂ := false
    if ←advance_i₁.assert then
      i₁ := i₁ + 1
      if i₁ = ts₁.length then
        if result ≠ none then return ←result.assert
        return ts₁
      T₁ ← ts₁[i₁]?.assert
    if ←advance_i₂.assert then
      i₂ := i₂ + 1
      if i₂ = ts₂.length then
        if result ≠ none then return ←result.assert
        if i₁ = ts₁.length then return ts₁
        return ts₁.take i₁
      T₂ ← ts₂[i₂]?.assert

@[expose]
public def joinPromotedTypesA {m} [Monad m] [MonadExcept String m] (ts₁ ts₂ : List τ) :
    m (List τ) := do
  let mut ts₁ := ts₁
  let mut ts₂ := ts₂
  if ts₁ = [] then return ts₁
  if ts₂ = [] then return ts₂
  if ts₁.length > ts₂.length then
    let tmp := ts₁
    ts₁ := ts₂
    ts₂ := tmp
  joinPromotedTypesA' ts₁ ts₂

/-- Not exposed so that proofs can't rely on it -/
public def unspecifiedPromotionChain : List τ := []

@[expose]
public def ValueModelA.join (vmA₁ vmA₂ : ValueModelA) : ValueModelA :=
  match (joinPromotedTypesA vmA₁.promotedTypes vmA₂.promotedTypes : ExceptT String Id _).run with
    | .ok ts => ⟨ts⟩
    | .error _ => ⟨unspecifiedPromotionChain⟩

@[expose]
public def ValueModelA.promotedType? (vmA : ValueModelA) : Option τ :=
  vmA.promotedTypes.getLast?

@[expose]
public def ValueModelA.currentType (vmA : ValueModelA) (baseType : τ) :
    τ :=
  match vmA.promotedType? with
  | none => baseType
  | some T => if T ≤ baseType then T else baseType

-- TODO: use a more PromotionInfo-like structure
public structure FlowModelA where
  env : Std.HashMap Variable ValueModelA
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
  ⟨mergeMaps ValueModelA.join fmA₁.env fmA₂.env⟩

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
    | some vmA =>
      if T < vmA.currentType v.type then
        modify (fun s => { s with env := s.env.insert v ⟨[T]⟩})
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
    modify (fun s => { s with env := s.env.insert ⟨n, T⟩ ⟨[]⟩ })
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
