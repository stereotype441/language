/-
This module contains an algorithmic implementation of the flow analysis rules defined in
`FlowAnalysis.Elaboration`.
-/

module
public import Std.Data.HashMap
import FlowAnalysis.Elaboration
public import FlowAnalysis.Key.StoreImpl
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
local notation "Stmt" => Stmt (τ := τ)
local notation "Variable" => Variable (τ := τ)

section
variable {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ) (ℓ := ℓ)
local notation "PromotionKeyStore" => PromotionKeyStore (τ := τ) (ℓ := ℓ)

/-- Not exposed so that proofs can't rely on it -/
public def unspecifiedPromotionChain : List τ := []

-- TODO: use a more PromotionInfo-like structure
@[ext]
public structure FlowModelImpl where
  promotionInfo : Std.HashMap PromotionKey PromotionModelImpl
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
  ref? : Option PromotionKey
  boolInfo : Option (FlowModelImpl × FlowModelImpl)

local notation "ExprModelImpl" => ExprModelImpl (τ := τ) (ℓ := ℓ)

/--
The context in which a node is analyzed. Unlike `AlgState`, this is passed down the syntax tree
but never back up.
-/
public structure Config where
  /--
  The AST path of the node being analyzed. Used to label the value versions the node creates, in
  place of the object identity that Dart's `ValueVersion` objects have.
  -/
  path : AstPath

/--
Models the mutable state of Dart's `_FlowAnalysisImpl`, as far as it is modelled so far.
-/
public structure AlgState where
  /-- Mirrors `_FlowAnalysisImpl._current`: the flow model at the current point in the code. -/
  current : FlowModelImpl
  /--
  Mirrors `_FlowAnalysisImpl.promotionKeyStore`.

  Unlike `current`, this is never saved and restored as the analysis moves between branches: keys
  are allocated once for the whole analysis, so a key allocated while analyzing one branch still
  stands for the same thing when it turns up in another.
  -/
  promotionKeyStore : PromotionKeyStore

local notation "AlgState" => AlgState (τ := τ) (ℓ := ℓ)

/-- The state at the start of flow analysis. -/
@[expose]
public def AlgState.initial : AlgState := ⟨FlowModelImpl.empty, PromotionKeyStore.empty⟩

/--
Elaboration algorithms are defined using a state monad that records the current flow analysis
state. This state is updated as we recursively traverse the code being analyzed.
-/
public abbrev AlgM :=
  ReaderT Config (StateT AlgState (ExceptT String Id))

local notation "AlgM" => AlgM (τ := τ) (ℓ := ℓ)

/--
Monadic form of `PromotionKeyStore.keyForVariable`, updating the key store in the state.  Mirrors
Dart's `promotionKeyStore.keyForVariable(variable)`.
-/
@[expose]
public def keyForVariableM (v : Variable) : AlgM PromotionKey :=
  modifyGet fun s =>
    let r := s.promotionKeyStore.keyForVariable v
    (r.1, { s with promotionKeyStore := r.2 })

/-- Mirrors `_FlowAnalysisImpl._current = fmI`. -/
@[expose]
public def setCurrent (fmI : FlowModelImpl) : AlgM Unit :=
  modify fun s => { s with current := fmI }

/-- Mirrors `_FlowAnalysisImpl._current = f(_current)`. -/
@[expose]
public def modifyCurrent (f : FlowModelImpl → FlowModelImpl) : AlgM Unit :=
  modify fun s => { s with current := f s.current }

/--
`withChild i x` runs `x` as the analysis of child `i` of the current node, by prepending `i` to the
AST path in the `Config`. See `AstPath` for how children are numbered.
-/
@[expose]
public def withChild {α : Type} (i : Nat) (x : AlgM α) : AlgM α :=
  withReader (fun cfg => { cfg with path := i :: cfg.path }) x

/--
Mirrors `FlowModel._finishTypeTest`: the common core of `tryMarkNonNullable` and
`tryPromoteForTypeCast` (and, once `is` is modelled, `tryPromoteForTypeCheck`).  Records that
the referent of `ref`, whose current promotion model is `pmI`, has been promoted to `promotedType`.

The caller is responsible for having checked that the promotion is valid.

Unlike Dart's `_finishTypeTest`, this takes no `testedType`, and so never updates
`PromotionModelImpl.tested`.  The specification's `PromotionModel.tryPromote` doesn't update
`PromotionModel.tested` either, so the field is currently vestigial on both sides.

TODO(stage 6): track tested types, alongside types of interest.
-/
@[expose]
public def FlowModelImpl.finishTypeTest (fmI : FlowModelImpl) (ref : PromotionKey)
    (pmI : PromotionModelImpl) (promotedType : τ) : FlowModelImpl :=
  ⟨fmI.promotionInfo.insert ref { pmI with promotedTypes := pmI.promotedTypes ++ [promotedType] }⟩

/--
Mirrors `FlowModel.tryMarkNonNullable`: the effect on the flow model of learning that the referent
of `ref`, whose static type is `previousType`, is not `null`.

Dart's version returns an `ExpressionInfo`, whose `ifFalse` model is the unchanged flow model.
Every construct modelled so far uses only the `ifTrue` model, so that is all this returns.

If `ref` has no promotion model, this returns `fmI` unchanged. That departs from Dart, which
obtains the promotion model via `infoFor`, and so creates
`PromotionModel.fresh(version: reference.version)` when there isn't one, and then promotes it. The
`none` branch is currently unreachable: `ref` can only come from the `var` case of `elabExprImpl`,
which throws unless the variable has a promotion model, and a variable read doesn't change the flow
model. The specification's `FlowModel.tryPromote` has the same `none` branch, so refinement is
unaffected.

TODO(stage 4): in the `none` branch, create a fresh promotion model at the reference's value
version (as Dart's `infoFor` does) and promote that. The first promotion of a property reaches
this branch.
-/
@[expose]
public def FlowModelImpl.tryMarkNonNullable (fmI : FlowModelImpl) (ref : PromotionKey)
    (previousType : τ) : FlowModelImpl :=
  match fmI.promotionInfo[ref]? with
  | none => fmI
  | some pmI =>
    if pmI.writeCaptured then fmI else
    let newType := NonNull previousType
    if newType < previousType ∧ isPromotionChain (pmI.promotedTypes ++ [newType]) then
      fmI.finishTypeTest ref pmI newType
    else
      fmI

/--
Mirrors `FlowModel.tryPromoteForTypeCast`: the effect on the flow model of casting the referent of
`ref`, whose static type is `previousType`, to `T`.

If `ref` has no promotion model, this returns `fmI` unchanged. As with `tryMarkNonNullable`, that
departs from Dart's `infoFor`, which creates `PromotionModel.fresh(version: reference.version)`,
but the branch is currently unreachable, because the `var` case of `elabExprImpl` throws unless
the variable has a promotion model.

TODO(stage 4): in the `none` branch, create a fresh promotion model at the reference's value
version and promote that.
-/
@[expose]
public def FlowModelImpl.tryPromoteForTypeCast (fmI : FlowModelImpl) (ref : PromotionKey)
    (previousType T : τ) : FlowModelImpl :=
  match fmI.promotionInfo[ref]? with
  | none => fmI
  | some pmI =>
    if pmI.writeCaptured then fmI else
    let newType := T
    if newType < previousType ∧ isPromotionChain (pmI.promotedTypes ++ [newType]) then
      fmI.finishTypeTest ref pmI newType
    else
      fmI

end

/-
The elaboration functions label the value versions they create by AST paths, so from here on labels
are `AstPath`s.
-/

local notation "AlgM" => AlgM (τ := τ) (ℓ := AstPath)
local notation "ExprModelImpl" => ExprModelImpl (τ := τ) (ℓ := AstPath)

mutual

@[expose]
public def elabExprImpl (e : Expr) :
    AlgM
      (LoweredExpr × ExprModelImpl) := do
  match e with
  | .var v =>
    -- Mirrors `_FlowAnalysisImpl.variableRead`.
    let k <- keyForVariableM v
    match (<- get).current.promotionInfo[k]? with
    | some pm =>
        let T := pm.currentType v.type
        pure (LoweredExpr.var v T, ⟨T, some k, none⟩)
    | none =>
      -- Referring to an undeclared variable is a compile-time error, which this `throw` models.
      -- It is intended to stay, though it may move out of the flow analysis part of the model once
      -- elaboration covers name resolution. Dart's `variableRead` doesn't fail here; it falls back
      -- to a fresh promotion model instead. This `throw` is what makes the `none` branches of
      -- `FlowModelImpl.tryMarkNonNullable` and `FlowModelImpl.tryPromoteForTypeCast` unreachable.
      throw s!"Undefined variable {v.name}"
  | .nullCheck eInner =>
    let (m, emI) <- withChild 0 (elabExprImpl eInner)
    modifyCurrent fun fmI =>
      match emI.ref? with
      | some ref => fmI.tryMarkNonNullable ref emI.type
      | none => fmI
    pure (m.nullCheck, ⟨NonNull emI.type, none, none⟩)
  | .as eInner T =>
    let (m, emI) <- withChild 0 (elabExprImpl eInner)
    modifyCurrent fun fmI =>
      match emI.ref? with
      | some ref => fmI.tryPromoteForTypeCast ref emI.type T
      | none => fmI
    pure (m.as T, ⟨T, none, none⟩)
  | .null =>
    pure (.null, ⟨Γ.Null, none, none⟩)

public def elabStmtImpl (s : Stmt) :
    AlgM LoweredExpr := do
  match s with
  | .declare n T =>
    -- Mirrors `_FlowAnalysisImpl.declare`, whose `new ValueVersion()` is modelled by the root
    -- labelled by this declaration's AST path.
    let k <- keyForVariableM ⟨n, T⟩
    let π := (<- read).path
    modifyCurrent fun fmI =>
      ⟨fmI.promotionInfo.insert k ⟨[], [], true, false, some (ValueVersion.root π)⟩⟩
    pure (LoweredExpr.declare ⟨n, T⟩ T)
  | .exprStmt e =>
    let (m, _) <- withChild 0 (elabExprImpl e)
    pure m
  | .ifStmt e₁ s₂ s₃ =>
    let (m₁, em₁) <- withChild 0 (elabExprImpl e₁)
    -- TODO: handle dynamic
    if em₁.type != Γ.bool then throw s!"Type of {e₁} is {em₁.type}, expected bool" else
    -- TODO: make a helper function for some of this logic?
    let fm₁ := (<- get).current
    let (fm₁_true, fm₁_false) := em₁.boolInfo.getD (fm₁, fm₁)
    setCurrent fm₁_true
    let m₂ <- withChild 1 (elabStmtImpl s₂)
    let fm₂ := (<- get).current
    -- Only the flow model is restored here; keys allocated while analyzing `s₂` stay allocated.
    setCurrent fm₁_false
    let m₃ <- withChild 2 (elabStmtImpl s₃)
    let fm₃ := (<- get).current
    setCurrent (fm₂.join fm₃)
    pure (.cond m₁ m₂ m₃ Γ.Null)
  | .block stmts =>
    let loweredStmts <- withChild 0 (elabStmtsImpl stmts)
    pure (LoweredExpr.block loweredStmts)

public def elabStmtsImpl (ss : List Stmt) :
    AlgM (List LoweredExpr) := do
  match ss with
  | [] => pure []
  | s :: ss' =>
    let loweredS <- withChild 0 (elabStmtImpl s)
    let loweredSS <- withChild 1 (elabStmtsImpl ss')
    pure (loweredS :: loweredSS)

end

end FlowAnalysis
