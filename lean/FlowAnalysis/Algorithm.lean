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
local notation "Property" => Property (τ := τ)
local notation "Stmt" => Stmt (τ := τ)
local notation "Variable" => Variable (τ := τ)

section
variable {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ) (ℓ := ℓ)
local notation "PromotionKeyStore" => PromotionKeyStore (τ := τ) (ℓ := ℓ)
local notation "ValueVersionImpl" => ValueVersionImpl (ℓ := ℓ)

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

/--
Mirrors Dart's `_Reference`: what flow analysis knows about the location that an expression read,
so that the location can be promoted when the expression's value is.

Dart's `_Reference` also records the static type of the read, and (for why-not-promoted) whether
the location is promotable; here the static type is `ExprModelImpl.type`, and only promotable
locations get references.
-/
public structure ReferenceImpl where
  /-- The promotion key of the location that was read. -/
  promotionKey : PromotionKey
  /--
  The version of the value that was read.

  `none` only for a write-captured variable, where Dart instead uses a fresh `ValueVersion` (see
  the specification's `Reference.version?`). TODO(stage 7): revisit when write capture is modelled.
  -/
  version? : Option ValueVersionImpl

local notation "ReferenceImpl" => ReferenceImpl (ℓ := ℓ)

/--
`fmI.infoFor r` is the promotion model of the location that `r` refers to: the one `fmI` stores
under `r.promotionKey` if there is one, and otherwise a fresh promotion model holding the version
that was read. Mirrors Dart's `FlowModel.infoFor`.

As in the specification's `FlowModel.infoFor`, the result is `none` only if there is no stored model
and `r` has no version, which happens only for a write-captured variable.
-/
@[expose]
public def FlowModelImpl.infoFor (fmI : FlowModelImpl) (r : ReferenceImpl) :
    Option PromotionModelImpl :=
  match fmI.promotionInfo[r.promotionKey]? with
  | some pmI => some pmI
  | none => r.version?.map fun v => PromotionModelImpl.fresh v.roots

public structure ExprModelImpl where
  type : τ
  ref? : Option ReferenceImpl
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

As in Dart, the promotion model to promote is obtained with `infoFor`, so the first promotion of a
property starts from a fresh model. `infoFor` returns `none` only for a write-captured variable,
which wouldn't be promoted anyway.
-/
@[expose]
public def FlowModelImpl.tryMarkNonNullable (fmI : FlowModelImpl) (ref : ReferenceImpl)
    (previousType : τ) : FlowModelImpl :=
  match fmI.infoFor ref with
  | none => fmI
  | some pmI =>
    if pmI.writeCaptured then fmI else
    let newType := NonNull previousType
    if newType < previousType ∧ isPromotionChain (pmI.promotedTypes ++ [newType]) then
      fmI.finishTypeTest ref.promotionKey pmI newType
    else
      fmI

/--
Mirrors `FlowModel.tryPromoteForTypeCast`: the effect on the flow model of casting the referent of
`ref`, whose static type is `previousType`, to `T`.

As with `tryMarkNonNullable`, the promotion model to promote is obtained with `infoFor`.
-/
@[expose]
public def FlowModelImpl.tryPromoteForTypeCast (fmI : FlowModelImpl) (ref : ReferenceImpl)
    (previousType T : τ) : FlowModelImpl :=
  match fmI.infoFor ref with
  | none => fmI
  | some pmI =>
    if pmI.writeCaptured then fmI else
    let newType := T
    if newType < previousType ∧ isPromotionChain (pmI.promotedTypes ++ [newType]) then
      fmI.finishTypeTest ref.promotionKey pmI newType
    else
      fmI

/--
Monadic form of `PromotionKeyStore.getOrCreatePropertyVersion`, updating the key store in the
state.  Mirrors Dart's `target.getOrCreatePropertyVersion(...)` for a promotable property.
-/
@[expose]
public def getOrCreatePropertyVersionM (target : ValueVersionImpl) (name : String) :
    AlgM PromotionKey :=
  modifyGet fun s =>
    let r := s.promotionKeyStore.getOrCreatePropertyVersion target name
    (r.1, { s with promotionKeyStore := r.2 })

/--
Mirrors Dart's `_handleProperty`: given the reference (if any) produced by the target of a read of
property `p`, returns the type of the read and the reference (if any) to the property.

If the target's value is tracked and `p` is promotable, the property's key is looked up (and
allocated, on a miss) in the target version's `_promotableProperties`, and the type is the
property's promoted type in the current flow model, if any. The flow model itself is unchanged: as
in Dart, the read only looks up the property's promotion model, and doesn't create one.

Otherwise the read has the declared type of `p` and no reference. This departs from Dart, which
allocates a fresh key for every read of a non-promotable property, and returns a reference to it.
TODO(stage 7): mirror Dart here; see `PromotionKeyStore.getOrCreatePropertyVersion`.
-/
@[expose]
public def handlePropertyM (target? : Option ReferenceImpl) (p : Property) :
    AlgM (τ × Option ReferenceImpl) := do
  match target?.bind (·.version?), p.isPromotable with
  | some target, true =>
    let k <- getOrCreatePropertyVersionM target p.name
    let T := ((<- get).current.promotionInfo[k]?).elim p.type (·.currentType p.type)
    pure (T, some ⟨k, some ⟨target.roots, target.path ++ [p.name]⟩⟩)
  | _, _ => pure (p.type, none)

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
        pure (LoweredExpr.var v T, ⟨T, some ⟨k, pm.version?.map (⟨·, []⟩)⟩, none⟩)
    | none =>
      -- Referring to an undeclared variable is a compile-time error, which this `throw` models.
      -- It is intended to stay, though it may move out of the flow analysis part of the model once
      -- elaboration covers name resolution. Dart's `variableRead` doesn't fail here; it falls back
      -- to a fresh promotion model instead.
      throw s!"Undefined variable {v.name}"
  | .property eInner p =>
    -- Mirrors `_FlowAnalysisImpl.propertyGet`.
    let (m, emI) <- withChild 0 (elabExprImpl eInner)
    let (T, ref?) <- handlePropertyM emI.ref? p
    pure (m.propertyGet p T, ⟨T, ref?, none⟩)
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
