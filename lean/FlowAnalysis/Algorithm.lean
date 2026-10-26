module
public import Std.Data.HashMap
import FlowAnalysis.Elaboration
public import FlowAnalysis.Key.StoreImpl
public import DartLang.Lowered
public import FlowAnalysis.PromotionChain.JoinImpl
public import FlowAnalysis.PromotionModel.Impl
public import FlowAnalysis.State
public import FlowAnalysis.Syntax
public import DartLang.Types

/-!
# An algorithmic model of flow analysis

This module contains an algorithmic implementation of the flow analysis rules defined in
`FlowAnalysis.Elaboration`, written to mirror the structure of the Dart implementation
(`_FlowAnalysisImpl`) as closely as possible: it walks the syntax tree once, in a state monad
(`AlgM`) whose state holds the current flow model (`FlowModelImpl`) and the promotion key store,
and it uses the same data structures as Dart (hash maps keyed by integer promotion keys, and
promotion chains as plain lists).

Where the specification relates a program to its lowering and flow models, the algorithm computes
them, or fails with an error message for a program that flow analysis rejects.
`FlowAnalysis.AlgorithmTheorems` proves that the two agree.

This algorithm is a stepping stone: once the Dart implementation of flow analysis can be
translated to Lean and verified directly, it will be removed.
-/

open FlowAnalysis

namespace FlowAnalysis
open DartLang

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
local notation "PromotionKeyStore" => PromotionKeyStore (ℓ := ℓ)
local notation "ValueVersionImpl" => ValueVersionImpl (ℓ := ℓ)

/--
Mirrors Dart's `FlowModel`: the flow model at a point in the code, as a hash map from promotion keys
to promotion models (Dart's `promotionInfo`, there a persistent map). Related to the specification's
`FlowModel` by `FlowModelImpl.refines`.
-/
-- TODO: use a more PromotionInfo-like structure
@[ext]
public structure FlowModelImpl where
  /-- The promotion model of each location that flow analysis is tracking. -/
  promotionInfo : Std.HashMap PromotionKey PromotionModelImpl
deriving Inhabited

local notation "FlowModelImpl" => FlowModelImpl (τ := τ) (ℓ := ℓ)

/-- The flow model at the start of flow analysis, which tracks nothing. -/
@[expose]
public def FlowModelImpl.empty : FlowModelImpl := ⟨∅⟩

/--
`mergeMaps f m₁ m₂` is the map that has an entry for each key that both `m₁` and `m₂` have, whose
value is `f` applied to the two values. Used to join flow models.
-/
@[expose]
public def mergeMaps {α β : Type} [BEq α] [Hashable α]
    (f : β → β → β) (m₁ m₂ : Std.HashMap α β) : Std.HashMap α β :=
  m₁.filterMap fun k v₁ =>
    match m₂[k]? with
     | none => none
     | some v₂ => f v₁ v₂

/--
Mirrors Dart's `FlowModel.join`, minus reachability: the flow model where two control flow paths
come together. A key that only one path tracks is dropped, and each remaining key's promotion
model is the join of its two promotion models. As in Dart, if either flow model tracks nothing,
the result is that flow model, without building a new map.
-/
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
  the specification's `Reference.version?`). TODO: revisit when write capture is modelled.
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

/--
What the algorithm learns from analyzing an expression, other than its effect on the current flow
model. Mirrors the combination of the expression's static type, Dart's `_Reference` for it (if
any), and Dart's `ExpressionInfo` for it (if any).
-/
public structure ExprModelImpl where
  /-- The expression's static type. -/
  type : τ
  /-- The location the expression read, if it read one that flow analysis can promote. -/
  ref? : Option ReferenceImpl
  /--
  The flow models after the expression for when it evaluates to `true` and to `false` (Dart's
  `ExpressionInfo.ifTrue` and `ifFalse`), or `none` if both are just the current flow model after
  it.
  -/
  boolInfo : Option (FlowModelImpl × FlowModelImpl)

local notation "ExprModelImpl" => ExprModelImpl (τ := τ) (ℓ := ℓ)

/--
The context in which a node is analyzed. Unlike `AlgState`, this is passed down the syntax tree
but never back up.
-/
public structure Config where
  /--
  The AST path of the node being analyzed. Used to label the value versions the node creates, in
  place of the object identity that Dart's `ValueVersion` objects have, and to identify the variable
  that a declaration declares (see `Scope`).
  -/
  path : AstPath
  /--
  The variables in scope at the node being analyzed. Dart's flow analysis has no counterpart: its
  clients resolve names before calling it, and pass it variable elements.
  -/
  scope : Scope (τ := τ)

local notation "Config" => Config (τ := τ)

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
Dart's `promotionKeyStore.keyForVariable(variable)`, for the variable declared at `decl`.
-/
@[expose]
public def keyForVariableM (decl : ℓ) : AlgM PromotionKey :=
  modifyGet fun s =>
    let r := s.promotionKeyStore.keyForVariable decl
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
`withRest s x` runs `x` as the analysis of the rest of a statement list whose first statement is
`s`: as child `1` of the current node, in the scope extended by the variable that `s` (child `0`)
declares, if any (see `Stmt.extendScope`).
-/
@[expose]
public def withRest {α : Type} (s : Stmt) (x : AlgM α) : AlgM α :=
  withReader (fun cfg => ⟨1 :: cfg.path, s.extendScope cfg.scope (0 :: cfg.path)⟩) x

/--
Mirrors `FlowModel._finishTypeTest`: the common core of `tryMarkNonNullable` and
`tryPromoteForTypeCast`, which `is` also uses, in place of Dart's `tryPromoteForTypeCheck`.  Records
that the referent of `ref`, whose current promotion model is `pmI`, has been promoted to
`promotedType`.

The caller is responsible for having checked that the promotion is valid.

Unlike Dart's `_finishTypeTest`, this takes no `testedType`, and so never updates
`PromotionModelImpl.tested`.  The specification's `PromotionModel.tryPromote` doesn't update
`PromotionModel.tested` either, so the field is currently vestigial on both sides.

TODO: track tested types, alongside types of interest.
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
TODO: mirror Dart here; see `PromotionKeyStore.getOrCreatePropertyVersion`.
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

/--
Analyzes the expression `e`, at the AST path and in the scope given by the `Config`, starting from
the current flow model in the state. Returns the lowered expression and the expression model, and
leaves the flow model after `e` in the state; or fails, if flow analysis rejects `e`. Mirrors the
calls that Dart's analyzer and front end make into `_FlowAnalysisImpl` while visiting `e`.
-/
@[expose]
public def elabExprImpl (e : Expr) :
    AlgM
      (LoweredExpr × ExprModelImpl) := do
  match e with
  | .var n =>
    -- Resolves `n` to the innermost declaration in scope, then mirrors
    -- `_FlowAnalysisImpl.variableRead`.
    match (<- read).scope.lookup n with
    | none =>
      -- Referring to an undeclared variable is a compile-time error, which this `throw` models.
      throw s!"Undefined variable {n}"
    | some (v, decl) =>
    let k <- keyForVariableM decl
    match (<- get).current.promotionInfo[k]? with
    | some pm =>
        -- Reading a variable that isn't readable is a compile-time error: see
        -- `PromotionModel.Readable`.
        if !(pm.assigned || v.startsNull) then
          throw s!"Variable {n} is read before it is definitely assigned"
        else
        let T := pm.currentType v.type
        pure (LoweredExpr.var v T, ⟨T, some ⟨k, pm.version?.map (⟨·, []⟩)⟩, none⟩)
    | none =>
      -- Not expected for a variable in scope, which was given a promotion model when it was
      -- declared, but nothing here relies on that. As in the specification, which has no rule
      -- for this case, the read fails. Dart's `variableRead` doesn't fail here; it falls back to a
      -- fresh promotion model instead.
      throw s!"Undefined variable {n}"
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
  | .is eInner T =>
    -- Mirrors `_FlowAnalysisImpl.isExpression_end`, which promotes the referent of `eInner` to `T`
    -- when the test is `true` (`tryPromoteForTypeCheck`, here the same as for a cast), and learns
    -- nothing when it's `false`. Promotion to a factor type when it's `false` isn't modeled yet.
    let (m, emI) <- withChild 0 (elabExprImpl eInner)
    let fmI := (<- get).current
    let fmI_true :=
      match emI.ref? with
      | some ref => fmI.tryPromoteForTypeCast ref emI.type T
      | none => fmI
    setCurrent (fmI_true.join fmI)
    pure (m.is T, ⟨Γ.bool, none, some (fmI_true, fmI)⟩)
  | .null =>
    pure (.null, ⟨Γ.Null, none, none⟩)
  | .assign n e₁ =>
    -- Mirrors `_FlowAnalysisImpl.write`, after the right-hand side has been analyzed.
    let (m₁, emI₁) <- withChild 0 (elabExprImpl e₁)
    let cfg <- read
    match cfg.scope.lookup n with
    | none => throw s!"Undefined variable {n}"
    | some (v, decl) =>
    -- TODO: when dynamic downcasts are supported, an assignment whose right-hand side has type
    -- `dynamic` will have to be accepted (with an implicit downcast), so this check will change.
    if !(decide (emI₁.type ≤ v.type)) then
      throw s!"Type of {e₁} is {emI₁.type}, expected a subtype of {v.type}"
    else
    let k <- keyForVariableM decl
    match (<- get).current.promotionInfo[k]? with
    | some pmI =>
      -- Assigning to a `final` variable that isn't definitely unassigned (after the right-hand
      -- side, which runs first) is a compile-time error.
      if v.isFinal && !pmI.unassigned then
        throw s!"Final variable {n} is assigned when it isn't definitely unassigned"
      else
      -- The new value version mirrors the `new ValueVersion()` in Dart's `write`.
      modifyCurrent fun fmI =>
        ⟨fmI.promotionInfo.insert k (pmI.write emI₁.type (ValueVersion.root cfg.path))⟩
      pure (.variableSet v m₁, ⟨emI₁.type, none, none⟩)
    | none => throw s!"Undefined variable {n}"

/--
Analyzes the statement `s`, like `elabExprImpl`: returns its lowering, and leaves the flow model
after `s` in the state; or fails, if flow analysis rejects `s`.
-/
public def elabStmtImpl (s : Stmt) :
    AlgM LoweredExpr := do
  match s with
  | .declare n T isFinal =>
    -- Mirrors `_FlowAnalysisImpl.declare`, whose `new ValueVersion()` is modelled by the root
    -- labelled by this declaration's AST path. The same path identifies the variable (see `Scope`).
    let π := (<- read).path
    let k <- keyForVariableM π
    modifyCurrent fun fmI =>
      ⟨fmI.promotionInfo.insert k ⟨[], [], false, true, some (ValueVersion.root π)⟩⟩
    pure (LoweredExpr.declare ⟨n, T, isFinal⟩ T (Variable.startsNull ⟨n, T, isFinal⟩))
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
    pure (.cond m₁ (.block [m₂]) (.block [m₃]) Γ.Null)
  | .block stmts =>
    let loweredStmts <- withChild 0 (elabStmtsImpl stmts)
    pure (LoweredExpr.block loweredStmts)

/--
Analyzes the statement list `ss` in order, like `elabStmtImpl`, extending the scope with each
statement's declaration (if any) for the statements after it. Returns the lowered statements.
-/
public def elabStmtsImpl (ss : List Stmt) :
    AlgM (List LoweredExpr) := do
  match ss with
  | [] => pure []
  | s :: ss' =>
    let loweredS <- withChild 0 (elabStmtImpl s)
    let loweredSS <- withRest s (elabStmtsImpl ss')
    pure (loweredS :: loweredSS)

end

end FlowAnalysis
