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
and it uses the same data structures as Dart (hash maps keyed by integer promotion keys, promotion
chains as plain lists, and value versions with their own identity).

In particular, like Dart, and unlike the specification, the algorithm names a property by the
value version of its target rather than by its root variable: a property's promotion key is found
in the property map of the version it was read from (`handlePropertyM`). So assigning a variable,
which gives it a new version, makes the promotions of its old value's properties unreachable,
without erasing them. And joining two flow models in which a variable holds different versions
gives it a new version, whose properties are re-keyed, as Dart's `ValueVersion._joinProperties`
does (`joinProperties`).

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
local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ)

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

local notation "FlowModelImpl" => FlowModelImpl (τ := τ)

/-- The flow model at the start of flow analysis, which tracks nothing. -/
@[expose]
public def FlowModelImpl.empty : FlowModelImpl := ⟨∅⟩

section
variable {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionKeyStore" => PromotionKeyStore (ℓ := ℓ)

/--
The promotion model, if any, of the joined property whose version is `c`, given that the property
versions on the two control flow paths being joined, whose flow models are `fmI₁` and `fmI₂`, are
`p₁` and `p₂`. Mirrors the part of Dart's `ValueVersion._joinProperties` that joins the property's
promotion models: if the property has a promotion model along both paths, it might be promoted, so
the result is their join, by Dart's `PromotionModel.join` with `propertyVersion: c`, which never
joins value versions, and so is just `PromotionModelImpl.joinWith`. Otherwise the result is `none`.
-/
@[expose]
public def joinPropertyModels (fmI₁ fmI₂ : FlowModelImpl) (p₁ p₂ : PropertyValueVersionImpl)
    (c : ValueVersionImpl) : Option PromotionModelImpl :=
  match fmI₁.promotionInfo[p₁.promotionKey]?, fmI₂.promotionInfo[p₂.promotionKey]? with
  | some pmI₁, some pmI₂ =>
    some (pmI₁.joinWith pmI₂ (if pmI₁.writeCaptured || pmI₂.writeCaptured then none else some c))
  | _, _ => none

/--
One iteration of the loop in Dart's `ValueVersion._joinProperties` (see `joinProperties`), for the
property `entry.1`, whose version on the first control flow path is `entry.2`: if the second path
also has the property (in `second`, the property map of its version), the new version `v` gets a
property version with a fresh promotion key; the joined promotion model, if any
(`joinPropertyModels`), is stored under the new key in the flow model being built for the join
point (the first component of the state `st`); and the properties of the property are joined, by
`recurse`.
-/
@[expose]
public def joinPropertiesStep (fmI₁ fmI₂ : FlowModelImpl)
    (recurse : ValueVersionImpl → ValueVersionImpl → ValueVersionImpl →
      FlowModelImpl × PromotionKeyStore → FlowModelImpl × PromotionKeyStore)
    (v : ValueVersionImpl) (second : Std.HashMap String PropertyValueVersionImpl)
    (st : FlowModelImpl × PromotionKeyStore) (entry : String × PropertyValueVersionImpl) :
    FlowModelImpl × PromotionKeyStore :=
  match second[entry.1]? with
  | none => st
  | some p₂ =>
    let r := st.2.addPropertyVersion v entry.1
    let acc :=
      match joinPropertyModels fmI₁ fmI₂ entry.2 p₂ r.1.version with
      | some pmI => ⟨st.1.promotionInfo.insert r.1.promotionKey pmI⟩
      | none => st.1
    recurse r.1.version entry.2.version p₂.version (acc, r.2)

/--
Mirrors Dart's `ValueVersion._joinProperties`, called on the new version `v` that joins versions
`v₁` and `v₂`, which are held on the two control flow paths whose flow models are `fmI₁` and `fmI₂`.

For each property that both `v₁` and `v₂` have, it gives `v` a property version with a fresh
promotion key; if the property has a promotion model on both paths, it stores their join under the
new key, in the flow model being built for the join point (the first component of the state); and
then it joins the properties of the property, recursively (`joinPropertiesStep`). A property that
only one of `v₁` and `v₂` has is dropped, along with its properties: along the other path, it has
never been read.

`fuel` bounds the depth of the recursion. Dart needs no such bound: its recursion terminates because
the property maps are finite trees. Here that follows from the well-formedness of the key store (a
property's version is newer than its target's), which the definition can't see, so the caller
passes a bound that is never reached (see `joinVersions`).
-/
@[expose]
public def joinProperties (fmI₁ fmI₂ : FlowModelImpl) :
    Nat → ValueVersionImpl → ValueVersionImpl → ValueVersionImpl →
      FlowModelImpl × PromotionKeyStore → FlowModelImpl × PromotionKeyStore
  | 0, _, _, _, st => st
  | fuel + 1, v, v₁, v₂, st =>
    (st.2.promotableProperties v₁).toList.foldl
      (joinPropertiesStep fmI₁ fmI₂ (joinProperties fmI₁ fmI₂ fuel) v
        (st.2.promotableProperties v₂))
      st

/--
Mirrors Dart's `ValueVersion._join`: the value version at a point where two control flow paths, on
which a location holds versions `v₁` and `v₂`, come together. If they're the same version, it's
kept. Otherwise a new version is allocated, and the properties of the two versions are joined
(`joinProperties`), updating the flow model being built for the join point and the key store (the
state `st`).

The new version is the last one allocated, so every version reachable from `v₁` through the property
maps is older (by the well-formedness of the key store), and the recursion of `joinProperties` is
at most `ks.nextVersion` deep.
-/
@[expose]
public def joinVersions (fmI₁ fmI₂ : FlowModelImpl) (v₁ v₂ : ValueVersionImpl)
    (st : FlowModelImpl × PromotionKeyStore) :
    ValueVersionImpl × (FlowModelImpl × PromotionKeyStore) :=
  if v₁ = v₂ then (v₁, st) else
  let r := st.2.newVersion
  (r.1, joinProperties fmI₁ fmI₂ r.2.nextVersion r.1 v₁ v₂ (st.1, r.2))

/--
Mirrors Dart's `PromotionModel.join`, for a variable: the promotion model where two control flow
paths, on which the variable's promotion models are `pmI₁` and `pmI₂`, come together. If the
variable is write captured on either path, so is the joined model; otherwise its version is the join
of the two versions (`joinVersions`), which may update the flow model being built for the join point
and the key store (the state `st`).
-/
@[expose]
public def PromotionModelImpl.join (fmI₁ fmI₂ : FlowModelImpl) (pmI₁ pmI₂ : PromotionModelImpl)
    (st : FlowModelImpl × PromotionKeyStore) :
    PromotionModelImpl × (FlowModelImpl × PromotionKeyStore) :=
  match pmI₁.version?, pmI₂.version? with
  | some v₁, some v₂ =>
    let r := joinVersions fmI₁ fmI₂ v₁ v₂ st
    (pmI₁.joinWith pmI₂ (some r.1), r.2)
  | _, _ => (pmI₁.joinWith pmI₂ none, st)

/--
One iteration of the loop in Dart's `FlowModel.joinPromotionInfo` (see `FlowModelImpl.join`), for
the key `entry.1`, whose promotion model in `fmI₁` is `entry.2`: if `fmI₂` also has a promotion
model for the key, their join (`PromotionModelImpl.join`) is stored under the key in the flow model
being built for the join point (the first component of the state `st`).
-/
@[expose]
public def FlowModelImpl.joinStep (fmI₁ fmI₂ : FlowModelImpl)
    (st : FlowModelImpl × PromotionKeyStore) (entry : PromotionKey × PromotionModelImpl) :
    FlowModelImpl × PromotionKeyStore :=
  match fmI₂.promotionInfo[entry.1]? with
  | none => st
  | some pmI₂ =>
    let r := PromotionModelImpl.join fmI₁ fmI₂ entry.2 pmI₂ st
    (⟨r.2.1.promotionInfo.insert entry.1 r.1⟩, r.2.2)

/--
Mirrors Dart's `FlowModel.join`, minus reachability: the flow model where two control flow paths
come together, and the key store, which joining may extend. A key that only one path tracks is
dropped, and each remaining key's promotion model is the join of its two promotion models
(`PromotionModelImpl.join`), which also gives the joined model's properties their promotion models,
under new keys. As in Dart, if either flow model tracks nothing, the result is that flow model,
without building a new map.

Dart's `joinPromotionInfo` only visits the keys whose promotion models differ between the two flow
models, keeping the others from their common ancestor. Joining a promotion model with itself gives
the same model, so visiting every key, as here, gives the same flow model.
-/
@[expose]
public def FlowModelImpl.join (fmI₁ fmI₂ : FlowModelImpl) (ks : PromotionKeyStore) :
    FlowModelImpl × PromotionKeyStore :=
  -- TODO: reachability
  -- TODO: identical check
  if fmI₁.promotionInfo.isEmpty then (fmI₁, ks) else
  if fmI₂.promotionInfo.isEmpty then (fmI₂, ks) else
  fmI₁.promotionInfo.toList.foldl (FlowModelImpl.joinStep fmI₁ fmI₂) (FlowModelImpl.empty, ks)

end

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
  the specification's `Reference.var`). TODO: revisit when write capture is modelled.
  -/
  version? : Option ValueVersionImpl

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
  | none => r.version?.map PromotionModelImpl.fresh

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

local notation "ExprModelImpl" => ExprModelImpl (τ := τ)

/--
The context in which a node is analyzed. Unlike `AlgState`, this is passed down the syntax tree
but never back up.
-/
public structure Config where
  /--
  The AST path of the node being analyzed. Used to identify the variable that a declaration
  declares (see `Scope`).
  -/
  path : AstPath
  /--
  The variables in scope at the node being analyzed. Dart's flow analysis has no counterpart: its
  clients resolve names before calling it, and pass it variable elements.
  -/
  scope : Scope (τ := τ)

local notation "Config" => Config (τ := τ)

section
variable {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionKeyStore" => PromotionKeyStore (ℓ := ℓ)

/--
Models the mutable state of Dart's `_FlowAnalysisImpl`, as far as it is modelled so far.
-/
public structure AlgState where
  /-- Mirrors `_FlowAnalysisImpl._current`: the flow model at the current point in the code. -/
  current : FlowModelImpl
  /--
  Mirrors `_FlowAnalysisImpl.promotionKeyStore`, together with the allocation state of value
  versions and their property maps.

  Unlike `current`, this is never saved and restored as the analysis moves between branches: keys
  and versions are allocated once for the whole analysis, so a key allocated while analyzing one
  branch still stands for the same thing when it turns up in another.
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

/--
Monadic form of `PromotionKeyStore.newVersion`, updating the key store in the state.  Mirrors
Dart's `new ValueVersion()`.
-/
@[expose]
public def newVersionM : AlgM ValueVersionImpl :=
  modifyGet fun s =>
    let r := s.promotionKeyStore.newVersion
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
Monadic form of `FlowModelImpl.join`, updating the key store in the state. Mirrors Dart's
`FlowModel.join(this, fmI₁, fmI₂)`.
-/
@[expose]
public def joinM (fmI₁ fmI₂ : FlowModelImpl) : AlgM FlowModelImpl :=
  modifyGet fun s =>
    let r := fmI₁.join fmI₂ s.promotionKeyStore
    (r.1, { s with promotionKeyStore := r.2 })

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
    AlgM PropertyValueVersionImpl :=
  modifyGet fun s =>
    let r := s.promotionKeyStore.getOrCreatePropertyVersion target name
    (r.1, { s with promotionKeyStore := r.2 })

/--
Mirrors Dart's `_handleProperty`: given the reference (if any) produced by the target of a read of
property `p`, returns the type of the read and the reference (if any) to the property.

If the target's value is tracked and `p` is promotable, the property's version (and with it, its
key) is looked up (and allocated, on a miss) in the target version's `_promotableProperties`, and
the type is the property's promoted type in the current flow model, if any. The flow model itself
is unchanged: as in Dart, the read only looks up the property's promotion model, and doesn't
create one.

Otherwise the read has the declared type of `p` and no reference. This departs from Dart, which
allocates a fresh key for every read of a non-promotable property, and returns a reference to it.
TODO: mirror Dart here; see `PromotionKeyStore.getOrCreatePropertyVersion`.
-/
@[expose]
public def handlePropertyM (target? : Option ReferenceImpl) (p : Property) :
    AlgM (τ × Option ReferenceImpl) := do
  match target?.bind (·.version?), p.isPromotable with
  | some target, true =>
    let pv <- getOrCreatePropertyVersionM target p.name
    let T := ((<- get).current.promotionInfo[pv.promotionKey]?).elim p.type
      (·.currentType p.type)
    pure (T, some ⟨pv.promotionKey, some pv.version⟩)
  | _, _ => pure (p.type, none)

end

/-
From here on, labels are `AstPath`s: the elaboration functions identify each variable by the AST
path of its declaration (see `Scope`).
-/

local notation "AlgM" => AlgM (τ := τ) (ℓ := AstPath)

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
        pure (LoweredExpr.var v T, ⟨T, some ⟨k, pm.version?⟩, none⟩)
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
    setCurrent (<- joinM fmI_true fmI)
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
      -- Mirrors the `new ValueVersion()` in Dart's `write`. The promotions of the old value's
      -- properties stay in the flow model, under keys that are no longer reachable from `v`.
      let newVersion <- newVersionM
      modifyCurrent fun fmI =>
        ⟨fmI.promotionInfo.insert k (pmI.write emI₁.type newVersion)⟩
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
    -- Mirrors `_FlowAnalysisImpl.declare`, which gives the variable a `new ValueVersion()`. The
    -- declaration's AST path identifies the variable (see `Scope`).
    let π := (<- read).path
    let k <- keyForVariableM π
    let version <- newVersionM
    modifyCurrent fun fmI =>
      ⟨fmI.promotionInfo.insert k ⟨[], [], false, true, some version⟩⟩
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
    -- Only the flow model is restored here; keys and versions allocated while analyzing `s₂` stay
    -- allocated.
    setCurrent fm₁_false
    let m₃ <- withChild 2 (elabStmtImpl s₃)
    let fm₃ := (<- get).current
    setCurrent (<- joinM fm₂ fm₃)
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
