module
import Aesop
public import Lean
import Mathlib.Basic.Logic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.SplitIfs
import Std.Data.HashMap
public import FlowAnalysis.Algorithm
public import FlowAnalysis.AlgorithmRefinement
public import FlowAnalysis.Elaboration
import FlowAnalysis.PromotionChain.JoinImpl
import Mathlib.Tactic.Order

/-!
# Correctness of the algorithmic model of flow analysis

This module proves that the algorithm in `FlowAnalysis.Algorithm` is sound and complete with
respect to the specification in `FlowAnalysis.Elaboration`: whenever the algorithm accepts a
program, the specification relates it to the same lowering and to a flow model that the
algorithm's final state represents, and whenever the specification relates a program to a lowering
and a flow model, the algorithm accepts it, producing them (`elabExprImpl.correct`,
`elabStmtImpl.correct`).

The algorithm's data structures are related to the specification's by refinement relations
(`FlowModelImpl.refines` and `ReferenceImpl.refines`, defined in `FlowAnalysis.AlgorithmRefinement`,
and `ExprModelImpl.refines` and `AlgState.refines`, defined here), which interpret the algorithm's
integer promotion keys using its promotion key store, and its value versions using its flow model.
In particular, the algorithm keys properties by the value version of their target, as Dart does,
and the specification by their root variable, as `flow-analysis.md` does, so the correctness
theorems establish that the two keyings are equivalent. The proofs show that each step of the
algorithm preserves refinement, and that the key store only ever grows, so refinement established
earlier in the analysis stays valid.
-/

namespace FlowAnalysis
open DartLang

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "Expr" => Expr (τ := τ)
local notation "Property" => Property (τ := τ)
local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "Stmt" => Stmt (τ := τ)
local notation "ExprModelImpl" => ExprModelImpl (τ := τ)
local notation "FlowModelImpl" => FlowModelImpl (τ := τ)
local notation "PromotionModel" => PromotionModel (τ := τ)
local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ)

section
variable {ℓ : Type} [DecidableEq ℓ]
variable {cfg : Config (τ := τ)}

local notation "AlgM" => AlgM (τ := τ) (ℓ := ℓ)
local notation "AlgState" => AlgState (τ := τ) (ℓ := ℓ)
local notation "ExprModel" => ExprModel (τ := τ) (ℓ := ℓ)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := ℓ)
local notation "Key" => Key (ℓ := ℓ)
local notation "PromotionKeyStore" => PromotionKeyStore (ℓ := ℓ)
local notation "Reference" => Reference (ℓ := ℓ)

-- These lemmas are about the shape of `AlgM`, so none of them need to know anything about labels.
omit Γ [DecidableEq ℓ] in
/-- `get` in `AlgM` returns the state and leaves it unchanged. -/
@[simp]
theorem AlgM_get_eq {s : AlgState} :
  (get : AlgM _) cfg s = Except.ok (s, s) := rfl

omit Γ [DecidableEq ℓ] in
/-- `pure a` in `AlgM` returns `a` and leaves the state unchanged. -/
@[simp]
theorem AlgM_pure_eq {α} {s : AlgState} {a : α} :
  (pure a : AlgM _) cfg s = Except.ok (a, s) := rfl

omit Γ [DecidableEq ℓ] in
/-- `x >>= f` in `AlgM` runs `x`, then, if it succeeds with `a`, runs `f a` in the new state. -/
@[simp]
theorem AlgM_bind_eq {α β : Type} {x : AlgM α} {s : AlgState}
    {f : α → AlgM β} :
  (x >>= f) cfg s = match x cfg s with
                 | Except.ok (a, hm') => f a cfg hm'
                 | Except.error e => Except.error e := by
  simp [bind, ReaderT.bind, StateT.bind]
  cases x cfg s <;> rfl

omit Γ [DecidableEq ℓ] in
/-- `f <$> x` in `AlgM` runs `x`, then, if it succeeds with `a`, returns `f a`. -/
@[simp]
theorem AlgM_map_eq {α β : Type} {s : AlgState} {f : α → β} {x : AlgM α} :
  (f <$> x) cfg s = match x cfg s with
                 | Except.ok (a, hm') => Except.ok (f a, hm')
                 | Except.error e => Except.error e := by
  dsimp [Functor.map, StateT.instMonad, StateT.map, StateT.bind, StateT.pure, ExceptT.bind,
    ExceptT.pure, bind, pure]
  cases x cfg s <;> trivial

omit Γ [DecidableEq ℓ] in
/-- `modify f` in `AlgM` applies `f` to the state. -/
@[simp]
theorem AlgM_modify_eq {f} {s : AlgState} :
    (modify : _ → AlgM _) f cfg s = Except.ok ((), f s) := rfl

omit Γ [DecidableEq ℓ] in
/-- `set s'` in `AlgM` replaces the state with `s'`. -/
@[simp]
theorem AlgM_set_eq {s s' : AlgState} :
    (set : _ → AlgM _) s' cfg s = Except.ok ((), s') := rfl

omit Γ [DecidableEq ℓ] in
/-- `throw e` in `AlgM` never succeeds. -/
@[simp]
theorem AlgM_throw_eq_ok_contra {α e x} {s₀ s : AlgState} :
    (throw e : AlgM α) cfg s₀ = Except.ok (x, s) ↔ False := by
  constructor
  case mp => intro h; contradiction
  case mpr => intro h; exfalso; assumption

omit Γ in
/--
`keyForVariableM decl` runs `keyForVariable decl` on the state's key store, returning the key and
storing the updated key store.
-/
@[simp]
theorem keyForVariableM_eq {decl : ℓ} {s : AlgState} :
    (keyForVariableM decl : AlgM _) cfg s =
      Except.ok ((s.promotionKeyStore.keyForVariable decl).1,
        { s with promotionKeyStore := (s.promotionKeyStore.keyForVariable decl).2 }) := rfl

omit Γ [DecidableEq ℓ] in
/--
`newVersionM` runs `newVersion` on the state's key store, returning the new version and storing the
updated key store.
-/
@[simp]
theorem newVersionM_eq {s : AlgState} :
    (newVersionM : AlgM _) cfg s =
      Except.ok (s.promotionKeyStore.nextVersion,
        { s with promotionKeyStore := s.promotionKeyStore.newVersion.2 }) := rfl

omit Γ [DecidableEq ℓ] in
/--
`getOrCreatePropertyVersionM target name` runs `getOrCreatePropertyVersion target name` on the
state's key store, returning the property version and storing the updated key store.
-/
@[simp]
theorem getOrCreatePropertyVersionM_eq {target : ValueVersionImpl} {name : String}
    {s : AlgState} :
    (getOrCreatePropertyVersionM target name : AlgM _) cfg s =
      Except.ok ((s.promotionKeyStore.getOrCreatePropertyVersion target name).1,
        { s with
          promotionKeyStore := (s.promotionKeyStore.getOrCreatePropertyVersion target name).2 }) :=
  rfl

omit [DecidableEq ℓ] in
/--
`joinM fmI₁ fmI₂` runs `FlowModelImpl.join` on the state's key store, returning the joined flow
model and storing the updated key store.
-/
@[simp]
theorem joinM_eq {fmI₁ fmI₂ : FlowModelImpl} {s : AlgState} :
    (joinM fmI₁ fmI₂ : AlgM _) cfg s =
      Except.ok ((fmI₁.join fmI₂ s.promotionKeyStore).1,
        { s with promotionKeyStore := (fmI₁.join fmI₂ s.promotionKeyStore).2 }) := rfl

omit Γ [DecidableEq ℓ] in
/-- `setCurrent fmI` makes `fmI` the current flow model. -/
@[simp]
theorem setCurrent_eq {fmI : FlowModelImpl} {s : AlgState} :
    (setCurrent fmI : AlgM _) cfg s = Except.ok ((), { s with current := fmI }) := rfl

omit Γ [DecidableEq ℓ] in
/-- `modifyCurrent f` applies `f` to the current flow model. -/
@[simp]
theorem modifyCurrent_eq {f : FlowModelImpl → FlowModelImpl} {s : AlgState} :
    (modifyCurrent f : AlgM _) cfg s = Except.ok ((), { s with current := f s.current }) := rfl

omit Γ [DecidableEq ℓ] in
/-- `read` in `AlgM` returns the configuration and leaves the state unchanged. -/
@[simp]
theorem AlgM_read_eq {s : AlgState} :
    (read : AlgM _) cfg s = Except.ok (cfg, s) := rfl

omit Γ [DecidableEq ℓ] in
/-- `withChild i x` runs `x` with `i` pushed onto the configuration's AST path. -/
@[simp]
theorem withChild_eq {α} {i : Nat} {x : AlgM α} {s : AlgState} :
    (withChild i x : AlgM _) cfg s = x { cfg with path := i :: cfg.path } s := rfl

omit Γ [DecidableEq ℓ] in
/--
`withRest s₁ x` runs `x` on the statements after `s₁`: with `1` pushed onto the AST path, and the
scope extended by `s₁`'s declarations.
-/
@[simp]
theorem withRest_eq {α} {s₁ : Stmt} {x : AlgM α} {s : AlgState} :
    (withRest s₁ x : AlgM _) cfg s =
      x ⟨1 :: cfg.path, s₁.extendScope cfg.scope (0 :: cfg.path)⟩ s := rfl

/--
`emI.refines ks fmI em` says that the algorithm's expression model `emI`, interpreted in the
algorithmic flow model `fmI` that the algorithm reached after analyzing the expression, and with its
promotion keys interpreted by the key store `ks`, faithfully represents the specification's
expression model `em`.

`fmI` is needed because the algorithm only records flow models for an expression when they differ
between the `true` and `false` cases, whereas the specification always records both; and because
the expression's reference, if any, is interpreted in the flow model after the read (see
`ReferenceImpl.refines`).
-/
structure ExprModelImpl.refines (emI : ExprModelImpl) (ks : PromotionKeyStore)
    (fmI : FlowModelImpl) (em : ExprModel) :
    Prop where
  /-- The algorithm and the specification infer the same static type for the expression. -/
  types : emI.type = em.type
  /--
  The algorithm and the specification identify the same promotion target, if any: either neither
  has one, or the algorithm's reference refines the specification's.
  -/
  ref?s : Option.Rel (fun rI r => rI.refines ks fmI r) emI.ref? em.ref?
  /-- The flow models that apply when the expression evaluates to `true` are related. -/
  fm_trues : (emI.boolInfo.getD (fmI, fmI)).fst.refines ks em.fm_true
  /-- The flow models that apply when the expression evaluates to `false` are related. -/
  fm_falses : (emI.boolInfo.getD (fmI, fmI)).snd.refines ks em.fm_false

omit [DecidableEq ℓ] in
/--
An algorithmic expression model that records no boolean information refines a specification
expression model whose `true` and `false` flow models are both the flow model the algorithm reached,
given refinement of that flow model (`hrefines`) and of the references (`hrefs`).
-/
theorem ExprModelImpl.refines.noBoolInfo {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm : FlowModel} (hrefines : fmI.refines ks fm) (T : τ) {refI? : Option ReferenceImpl}
    {ref? : Option Reference} (hrefs : Option.Rel (fun rI r => rI.refines ks fmI r) refI? ref?) :
    (⟨T, refI?, none⟩ : ExprModelImpl).refines ks fmI ⟨T, ref?, fm, fm⟩ :=
  ⟨rfl, hrefs, hrefines, hrefines⟩

/--
`s.refines fm` says that the algorithm's state `s` faithfully represents the specification's flow
model `fm`: the key store is well formed, and the current flow model refines `fm` relative to it.
-/
structure AlgState.refines (s : AlgState) (fm : FlowModel) : Prop where
  /-- The key store is well formed. -/
  wf : s.promotionKeyStore.WellFormed
  /-- The current flow model refines `fm`. -/
  current : s.current.refines s.promotionKeyStore fm

omit [DecidableEq ℓ] in
/-- The algorithm's initial state refines the specification's initial flow model. -/
theorem AlgState.refines.initial : (AlgState.initial : AlgState).refines FlowModel.empty :=
  ⟨PromotionKeyStore.WellFormed.empty, FlowModelImpl.refines.empty⟩

/--
Looking up the key for the variable declared at `decl`, allocating it if necessary, preserves
refinement (`hrefines`): it gives a key `k` and a key store `ks` such that:
- looking up the key in the old store returns them
  (`s.promotionKeyStore.keyForVariable decl = (k, ks)`);
- `k` is the variable's key (`ks.variableKeys decl = some k`);
- `ks` extends the old key store (`s.promotionKeyStore.Extends ks`); and
- the state with the new key store still refines `fm`
  (`({ s with promotionKeyStore := ks } : AlgState).refines fm`).
-/
theorem AlgState.refines.keyForVariable {s : AlgState} {fm : FlowModel} (hrefines : s.refines fm)
    (decl : ℓ) :
    ∃ k ks, s.promotionKeyStore.keyForVariable decl = (k, ks) ∧ ks.variableKeys decl = some k ∧
      s.promotionKeyStore.Extends ks ∧
      ({ s with promotionKeyStore := ks } : AlgState).refines fm := by
  rcases hr : s.promotionKeyStore.keyForVariable decl with ⟨k, ks⟩
  have hwf' := PromotionKeyStore.keyForVariable_wellFormed hrefines.wf hr
  have hext := PromotionKeyStore.keyForVariable_extends hr
  exact ⟨k, ks, rfl, PromotionKeyStore.keyForVariable_variableKeys hr, hext,
    ⟨hwf', hrefines.current.mono hrefines.wf hwf' hext⟩⟩

omit [DecidableEq ℓ] in
/--
The tracked case of `handlePropertyM`: the read of a promotable property `p` (`hp`) from a target
whose reference records the version `v` (`hvI`), where `v` is the version reached along `path`
(`hpath`) from the version `v₀` that the variable declared at `root` holds (`hv₀`), in a state `s₁`
that refines `fm` (`hrefines`). It gives a new state `s₂` and a reference `rI'` such that:
- `handlePropertyM` succeeds, returning the type of the read that the specification gives for the
  property target `root` with path `path ++ [p.name]`, and `rI'`, and leaving the state `s₂`
  (`handlePropertyM (some rI) p cfg s₁ = .ok ((fm.currentTypeOf … p.type, some rI'), s₂)`);
- `s₂`'s key store extends `s₁`'s (`s₁.promotionKeyStore.Extends s₂.promotionKeyStore`);
- `s₂` still refines `fm` (`s₂.refines fm`), and has the same current flow model
  (`s₂.current = s₁.current`); and
- `rI'` refines the reference to that property target, in `s₂`'s key store and flow model
  (`rI'.refines s₂.promotionKeyStore s₂.current (.property root (path ++ [p.name]))`).
-/
theorem handlePropertyM.correct_tracked {s₁ : AlgState} {fm : FlowModel} (hrefines : s₁.refines fm)
    {rI : ReferenceImpl} {v : ValueVersionImpl} (hvI : rI.version? = some v) {root : ℓ}
    {path : List String} {v₀ : ValueVersionImpl}
    (hv₀ : s₁.current.rootVersion s₁.promotionKeyStore root = some v₀)
    (hpath : s₁.promotionKeyStore.versionAt v₀ path = some v) {p : Property}
    (hp : p.isPromotable = true) :
    ∃ s₂ rI',
      handlePropertyM (some rI) p cfg s₁ =
        .ok ((fm.currentTypeOf (some (.property root (path ++ [p.name]))) p.type, some rI'), s₂) ∧
      s₁.promotionKeyStore.Extends s₂.promotionKeyStore ∧ s₂.refines fm ∧
      s₂.current = s₁.current ∧ rI'.refines s₂.promotionKeyStore s₂.current
        (.property root (path ++ [p.name])) := by
  -- `v` is allocated, since `v₀` is.
  have hv₀lt : v₀ < s₁.promotionKeyStore.nextVersion := by
    simp only [FlowModelImpl.rootVersion, Option.bind_eq_some_iff] at hv₀
    obtain ⟨k, -, pmI, hk, hv⟩ := hv₀
    exact hrefines.current.versions k pmI v₀ hk hv
  have hvlt := hrefines.wf.versionAt_lt hv₀lt hpath
  rcases hgc : s₁.promotionKeyStore.getOrCreatePropertyVersion v p.name with ⟨pv, ks'⟩
  obtain ⟨hwf', hext, hvar, hpv⟩ :=
    PromotionKeyStore.getOrCreatePropertyVersion_spec hrefines.wf hvlt hgc
  have hrefines₂ : ({ s₁ with promotionKeyStore := ks' } : AlgState).refines fm :=
    ⟨hwf', hrefines.current.mono hrefines.wf hwf' hext⟩
  have hroot' : s₁.current.rootVersion ks' root = some v₀ := by
    rw [← hv₀]; simp [FlowModelImpl.rootVersion, hvar]
  have hchain : ks'.propertyAt v₀ (path ++ [p.name]) = some pv := by
    rw [PromotionKeyStore.propertyAt_append_singleton, hext.versionAt hpath]
    exact hpv
  refine ⟨{ s₁ with promotionKeyStore := ks' }, ⟨pv.promotionKey, some pv.version⟩, ?_, hext,
    hrefines₂, rfl, ⟨v₀, pv, hroot', hchain, rfl, rfl⟩⟩
  -- The type is the property's promoted type, if the flow model has a promotion model for it, on
  -- both sides.
  have hprop := hrefines₂.current.properties root (path ++ [p.name])
  simp only [FlowModelImpl.PropertyRefinesAt, hroot', Option.bind_some, hchain] at hprop
  simp only [handlePropertyM, Option.bind_some, hvI, hp, AlgM_bind_eq,
    getOrCreatePropertyVersionM_eq, hgc, AlgM_get_eq, AlgM_pure_eq, FlowModel.currentTypeOf,
    Reference.key_property]
  cases hprop
  case absent hlookupI hlookup => simp_all
  case present pmI pm hlookupI hlookup hrefines_pm =>
    simp_all [hrefines_pm.currentTypes]

omit [DecidableEq ℓ] in
/--
`handlePropertyM` computes the type and reference that the specification's property read rule
(`ElabExpr.propertyGet`) prescribes, and preserves refinement. If the state `s₁` refines `fm`
(`hrefines`), and the algorithm's reference `refI?` refines the specification's `ref?` (`hrefs`, in
`s₁`'s current flow model), then for property `p` there are a new state `s₂` and a reference
`refI?'` such that:
- `handlePropertyM` succeeds, returning the type of the read that the specification gives and
  `refI?'`, and leaving the state `s₂`
  (`handlePropertyM refI? p cfg s₁ = .ok ((fm.currentTypeOf … p.type, refI?'), s₂)`);
- `s₂`'s key store extends `s₁`'s (`s₁.promotionKeyStore.Extends s₂.promotionKeyStore`);
- `s₂` still refines `fm` (`s₂.refines fm`), and has the same current flow model
  (`s₂.current = s₁.current`): the read leaves the flow model alone; and
- `refI?'` refines the specification's reference for the property (`ref?.bind (·.property? p)`),
  in `s₂`'s key store and current flow model.
-/
theorem handlePropertyM.correct {s₁ : AlgState} {fm : FlowModel} (hrefines : s₁.refines fm)
    {refI? : Option ReferenceImpl} {ref? : Option Reference}
    (hrefs : Option.Rel (fun rI r => rI.refines s₁.promotionKeyStore s₁.current r) refI? ref?)
    (p : Property) :
    ∃ s₂ refI?',
      handlePropertyM refI? p cfg s₁ =
        .ok ((fm.currentTypeOf (ref?.bind (·.property? p)) p.type, refI?'), s₂) ∧
      s₁.promotionKeyStore.Extends s₂.promotionKeyStore ∧ s₂.refines fm ∧
      s₂.current = s₁.current ∧
      Option.Rel (fun rI r => rI.refines s₂.promotionKeyStore s₂.current r) refI?'
        (ref?.bind (·.property? p)) := by
  -- The cases where the read has no reference, so its type is the property's declared type.
  have huntracked : ∀ (target? : Option ReferenceImpl), target?.bind (·.version?) = none ∨
      p.isPromotable = false → (handlePropertyM target? p : AlgM _) cfg s₁ =
        Except.ok ((p.type, none), s₁) := by
    intro target? h
    rcases h with h | h <;> simp [handlePropertyM, h]
  cases hrefs
  case none =>
    exact ⟨s₁, none, by simp [huntracked none (by simp), FlowModel.currentTypeOf], .refl _,
      hrefines, rfl, .none⟩
  case some rI r hr =>
    cases hp : p.isPromotable
    case false =>
      refine ⟨s₁, none, ?_, .refl _, hrefines, rfl, ?_⟩
      · simp [huntracked (some rI) (Or.inr hp), Reference.property?, hp,
          FlowModel.currentTypeOf]
      · simp [Reference.property?, hp]
    case true =>
      cases r
      case var decl tracked =>
        obtain ⟨hk, hv, htracked⟩ := hr
        cases hvI : rI.version?
        case none =>
          have htr : tracked = false := by simp [htracked, hvI]
          refine ⟨s₁, none, ?_, .refl _, hrefines, rfl, ?_⟩
          · simp [huntracked (some rI) (Or.inl (by simp [hvI])), Reference.property?, htr,
              FlowModel.currentTypeOf]
          · simp [Reference.property?, htr]
        case some v =>
          have htr : tracked = true := by simp [htracked, hvI]
          obtain ⟨s₂, rI', hok, hext, hrefines₂, hcur, hr'⟩ :=
            handlePropertyM.correct_tracked (cfg := cfg) hrefines hvI (hvI ▸ hv).symm
              (path := []) rfl hp
          refine ⟨s₂, some rI', ?_, hext, hrefines₂, hcur, ?_⟩
          · simpa [Reference.property?, hp, htr] using hok
          · simpa [Reference.property?, hp, htr] using Option.Rel.some hr'
      case property root path =>
        obtain ⟨v₀, q, hv₀, hq, hk, hver⟩ := hr
        obtain ⟨s₂, rI', hok, hext, hrefines₂, hcur, hr'⟩ :=
          handlePropertyM.correct_tracked (cfg := cfg) hrefines hver hv₀
            (PromotionKeyStore.versionAt_of_propertyAt hq) hp
        refine ⟨s₂, some rI', ?_, hext, hrefines₂, hcur, ?_⟩
        · simpa [Reference.property?, hp] using hok
        · simpa [Reference.property?, hp] using Option.Rel.some hr'

end

/-
From here on, labels are `AstPath`s: the elaboration rules and functions identify each variable by
the AST path of its declaration (see `Scope`).
-/

local notation "AlgState" => AlgState (τ := τ) (ℓ := AstPath)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := AstPath)
local notation "PromotionKeyStore" => PromotionKeyStore (ℓ := AstPath)
local notation "Reference" => Reference (ℓ := AstPath)

/-
The next two lemmas are stated at `ℓ := AstPath`, rather than for any `ℓ`, because their `match`es
must be the very ones in `elabExprImpl`. Lean shares the auxiliary definition of a `match` between
`match`es that elaborate to the same closed term, and a `match` on `Option (ReferenceImpl ℓ)`
doesn't elaborate to the same term as one on `Option (ReferenceImpl AstPath)`. A stuck `match`
doesn't unfold, so differing auxiliary definitions wouldn't be recognized as equal.
-/

/--
The `as` elaboration case's call to `tryPromoteForTypeCast`, including the check for a missing
reference that guards it, refines the specification's `FlowModel.tryPromote`, given refinement of
the flow model (`hrefines`) relative to a well-formed key store (`hwf`) and of the references
(`hrefs`).
-/
theorem FlowModelImpl.refines.tryPromoteForTypeCast?
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {refI? : Option ReferenceImpl} {ref? : Option Reference}
    (hrefs : Option.Rel (fun rI r => rI.refines ks fmI r) refI? ref?) (previousType T : τ) :
    (match refI? with
      | some ref => fmI.tryPromoteForTypeCast ref previousType T
      | none => fmI).refines ks (fm.tryPromote ref? previousType T) := by
  cases hrefs
  case none => exact hrefines
  case some rI r hr => exact hrefines.tryPromoteForTypeCast hwf hr previousType T

/--
The null check elaboration case's call to `tryMarkNonNullable`, including the check for a missing
reference that guards it, refines the specification's `FlowModel.promoteToNonNull`, given refinement
of the flow model (`hrefines`) relative to a well-formed key store (`hwf`) and of the references
(`hrefs`).
-/
theorem FlowModelImpl.refines.tryMarkNonNullable?
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {refI? : Option ReferenceImpl} {ref? : Option Reference}
    (hrefs : Option.Rel (fun rI r => rI.refines ks fmI r) refI? ref?) (previousType : τ) :
    (match refI? with
      | some ref => fmI.tryMarkNonNullable ref previousType
      | none => fmI).refines ks (fm.promoteToNonNull ref? previousType) := by
  cases hrefs
  case none => exact hrefines
  case some rI r hr => exact hrefines.tryMarkNonNullable hwf hr previousType

/--
`elabExprImpl.Correctness π σ e` says that `elabExprImpl` is complete and sound with respect to
`ElabExpr` for the expression `e` at AST path `π`, in scope `σ`.

The path and scope are parameters, rather than being fixed for the whole proof, because the proof
for a node relies on the proofs for its children, which are at different paths (and, for statement
lists, in different scopes).
-/
structure elabExprImpl.Correctness (π : AstPath) (σ : Scope (τ := τ)) (e : Expr) : Prop where
  complete : ∀ {fm₀ m em} {s₀ : AlgState}, s₀.refines fm₀ →
    ElabExpr π σ fm₀ e m em → ∃ s emI,
      elabExprImpl e ⟨π, σ⟩ s₀ = Except.ok ((m, emI), s) ∧
      s₀.promotionKeyStore.Extends s.promotionKeyStore ∧
      s.refines em.fm_after ∧ emI.refines s.promotionKeyStore s.current em
  sound : ∀ {fm₀ m emI s} {s₀ : AlgState}, s₀.refines fm₀ →
      elabExprImpl e ⟨π, σ⟩ s₀ = Except.ok ((m, emI), s) → ∃ em,
      ElabExpr π σ fm₀ e m em ∧ s₀.promotionKeyStore.Extends s.promotionKeyStore ∧
      s.refines em.fm_after ∧ emI.refines s.promotionKeyStore s.current em

/--
The reference that the algorithm records for a read of the variable declared at `decl`, whose key
is `k` (`hk`) and whose promotion model `pmI` (`hlookupI`) refines the specification's `pm`
(`hrefines_pm`), refines the specification's reference, which records whether the variable is
tracked.
-/
theorem ReferenceImpl.refines.var {fmI : FlowModelImpl} {ks : PromotionKeyStore} {decl : AstPath}
    {k : PromotionKey} (hk : ks.variableKeys decl = some k) {pmI : PromotionModelImpl}
    (hlookupI : fmI.promotionInfo[k]? = some pmI) {pm : PromotionModel}
    (hrefines_pm : pmI.refines pm) :
    (⟨k, pmI.version?⟩ : ReferenceImpl).refines ks fmI (.var decl !pm.writeCaptured) := by
  refine ⟨hk, by simp [FlowModelImpl.rootVersion_eq hk, hlookupI], ?_⟩
  rw [← hrefines_pm.writeCaptured]
  simp only [PromotionModelImpl.writeCaptured]
  cases pmI.version? <;> rfl

/-- `elabExprImpl` is correct (`Correctness`) for a reference to a variable named `n`. -/
theorem elabExprImpl.correct.var {π σ} (n : String) :
    elabExprImpl.Correctness (τ := τ) π σ (.var n) := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases helab; case var v decl pm T hasg hT hlookup hscope =>
    subst hT
    simp only [ExprModel.simple_after]
    obtain ⟨k, ks₁, hr, hk, hext, hrefines₁⟩ := hrefines₀.keyForVariable decl
    cases hrefines₁.current.variableInfos decl k hk
    case absent hlookupI hlookup' => simp_all
    case present pmI pm' hlookupI hlookup' hrefines_pm =>
      have hpm : pm' = pm := by simp_all
      subst hpm
      refine ⟨{ s₀ with promotionKeyStore := ks₁ },
        ⟨pm'.currentType v.type, some ⟨k, pmI.version?⟩, none⟩, ?_, hext, hrefines₁,
        ExprModelImpl.refines.noBoolInfo hrefines₁.current _
          (.some (ReferenceImpl.refines.var hk hlookupI hrefines_pm))⟩
      rcases hasg with h | h
      · simp [elabExprImpl, hscope, hr, hlookupI, h, hrefines_pm.assigned,
          hrefines_pm.currentTypes]
      · simp [elabExprImpl, hscope, hr, hlookupI, h, hrefines_pm.currentTypes]
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    simp only [elabExprImpl, AlgM_bind_eq, AlgM_read_eq] at hok
    cases hscope : σ.lookup n
    case none => simp [hscope] at hok
    case some vd =>
    obtain ⟨v, decl⟩ := vd
    obtain ⟨k, ks₁, hr, hk, hext, hrefines₁⟩ := hrefines₀.keyForVariable decl
    simp only [hscope, AlgM_bind_eq, keyForVariableM_eq, AlgM_get_eq, hr] at hok
    cases hrefines₁.current.variableInfos decl k hk
    case absent hlookupI hlookup => simp_all
    case present pmI pm hlookupI hlookup hrefines_pm =>
      simp only [hlookupI] at hok
      split at hok
      case isTrue => simp at hok
      case isFalse hguard =>
      have hasg : pm.Readable v := by
        have h := hguard
        simp only [hrefines_pm.assigned, Bool.not_eq_true', Bool.or_eq_false_iff,
          not_and] at h
        unfold PromotionModel.Readable
        cases ha : pm.assigned <;> simp_all
      simp [hrefines_pm.currentTypes] at hok
      rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
      refine ⟨⟨pm.currentType v.type, some (.var decl !pm.writeCaptured), fm₀, fm₀⟩,
        ElabExpr.var hscope hlookup hasg rfl, hext, ?_,
        ExprModelImpl.refines.noBoolInfo hrefines₁.current _
          (.some (ReferenceImpl.refines.var hk hlookupI hrefines_pm))⟩
      simp only [ExprModel.simple_after]
      exact hrefines₁

/--
A property read is correct if the read of its target is (`hcorrect₁`): the target's reference is
passed to `handlePropertyM`, which does what `ElabExpr.propertyGet` prescribes.
-/
theorem elabExprImpl.correct.propertyGet {π σ} (e₁ : Expr) (p : Property)
    (hcorrect₁ : elabExprImpl.Correctness (0 :: π) σ e₁) :
    elabExprImpl.Correctness π σ (e₁.property p) := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases helab; case propertyGet m₁ em₁ ref? T helab₁ href hT =>
    subst href hT
    obtain ⟨s₁, emI₁, hok₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.complete hrefines₀ helab₁
    obtain ⟨s₂, refI?, hok₂, hext₂, hrefines₂, -, hrefs₂⟩ :=
      handlePropertyM.correct (cfg := ⟨π, σ⟩) hrefines₁ hrefines_em₁.ref?s p
    simp only [ExprModel.simple_after]
    refine ⟨s₂, ⟨_, refI?, none⟩, ?_, hext₁.trans hext₂, hrefines₂,
      ExprModelImpl.refines.noBoolInfo hrefines₂.current _ hrefs₂⟩
    simp [elabExprImpl, hok₁, hok₂]
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    simp only [elabExprImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π, σ⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, s₁⟩
    obtain ⟨em₁, helab₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    obtain ⟨s₂, refI?, hok₂, hext₂, hrefines₂, -, hrefs₂⟩ :=
      handlePropertyM.correct (cfg := ⟨π, σ⟩) hrefines₁ hrefines_em₁.ref?s p
    simp [hok₁, hok₂] at hok
    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
    refine ⟨_, ElabExpr.propertyGet helab₁ rfl rfl, hext₁.trans hext₂, ?_,
      ExprModelImpl.refines.noBoolInfo hrefines₂.current _ hrefs₂⟩
    simp only [ExprModel.simple_after]
    exact hrefines₂

/-- A null check `e₁!` is correct if the analysis of its operand is (`hcorrect₁`). -/
theorem elabExprImpl.correct.nullCheck {π σ} (e₁ : Expr) (hcorrect₁ :
    elabExprImpl.Correctness (0 :: π) σ e₁) :
    elabExprImpl.Correctness π σ e₁.nullCheck := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases helab; case nullCheck m₁ em₁ fm hfm helab₁ =>
    subst hfm
    obtain ⟨s₁, emI₁, hok₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.complete hrefines₀ helab₁
    have hrefines_fm :=
      hrefines₁.current.tryMarkNonNullable? hrefines₁.wf hrefines_em₁.ref?s emI₁.type
    simp only [← hrefines_em₁.types, ExprModel.simple_after]
    refine ⟨{ s₁ with
        current :=
          match emI₁.ref? with
          | some ref => s₁.current.tryMarkNonNullable ref emI₁.type
          | none => s₁.current },
      ⟨NonNull emI₁.type, none, none⟩, ?_, hext₁,
      ⟨hrefines₁.wf, hrefines_fm⟩, ExprModelImpl.refines.noBoolInfo hrefines_fm _ .none⟩
    -- The two sides' `match`es are distinct auxiliary definitions, so `simp` can't identify them,
    -- but they unfold to the same term.
    simp [elabExprImpl, hok₁]
    rfl
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    simp only [elabExprImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π, σ⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, s₁⟩
    simp [hok₁] at hok
    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
    obtain ⟨em₁, helab₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    have hrefines_fm :=
      hrefines₁.current.tryMarkNonNullable? hrefines₁.wf hrefines_em₁.ref?s emI₁.type
    refine ⟨_, ElabExpr.nullCheck helab₁ rfl, hext₁, ?_, ?_⟩
    all_goals simp only [← hrefines_em₁.types, ExprModel.simple_after]
    · exact ⟨hrefines₁.wf, hrefines_fm⟩
    · exact ExprModelImpl.refines.noBoolInfo hrefines_fm _ .none

/-- A cast `e₁ as T` is correct if the analysis of its operand is (`hcorrect₁`). -/
theorem elabExprImpl.correct.asExpr {π σ} (e₁ : Expr) T
    (hcorrect₁ : elabExprImpl.Correctness (0 :: π) σ e₁) :
    elabExprImpl.Correctness π σ (e₁.as T) := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases helab; case asExpr m₁ em₁ fm helab₁ hfm =>
    subst hfm
    obtain ⟨s₁, emI₁, hok₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.complete hrefines₀ helab₁
    have hrefines_fm :=
      hrefines₁.current.tryPromoteForTypeCast? hrefines₁.wf hrefines_em₁.ref?s emI₁.type T
    simp only [← hrefines_em₁.types, ExprModel.simple_after]
    refine ⟨{ s₁ with
        current :=
          match emI₁.ref? with
          | some ref => s₁.current.tryPromoteForTypeCast ref emI₁.type T
          | none => s₁.current },
      ⟨T, none, none⟩, ?_, hext₁, ⟨hrefines₁.wf, hrefines_fm⟩,
      ExprModelImpl.refines.noBoolInfo hrefines_fm _ .none⟩
    -- The two sides' `match`es are distinct auxiliary definitions, so `simp` can't identify them,
    -- but they unfold to the same term.
    simp [elabExprImpl, hok₁]
    rfl
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    simp only [elabExprImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π, σ⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, s₁⟩
    simp [hok₁] at hok
    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
    obtain ⟨em₁, helab₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    have hrefines_fm :=
      hrefines₁.current.tryPromoteForTypeCast? hrefines₁.wf hrefines_em₁.ref?s emI₁.type T
    refine ⟨_, ElabExpr.asExpr helab₁ rfl, hext₁, ?_, ?_⟩
    all_goals simp only [← hrefines_em₁.types, ExprModel.simple_after]
    · exact ⟨hrefines₁.wf, hrefines_fm⟩
    · exact ExprModelImpl.refines.noBoolInfo hrefines_fm _ .none

/--
A type test `e₁ is T` is correct if the analysis of its operand is (`hcorrect₁`): the flow model for
when it's `true` is computed as for a cast, and the flow model for when it's `false` is the one
after the operand. The flow model afterwards is their join, as `ExprModel.fm_after` says, which may
extend the key store, so the two flow models are carried over to the extended store.
-/
theorem elabExprImpl.correct.isExpr {π σ} (e₁ : Expr) T
    (hcorrect₁ : elabExprImpl.Correctness (0 :: π) σ e₁) :
    elabExprImpl.Correctness π σ (e₁.is T) := by
  -- What happens after the operand's analysis, from the state `s₁`, on both sides, where `fmI_true`
  -- is the flow model for when the test is `true` (`hfmI_true`).
  have hafter : ∀ {s₁ : AlgState} {emI₁ : ExprModelImpl} {em₁ : ExprModel}
      {fmI_true : FlowModelImpl},
      s₁.refines em₁.fm_after → emI₁.refines s₁.promotionKeyStore s₁.current em₁ →
      fmI_true =
        (match emI₁.ref? with
        | some ref => s₁.current.tryPromoteForTypeCast ref emI₁.type T
        | none => s₁.current) →
      s₁.promotionKeyStore.Extends (fmI_true.join s₁.current s₁.promotionKeyStore).2 ∧
      ({ current := (fmI_true.join s₁.current s₁.promotionKeyStore).1,
         promotionKeyStore := (fmI_true.join s₁.current s₁.promotionKeyStore).2 } :
        AlgState).refines ((em₁.fm_after.tryPromote em₁.ref? em₁.type T).join em₁.fm_after) ∧
      (⟨Γ.bool, none, some (fmI_true, s₁.current)⟩ : ExprModelImpl).refines
        (fmI_true.join s₁.current s₁.promotionKeyStore).2
        (fmI_true.join s₁.current s₁.promotionKeyStore).1
        ⟨Γ.bool, none, em₁.fm_after.tryPromote em₁.ref? em₁.type T, em₁.fm_after⟩ := by
    intro s₁ emI₁ em₁ fmI_true hrefines₁ hrefines_em₁ hfmI_true
    have hrefines_fm :=
      hrefines₁.current.tryPromoteForTypeCast? hrefines₁.wf hrefines_em₁.ref?s emI₁.type T
    rw [← hfmI_true, hrefines_em₁.types] at hrefines_fm
    obtain ⟨hwf', hext, hjoin⟩ := hrefines_fm.join hrefines₁.current hrefines₁.wf
    exact ⟨hext, ⟨hwf', hjoin⟩, ⟨rfl, .none, hrefines_fm.mono hrefines₁.wf hwf' hext,
      hrefines₁.current.mono hrefines₁.wf hwf' hext⟩⟩
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases helab; case isExpr m₁ em₁ fm_true helab₁ hfm =>
    subst hfm
    obtain ⟨s₁, emI₁, hok₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.complete hrefines₀ helab₁
    obtain ⟨hext, hrefines', hrefines_em'⟩ := hafter hrefines₁ hrefines_em₁ rfl
    refine ⟨_, _, ?_, hext₁.trans hext, hrefines', hrefines_em'⟩
    -- The two sides' `match`es are distinct auxiliary definitions, so `simp` can't identify them,
    -- but they unfold to the same term.
    simp [elabExprImpl, hok₁]
    rfl
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    simp only [elabExprImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π, σ⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, s₁⟩
    simp [hok₁] at hok
    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
    obtain ⟨em₁, helab₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    obtain ⟨hext, hrefines', hrefines_em'⟩ := hafter hrefines₁ hrefines_em₁ rfl
    exact ⟨_, ElabExpr.isExpr helab₁ rfl, hext₁.trans hext, hrefines', hrefines_em'⟩

/-- `elabExprImpl` is correct (`Correctness`) for the null literal. -/
theorem elabExprImpl.correct.nullLiteral {π σ} :
    elabExprImpl.Correctness (τ := τ) π σ .null := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases helab; case nullLiteral =>
    simp only [ExprModel.simple_after]
    refine ⟨s₀, ⟨Γ.Null, none, none⟩, ?_, .refl _, hrefines₀,
      ExprModelImpl.refines.noBoolInfo hrefines₀.current _ .none⟩
    simp [elabExprImpl]
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok; simp [elabExprImpl] at hok
    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
    refine ⟨⟨Γ.Null, none, fm₀, fm₀⟩, ElabExpr.nullLiteral, .refl _, ?_,
      ExprModelImpl.refines.noBoolInfo hrefines₀.current _ .none⟩
    simp only [ExprModel.simple_after]
    exact hrefines₀

/--
The algorithm's update for giving the variable declared at `decl`, whose key is `k` (`hk`), a new
value, in a state with flow model `fmI` and key store `ks` that refines `fm` (`hrefines`):
allocating a new version, and storing the promotion model `pmI`, which refines `pm`
(`hrefines_pm`), and holds no version or the new one (`hversion`). This is the common core of
declarations and assignments. Afterwards:
- the new key store extends `ks` (`ks.Extends ks.newVersion.2`); and
- the new state refines the specification's `(fm.eraseRooted decl).set (.var decl) pm`
  (`({ current := ⟨fmI.promotionInfo.insert k pmI⟩, promotionKeyStore := ks.newVersion.2 } :
  AlgState).refines ((fm.eraseRooted decl).set (.var decl) pm)`).
-/
theorem AlgState.refines.insertFresh {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm : FlowModel}
    (hrefines : ({ current := fmI, promotionKeyStore := ks } : AlgState).refines fm)
    {decl : AstPath} {k : PromotionKey} (hk : ks.variableKeys decl = some k)
    {pmI : PromotionModelImpl} {pm : PromotionModel} (hrefines_pm : pmI.refines pm)
    (hversion : pmI.version? = none ∨ pmI.version? = some ks.nextVersion) :
    ks.Extends ks.newVersion.2 ∧
    ({ current := ⟨fmI.promotionInfo.insert k pmI⟩, promotionKeyStore := ks.newVersion.2 } :
      AlgState).refines ((fm.eraseRooted decl).set (.var decl) pm) :=
  ⟨PromotionKeyStore.newVersion_extends,
    PromotionKeyStore.newVersion_wellFormed hrefines.wf,
    hrefines.current.insertFresh hrefines.wf hk hrefines_pm hversion⟩

/-- `PromotionModelImpl.write` gives the location the new version, unless it's write captured. -/
theorem PromotionModelImpl.write_version? (pmI : PromotionModelImpl) (writtenType : τ)
    (newVersion : ValueVersionImpl) :
    (pmI.write writtenType newVersion).version? = none ∨
      (pmI.write writtenType newVersion).version? = some newVersion := by
  unfold PromotionModelImpl.write
  split
  case isTrue h =>
    left
    simpa [PromotionModelImpl.writeCaptured] using h
  case isFalse => right; rfl

/--
An assignment is correct if the analysis of its right-hand side is (`hcorrect₁`): the variable gets
a new version, and its promotion model is then updated by `PromotionModelImpl.write`, which refines
`PromotionModel.write`; the specification forgets the property targets rooted at the variable,
which the new version has none of.
-/
theorem elabExprImpl.correct.assign {π σ} (n : String) (e₁ : Expr)
    (hcorrect₁ : elabExprImpl.Correctness (0 :: π) σ e₁) :
    elabExprImpl.Correctness π σ (.assign n e₁) := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases helab; case assign m₁ em₁ v decl pm fm hlookup htype hfin hfm hscope helab₁ =>
    subst hfm
    obtain ⟨s₁, emI₁, hok₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.complete hrefines₀ helab₁
    obtain ⟨k, ks₂, hr, hk, hext₂, hrefines₂⟩ := hrefines₁.keyForVariable decl
    cases hrefines₂.current.variableInfos decl k hk
    case absent hlookupI hlookup' => simp_all
    case present pmI pm' hlookupI hlookup' hrefines_pm =>
      have hpm : pm' = pm := by simp_all
      subst hpm
      obtain ⟨hext₃, hrefines₃⟩ := hrefines₂.insertFresh hk
        (hrefines_pm.write em₁.type ks₂.nextVersion) (pmI.write_version? _ _)
      simp only [ExprModel.simple_after]
      refine ⟨_, ⟨em₁.type, none, none⟩, ?_, hext₁.trans (hext₂.trans hext₃), hrefines₃,
        ExprModelImpl.refines.noBoolInfo hrefines₃.current _ .none⟩
      have hfinI : ¬(v.isFinal = true ∧ pmI.unassigned = false) := fun ⟨hv, hu⟩ => by
        simp [hrefines_pm.unassigned, hfin hv] at hu
      simp [elabExprImpl, hok₁, hscope, htype, hr, hlookupI, hfinI, hrefines_em₁.types]
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    simp only [elabExprImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π, σ⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, s₁⟩
    obtain ⟨em₁, helab₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    simp only [hok₁, AlgM_read_eq] at hok
    cases hscope : σ.lookup n
    case none => simp [hscope] at hok
    case some vd =>
    obtain ⟨v, decl⟩ := vd
    by_cases htype : emI₁.type ≤ v.type
    case neg => simp [hscope, htype] at hok
    case pos =>
    obtain ⟨k, ks₂, hr, hk, hext₂, hrefines₂⟩ := hrefines₁.keyForVariable decl
    simp only [hscope, htype, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
      AlgM_bind_eq, keyForVariableM_eq, hr, AlgM_get_eq] at hok
    cases hrefines₂.current.variableInfos decl k hk
    case absent hlookupI hlookup => simp [hlookupI] at hok
    case present pmI pm hlookupI hlookup hrefines_pm =>
      simp only [hlookupI] at hok
      split at hok
      case isTrue => simp at hok
      case isFalse hguard =>
      have hfin : v.isFinal = true → pm.unassigned = true := fun hv => by
        simpa [hv, hrefines_pm.unassigned] using hguard
      simp at hok
      rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
      have htype' : em₁.type ≤ v.type := hrefines_em₁.types ▸ htype
      obtain ⟨hext₃, hrefines₃⟩ := hrefines₂.insertFresh hk
        (hrefines_pm.write em₁.type ks₂.nextVersion) (pmI.write_version? _ _)
      refine ⟨_, ElabExpr.assign helab₁ hscope hlookup htype' hfin rfl,
        hext₁.trans (hext₂.trans hext₃), ?_, ?_⟩
      all_goals simp only [hrefines_em₁.types, ExprModel.simple_after]
      · exact hrefines₃
      · exact ExprModelImpl.refines.noBoolInfo hrefines₃.current _ .none

/--
**Correctness of the expression analysis**: `elabExprImpl` is complete and sound with respect to
`ElabExpr` (`Correctness`) for every expression `e`, at every AST path `π`, in every scope `σ`.
-/
theorem elabExprImpl.correct (π : AstPath) (σ : Scope (τ := τ)) (e : Expr) :
    elabExprImpl.Correctness π σ e := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases h : e <;> rw [h] at helab
    case var n => apply (elabExprImpl.correct.var n).complete hrefines₀ helab
    case nullCheck e₁ =>
      apply (elabExprImpl.correct.nullCheck e₁ (elabExprImpl.correct (0 :: π) σ e₁)).complete
        hrefines₀ helab
    case as e₁ T =>
      apply (elabExprImpl.correct.asExpr e₁ T (elabExprImpl.correct (0 :: π) σ e₁)).complete
        hrefines₀ helab
    case is e₁ T =>
      apply (elabExprImpl.correct.isExpr e₁ T (elabExprImpl.correct (0 :: π) σ e₁)).complete
        hrefines₀ helab
    case null => apply elabExprImpl.correct.nullLiteral.complete hrefines₀ helab
    case property e₁ p =>
      apply (elabExprImpl.correct.propertyGet e₁ p (elabExprImpl.correct (0 :: π) σ e₁)).complete
        hrefines₀ helab
    case assign n e₁ =>
      apply (elabExprImpl.correct.assign n e₁ (elabExprImpl.correct (0 :: π) σ e₁)).complete
        hrefines₀ helab
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    cases h : e <;> rw [h] at hok
    case var n => apply (elabExprImpl.correct.var n).sound hrefines₀ hok
    case nullCheck e₁ =>
      apply (elabExprImpl.correct.nullCheck e₁ (elabExprImpl.correct (0 :: π) σ e₁)).sound
        hrefines₀ hok
    case as e₁ T =>
      apply (elabExprImpl.correct.asExpr e₁ T (elabExprImpl.correct (0 :: π) σ e₁)).sound
        hrefines₀ hok
    case is e₁ T =>
      apply (elabExprImpl.correct.isExpr e₁ T (elabExprImpl.correct (0 :: π) σ e₁)).sound
        hrefines₀ hok
    case null => apply elabExprImpl.correct.nullLiteral.sound hrefines₀ hok
    case property e₁ p =>
      apply (elabExprImpl.correct.propertyGet e₁ p (elabExprImpl.correct (0 :: π) σ e₁)).sound
        hrefines₀ hok
    case assign n e₁ =>
      apply (elabExprImpl.correct.assign n e₁ (elabExprImpl.correct (0 :: π) σ e₁)).sound
        hrefines₀ hok

/--
`elabStmtImpl.Correctness π σ s` says that `elabStmtImpl` is complete and sound with respect to
`ElabStmt` for the statement `s` at AST path `π`, in scope `σ`.
-/
structure elabStmtImpl.Correctness (π : AstPath) (σ : Scope (τ := τ)) (s : Stmt) : Prop where
  complete :
    ∀ {fm₀ m fm} {s₀ : AlgState}, s₀.refines fm₀ →
      ElabStmt π σ fm₀ s m fm →
      ∃ sI, elabStmtImpl s ⟨π, σ⟩ s₀ = Except.ok (m, sI) ∧
        s₀.promotionKeyStore.Extends sI.promotionKeyStore ∧ sI.refines fm
  sound :
    ∀ {fm₀ m sI} {s₀ : AlgState},
      s₀.refines fm₀ → elabStmtImpl s ⟨π, σ⟩ s₀ = Except.ok (m, sI) →
      ∃ fm, ElabStmt π σ fm₀ s m fm ∧
        s₀.promotionKeyStore.Extends sI.promotionKeyStore ∧ sI.refines fm

/--
`elabStmtsImpl.Correctness π σ ss` says that `elabStmtsImpl` is complete and sound with respect to
`ElabStmts` for the statement list `ss` at AST path `π`, in scope `σ`.
-/
structure elabStmtsImpl.Correctness (π : AstPath) (σ : Scope (τ := τ)) (ss : List Stmt) : Prop where
  complete :
    ∀ {fm₀ m fm} {s₀ : AlgState}, s₀.refines fm₀ →
      ElabStmts π σ fm₀ ss m fm →
      ∃ sI, elabStmtsImpl ss ⟨π, σ⟩ s₀ = Except.ok (m, sI) ∧
        s₀.promotionKeyStore.Extends sI.promotionKeyStore ∧ sI.refines fm
  sound :
    ∀ {fm₀ m sI} {s₀ : AlgState},
      s₀.refines fm₀ → elabStmtsImpl ss ⟨π, σ⟩ s₀ = Except.ok (m, sI) →
      ∃ fm, ElabStmts π σ fm₀ ss m fm ∧
        s₀.promotionKeyStore.Extends sI.promotionKeyStore ∧ sI.refines fm

/--
`elabStmtImpl` is correct (`Correctness`) for a declaration of a variable named `n`: the variable
gets a new version, which has no properties, as the specification forgets the property targets
rooted at the variable.
-/
theorem elabStmtImpl.correct.declare {π σ} (n : String) (T : τ) (isFinal : Bool) :
    elabStmtImpl.Correctness π σ (.declare n T isFinal) := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases helab; case declare =>
    obtain ⟨k, ks₁, hr, hk, hext, hrefines₁⟩ := hrefines₀.keyForVariable π
    obtain ⟨hext₂, hrefines₂⟩ := hrefines₁.insertFresh hk
      (PromotionModelImpl.refines.declared false ks₁.nextVersion) (Or.inr rfl)
    refine ⟨_, ?_, hext.trans hext₂, hrefines₂⟩
    simp [elabStmtImpl, hr]
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    obtain ⟨k, ks₁, hr, hk, hext, hrefines₁⟩ := hrefines₀.keyForVariable π
    simp [elabStmtImpl, hr] at hok
    rcases hok with ⟨rfl, rfl⟩
    obtain ⟨hext₂, hrefines₂⟩ := hrefines₁.insertFresh hk
      (PromotionModelImpl.refines.declared false ks₁.nextVersion) (Or.inr rfl)
    exact ⟨_, ElabStmt.declare π σ fm₀ n T isFinal, hext.trans hext₂, hrefines₂⟩

/-- An expression statement is correct if the analysis of its expression is (`hcorrect₁`). -/
theorem elabStmtImpl.correct.exprStmt {π σ}
    (e₁ : Expr) (hcorrect₁ : elabExprImpl.Correctness (0 :: π) σ e₁) :
    elabStmtImpl.Correctness π σ (.exprStmt e₁) := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases helab; case exprStmt em₁ helab₁ =>
    obtain ⟨s₁, emI₁, hok₁, hext₁, hrefines₁, -⟩ := hcorrect₁.complete hrefines₀ helab₁
    refine ⟨s₁, ?_, hext₁, hrefines₁⟩
    simp [elabStmtImpl, hok₁]
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    simp only [elabStmtImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π, σ⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, s₁⟩
    simp [hok₁] at hok
    rcases hok with ⟨rfl, rfl⟩
    obtain ⟨em₁, helab₁, hext₁, hrefines₁, -⟩ := hcorrect₁.sound hrefines₀ hok₁
    exact ⟨_, ElabStmt.exprStmt helab₁, hext₁, hrefines₁⟩

/--
An if statement is correct if the analyses of its condition (`hcorrect₁`) and its two branches
(`hcorrect₂`, `hcorrect₃`) are.
-/
theorem elabStmtImpl.correct.ifStmt {π σ}
    (e₁ : Expr) (s₂ s₃ : Stmt)
    (hcorrect₁ : elabExprImpl.Correctness (0 :: π) σ e₁)
    (hcorrect₂ : elabStmtImpl.Correctness (1 :: π) σ s₂)
    (hcorrect₃ : elabStmtImpl.Correctness (2 :: π) σ s₃) :
    elabStmtImpl.Correctness π σ (.ifStmt e₁ s₂ s₃) := by
  -- The join at the end of the statement, of the flow models after the two branches.
  have hjoin : ∀ {sI₂ sI₃ : AlgState} {fm₂ fm₃ : FlowModel},
      sI₂.refines fm₂ → sI₃.refines fm₃ →
      sI₂.promotionKeyStore.Extends sI₃.promotionKeyStore →
      let r := sI₂.current.join sI₃.current sI₃.promotionKeyStore
      sI₃.promotionKeyStore.Extends r.2 ∧
      ({ sI₃ with current := r.1, promotionKeyStore := r.2 } : AlgState).refines
        (fm₂.join fm₃) := by
    intro sI₂ sI₃ fm₂ fm₃ hrefines₂ hrefines₃ hext₃ r
    obtain ⟨hwf', hext, hjoin⟩ :=
      (hrefines₂.current.mono hrefines₂.wf hrefines₃.wf hext₃).join hrefines₃.current
        hrefines₃.wf
    exact ⟨hext, hwf', hjoin⟩
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases helab; case ifStmt m₁ em₁ m₂ fm₂ m₃ fm₃ his_bool helab₁ helab₂ helab₃ =>
    obtain ⟨s₁, emI₁, hok₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.complete hrefines₀ helab₁
    -- Analyze the `then` branch, starting from the flow model for when the condition is true.
    obtain ⟨sI₂, hok₂, hext₂, hrefines₂⟩ :=
      hcorrect₂.complete
        (s₀ := { s₁ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).fst })
        ⟨hrefines₁.wf, hrefines_em₁.fm_trues⟩ helab₂
    -- Analyze the `else` branch, starting from the flow model for when the condition is false.
    -- That flow model was computed before the `then` branch was analyzed, which may have allocated
    -- keys and versions, so its refinement has to be carried over to the enlarged key store.
    obtain ⟨sI₃, hok₃, hext₃, hrefines₃⟩ :=
      hcorrect₃.complete
        (s₀ := { sI₂ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).snd })
        ⟨hrefines₂.wf, hrefines_em₁.fm_falses.mono hrefines₁.wf hrefines₂.wf hext₂⟩ helab₃
    -- Likewise, the `then` branch's final flow model has to be carried over to the key store as
    -- enlarged by the `else` branch, before the two are joined.
    obtain ⟨hext₄, hrefines₄⟩ := hjoin hrefines₂ hrefines₃ hext₃
    refine ⟨_, ?_, hext₁.trans (hext₂.trans (hext₃.trans hext₄)), hrefines₄⟩
    have his_boolI : emI₁.type = Γ.bool := hrefines_em₁.types.trans his_bool
    simp [elabStmtImpl, hok₁, his_boolI, hok₂, hok₃]
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    simp only [elabStmtImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π, σ⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, s₁⟩
    obtain ⟨em₁, helab₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    by_cases his_bool : em₁.type = Γ.bool
    case neg =>
      have : emI₁.type ≠ Γ.bool := by rw [hrefines_em₁.types]; exact his_bool
      simp [hok₁, this] at hok
    case pos =>
    have his_boolI : emI₁.type = Γ.bool := hrefines_em₁.types.trans his_bool
    simp [hok₁, his_boolI] at hok
    cases hok₂ : elabStmtImpl s₂ ⟨1 :: π, σ⟩
        { s₁ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).fst }
    case error => simp [hok₂] at hok
    case ok result₂ =>
    rcases result₂ with ⟨m₂, sI₂⟩
    obtain ⟨fm₂, helab₂, hext₂, hrefines₂⟩ :=
      hcorrect₂.sound
        (s₀ := { s₁ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).fst })
        ⟨hrefines₁.wf, hrefines_em₁.fm_trues⟩ hok₂
    cases hok₃ : elabStmtImpl s₃ ⟨2 :: π, σ⟩
        { sI₂ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).snd }
    case error => simp [hok₂, hok₃] at hok
    case ok result₃ =>
    rcases result₃ with ⟨m₃, sI₃⟩
    obtain ⟨fm₃, helab₃, hext₃, hrefines₃⟩ :=
      hcorrect₃.sound
        (s₀ := { sI₂ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).snd })
        ⟨hrefines₂.wf, hrefines_em₁.fm_falses.mono hrefines₁.wf hrefines₂.wf hext₂⟩ hok₃
    simp [hok₂, hok₃] at hok
    rcases hok with ⟨rfl, rfl⟩
    obtain ⟨hext₄, hrefines₄⟩ := hjoin hrefines₂ hrefines₃ hext₃
    exact ⟨fm₂.join fm₃, ElabStmt.ifStmt helab₁ his_bool helab₂ helab₃,
      hext₁.trans (hext₂.trans (hext₃.trans hext₄)), hrefines₄⟩

/-- A block is correct if the analysis of its statement list is (`hcorrect₁`). -/
theorem elabStmtImpl.correct.block {π σ}
    (ss₁ : List Stmt) (hcorrect₁ : elabStmtsImpl.Correctness (0 :: π) σ ss₁) :
    elabStmtImpl.Correctness π σ (.block ss₁) := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases helab; case block ms₁ helab₁ =>
    obtain ⟨sI₁, hok₁, hext₁, hrefines₁⟩ := hcorrect₁.complete hrefines₀ helab₁
    refine ⟨sI₁, ?_, hext₁, hrefines₁⟩
    simp [elabStmtImpl, hok₁]
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    simp only [elabStmtImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabStmtsImpl ss₁ ⟨0 :: π, σ⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨m₁, sI₁⟩
    simp [hok₁] at hok
    rcases hok with ⟨rfl, rfl⟩
    obtain ⟨fm₁, helab₁, hext₁, hrefines₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    exact ⟨fm₁, ElabStmt.block helab₁, hext₁, hrefines₁⟩

/-- `elabStmtsImpl` is correct (`Correctness`) for the empty statement list. -/
theorem elabStmtsImpl.correct.nil {π σ} :
    elabStmtsImpl.Correctness (τ := τ) π σ [] := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases helab; case nil =>
    exact ⟨s₀, by simp [elabStmtsImpl], .refl _, hrefines₀⟩
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok; simp [elabStmtsImpl] at hok
    rcases hok with ⟨rfl, rfl⟩
    exact ⟨fm₀, ElabStmts.nil, .refl _, hrefines₀⟩

/--
A statement list `s₁ :: ss₂` is correct if the analyses of its first statement (`hcorrect₁`) and of
the rest, in the scope extended by `s₁`'s declarations (`hcorrect₂`), are.
-/
theorem elabStmtsImpl.correct.cons {π σ}
    (s₁ : Stmt) (ss₂ : List Stmt)
    (hcorrect₁ : elabStmtImpl.Correctness (0 :: π) σ s₁)
    (hcorrect₂ : elabStmtsImpl.Correctness (1 :: π) (s₁.extendScope σ (0 :: π)) ss₂) :
    elabStmtsImpl.Correctness π σ (s₁ :: ss₂) := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases helab; case cons fm₁ m₁ ms₂ helab₁ helab₂ =>
    obtain ⟨sI₁, hok₁, hext₁, hrefines₁⟩ := hcorrect₁.complete hrefines₀ helab₁
    obtain ⟨sI₂, hok₂, hext₂, hrefines₂⟩ := hcorrect₂.complete hrefines₁ helab₂
    refine ⟨sI₂, ?_, hext₁.trans hext₂, hrefines₂⟩
    simp [elabStmtsImpl, hok₁, hok₂]
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    simp only [elabStmtsImpl, AlgM_bind_eq, withChild_eq, withRest_eq] at hok
    cases hok₁ : elabStmtImpl s₁ ⟨0 :: π, σ⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨m₁, sI₁⟩
    obtain ⟨fm₁, helab₁, hext₁, hrefines₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    cases hok₂ : elabStmtsImpl ss₂ ⟨1 :: π, s₁.extendScope σ (0 :: π)⟩ sI₁
    case error => simp [hok₁, hok₂] at hok
    case ok result₂ =>
    rcases result₂ with ⟨m₂, sI₂⟩
    obtain ⟨fm₂, helab₂, hext₂, hrefines₂⟩ := hcorrect₂.sound hrefines₁ hok₂
    simp [hok₁, hok₂] at hok
    rcases hok with ⟨rfl, rfl⟩
    exact ⟨fm₂, ElabStmts.cons helab₁ helab₂, hext₁.trans hext₂, hrefines₂⟩

mutual
/--
**Correctness of the statement analysis**: `elabStmtImpl` is complete and sound with respect to
`ElabStmt` (`Correctness`) for every statement `s`, at every AST path `π`, in every scope `σ`.
-/
theorem elabStmtImpl.correct (π : AstPath) (σ : Scope (τ := τ)) (s : Stmt) :
    elabStmtImpl.Correctness π σ s := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases h : s <;> rw [h] at helab
    case declare n T isFinal =>
      apply (elabStmtImpl.correct.declare n T isFinal).complete hrefines₀ helab
    case exprStmt e₁ =>
      apply (elabStmtImpl.correct.exprStmt e₁ (elabExprImpl.correct (0 :: π) σ e₁)).complete
        hrefines₀ helab
    case ifStmt e₁ s₂ s₃ =>
      apply
        (elabStmtImpl.correct.ifStmt e₁ s₂ s₃ (elabExprImpl.correct (0 :: π) σ e₁)
            (elabStmtImpl.correct (1 :: π) σ s₂) (elabStmtImpl.correct (2 :: π) σ s₃)).complete
          hrefines₀ helab
    case block ss =>
      apply (elabStmtImpl.correct.block ss (elabStmtsImpl.correct (0 :: π) σ ss)).complete
        hrefines₀ helab
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    cases h : s <;> rw [h] at hok
    case declare n T isFinal =>
      apply (elabStmtImpl.correct.declare n T isFinal).sound hrefines₀ hok
    case exprStmt e₁ =>
      apply (elabStmtImpl.correct.exprStmt e₁ (elabExprImpl.correct (0 :: π) σ e₁)).sound
        hrefines₀ hok
    case ifStmt e₁ s₂ s₃ =>
      apply
        (elabStmtImpl.correct.ifStmt e₁ s₂ s₃ (elabExprImpl.correct (0 :: π) σ e₁)
            (elabStmtImpl.correct (1 :: π) σ s₂) (elabStmtImpl.correct (2 :: π) σ s₃)).sound
          hrefines₀ hok
    case block ss =>
      apply (elabStmtImpl.correct.block ss (elabStmtsImpl.correct (0 :: π) σ ss)).sound
        hrefines₀ hok

/--
**Correctness of the statement-list analysis**: `elabStmtsImpl` is complete and sound with respect
to `ElabStmts` (`Correctness`) for every statement list `ss`, at every AST path `π`, in every scope
`σ`.
-/
theorem elabStmtsImpl.correct (π : AstPath) (σ : Scope (τ := τ)) (ss : List Stmt) :
    elabStmtsImpl.Correctness π σ ss := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases h : ss <;> rw [h] at helab
    case nil => apply elabStmtsImpl.correct.nil.complete hrefines₀ helab
    case cons s ss =>
      apply
        (elabStmtsImpl.correct.cons s ss (elabStmtImpl.correct (0 :: π) σ s)
            (elabStmtsImpl.correct (1 :: π) (s.extendScope σ (0 :: π)) ss)).complete
          hrefines₀ helab
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    cases h : ss <;> rw [h] at hok
    case nil => apply elabStmtsImpl.correct.nil.sound hrefines₀ hok
    case cons s ss =>
      apply
        (elabStmtsImpl.correct.cons s ss (elabStmtImpl.correct (0 :: π) σ s)
            (elabStmtsImpl.correct (1 :: π) (s.extendScope σ (0 :: π)) ss)).sound
          hrefines₀ hok
end

/--
**Soundness of the statement analysis, from the start of flow analysis**: if `elabStmtImpl` accepts
the statement `s`, at AST path `π` and in scope `σ`, starting from the initial state, and lowers it
to `m` (`hok`), then `s` elaborates to `m`, starting from the empty flow model (`ElabStmt π σ
FlowModel.empty s m fm`, for some flow model `fm`).
-/
public theorem elabStmtImpl.sound_initial {π : AstPath} {σ : Scope (τ := τ)} {s : Stmt} {m sI}
    (hok : elabStmtImpl s ⟨π, σ⟩ AlgState.initial = Except.ok (m, sI)) :
    ∃ fm, ElabStmt π σ FlowModel.empty s m fm :=
  let ⟨fm, helab, _⟩ := (elabStmtImpl.correct π σ s).sound AlgState.refines.initial hok
  ⟨fm, helab⟩

end FlowAnalysis
