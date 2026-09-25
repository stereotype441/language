/-
Proofs of soundness and completeness of the algorithmic implementation in `FlowAnalysis.algorithm`.
-/

module
import Aesop
public import Lean
import Mathlib.Logic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.SplitIfs
import Std.Data.HashMap
import FlowAnalysis.Algorithm
import FlowAnalysis.Elaboration
import FlowAnalysis.PromotionChain.JoinImpl
import Mathlib.Tactic.Order

section
open Lean Elab Tactic Meta

/--
`by_cases_iff h` splits a hypothesis `h : P ↔ Q` into two subgoals:
- `pos`: assuming both `P` and `Q` are true.
- `neg`: assuming both `¬P` and `¬Q` are true.
-/
elab "by_cases_iff" t:term : tactic => withMainContext do
  -- 1. Split the equivalence: creates a temporary `Or` hypothesis and case-splits it
  evalTactic (← `(tactic| have h_or := iff_iff_and_or_not_and_not.mp $t))
  evalTactic (← `(tactic| cases h_or <;> rename_i h_or <;> cases h_or))

  -- 2. Grab the two resulting subgoals and assign the `pos` and `neg` tags
  let goals ← getGoals
  match goals with
  | g1 :: g2 :: rest =>
    g1.setTag `pos
    g2.setTag `neg
    setGoals (g1 :: g2 :: rest)
  | _ =>
    -- Fail silently or log nothing if the goal was solved during splitting
    pure ()
end

namespace FlowAnalysis

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "Expr" => Expr (τ := τ)
local notation "Property" => Property (τ := τ)
local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "Stmt" => Stmt (τ := τ)

section
variable {ℓ : Type} [DecidableEq ℓ]
variable {cfg : Config}

local notation "AlgM" => AlgM (τ := τ) (ℓ := ℓ)
local notation "AlgState" => AlgState (τ := τ) (ℓ := ℓ)
local notation "ExprModel" => ExprModel (τ := τ) (ℓ := ℓ)
local notation "ExprModelImpl" => ExprModelImpl (τ := τ) (ℓ := ℓ)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := ℓ)
local notation "FlowModelImpl" => FlowModelImpl (τ := τ) (ℓ := ℓ)
local notation "Key" => Key (τ := τ) (ℓ := ℓ)
local notation "PromotionKeyStore" => PromotionKeyStore (τ := τ) (ℓ := ℓ)
local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := ℓ)
local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ) (ℓ := ℓ)
local notation "Reference" => Reference (τ := τ) (ℓ := ℓ)
local notation "ReferenceImpl" => ReferenceImpl (ℓ := ℓ)
local notation "ValueVersion" => ValueVersion (ℓ := ℓ)
local notation "ValueVersionImpl" => ValueVersionImpl (ℓ := ℓ)

-- These lemmas are about the shape of `AlgM`, so none of them need to know anything about labels.
omit [DecidableEq ℓ] in
@[simp]
theorem AlgM_get_eq {s : AlgState} :
  (get : AlgM _) cfg s = Except.ok (s, s) := rfl

omit [DecidableEq ℓ] in
@[simp]
theorem AlgM_pure_eq {α} {s : AlgState} {a : α} :
  (pure a : AlgM _) cfg s = Except.ok (a, s) := rfl

omit [DecidableEq ℓ] in
@[simp]
theorem AlgM_bind_eq {α β : Type} {x : AlgM α} {s : AlgState}
    {f : α → AlgM β} :
  (x >>= f) cfg s = match x cfg s with
                 | Except.ok (a, hm') => f a cfg hm'
                 | Except.error e => Except.error e := by
  simp [bind, ReaderT.bind, StateT.bind]
  cases x cfg s <;> rfl

omit [DecidableEq ℓ] in
@[simp]
theorem AlgM_map_eq {α β : Type} {s : AlgState} {f : α → β} {x : AlgM α} :
  (f <$> x) cfg s = match x cfg s with
                 | Except.ok (a, hm') => Except.ok (f a, hm')
                 | Except.error e => Except.error e := by
  dsimp [Functor.map, StateT.instMonad, StateT.map, StateT.bind, StateT.pure, ExceptT.bind, ExceptT.pure, bind, pure]
  cases x cfg s <;> trivial

omit [DecidableEq ℓ] in
@[simp]
theorem AlgM_modify_eq {f} {s : AlgState} :
    (modify : _ → AlgM _) f cfg s = Except.ok ((), f s) := rfl

omit [DecidableEq ℓ] in
@[simp]
theorem AlgM_set_eq {s s' : AlgState} :
    (set : _ → AlgM _) s' cfg s = Except.ok ((), s') := rfl

omit [DecidableEq ℓ] in
@[simp]
theorem AlgM_throw_eq_ok_contra {α e x} {s₀ s : AlgState} :
    (throw e : AlgM α) cfg s₀ = Except.ok (x, s) ↔ False := by
  constructor
  case mp => intro h; contradiction
  case mpr => intro h; exfalso; assumption

omit [DecidableEq ℓ] in
@[simp]
theorem keyForVariableM_eq {v : Variable} {s : AlgState} :
    (keyForVariableM v : AlgM _) cfg s =
      Except.ok ((s.promotionKeyStore.keyForVariable v).1,
        { s with promotionKeyStore := (s.promotionKeyStore.keyForVariable v).2 }) := rfl

@[simp]
theorem getOrCreatePropertyVersionM_eq {target : ValueVersionImpl} {name : String}
    {s : AlgState} :
    (getOrCreatePropertyVersionM target name : AlgM _) cfg s =
      Except.ok ((s.promotionKeyStore.getOrCreatePropertyVersion target name).1,
        { s with
          promotionKeyStore := (s.promotionKeyStore.getOrCreatePropertyVersion target name).2 }) :=
  rfl

omit [DecidableEq ℓ] in
@[simp]
theorem setCurrent_eq {fmI : FlowModelImpl} {s : AlgState} :
    (setCurrent fmI : AlgM _) cfg s = Except.ok ((), { s with current := fmI }) := rfl

omit [DecidableEq ℓ] in
@[simp]
theorem modifyCurrent_eq {f : FlowModelImpl → FlowModelImpl} {s : AlgState} :
    (modifyCurrent f : AlgM _) cfg s = Except.ok ((), { s with current := f s.current }) := rfl

omit [DecidableEq ℓ] in
@[simp]
theorem AlgM_read_eq {s : AlgState} :
    (read : AlgM _) cfg s = Except.ok (cfg, s) := rfl

omit [DecidableEq ℓ] in
@[simp]
theorem withChild_eq {α} {i : Nat} {x : AlgM α} {s : AlgState} :
    (withChild i x : AlgM _) cfg s = x { cfg with path := i :: cfg.path } s := rfl

/--
`fmI.PromotionInfoRefinesAt fm k key` says that the `promotionInfo` fields of the algorithm's flow
model `fmI` and the specification's flow model `fm` agree about the promotion key `k`, which stands
for the specification key `key`: either neither flow model has an entry for it, or both do, and the
algorithm's promotion model refines the specification's.
-/
inductive FlowModelImpl.PromotionInfoRefinesAt (fmI : FlowModelImpl)
    (fm : FlowModel) (k : PromotionKey) (key : Key) : Prop where
  /-- Neither flow model has an entry. -/
  | absent (hlookupI : fmI.promotionInfo[k]? = none) (hlookup : fm.promotionInfo key = none)
  /-- Both flow models have an entry, and their promotion models are related by `refines`. -/
  | present
        {pmI : PromotionModelImpl} {pm : PromotionModel} (hlookupI : fmI.promotionInfo[k]? = some pmI)
        (hlookup : fm.promotionInfo key = some pm) (hrefines_pm : pmI.refines pm)

/--
`fmI.refines ks fm` says that the algorithm's flow model `fmI`, whose promotion keys are interpreted
by the key store `ks`, faithfully represents the specification's flow model `fm`.

Each clause covers one way a promotion key can relate to a specification key.  Only the first says
anything interesting; the other two ensure that neither flow model records anything the other has no
way to name.
-/
structure FlowModelImpl.refines (fmI : FlowModelImpl) (ks : PromotionKeyStore)
    (fm : FlowModel) : Prop where
  /-- The two flow models agree about every allocated promotion key. -/
  promotionInfos (k : PromotionKey) (key : Key) (hk : ks.keys[k]? = some key) :
    fmI.PromotionInfoRefinesAt fm k key
  /-- The specification's flow model records nothing about a key that no promotion key stands for. -/
  unallocated (key : Key) (hunallocated : ∀ k : PromotionKey, ks.keys[k]? ≠ some key) :
    fm.promotionInfo key = none
  /-- The algorithm's flow model records nothing under a promotion key that hasn't been allocated. -/
  beyondEnd (k : PromotionKey) (hk : ks.keys[k]? = none) : fmI.promotionInfo[k]? = none

omit [DecidableEq ℓ] in
/-- The algorithm's initial flow model refines the specification's initial flow model. -/
theorem FlowModelImpl.refines.empty {ks : PromotionKeyStore} :
    (.empty : FlowModelImpl).refines ks FlowModel.empty where
  promotionInfos _ _ _ := .absent (by simp [FlowModelImpl.empty]) (by simp [FlowModel.empty])
  unallocated _ _ := by simp [FlowModel.empty]
  beyondEnd _ _ := by simp [FlowModelImpl.empty]

omit [DecidableEq ℓ] in
/--
A flow model refined by `fmI` maps every key to `none` precisely when `fmI`'s `promotionInfo` is empty.
-/
theorem FlowModelImpl.refines.isEmpty {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm : FlowModel} (hrefines : fmI.refines ks fm) :
    fmI.promotionInfo.isEmpty ↔ ∀ key : Key, fm.promotionInfo key = none := by
  constructor
  case mp =>
    intro hemptyI key
    by_cases hallocated : ∃ k : PromotionKey, ks.keys[k]? = some key
    case pos =>
      obtain ⟨k, hk⟩ := hallocated
      have : fmI.promotionInfo[k]? = none := Std.HashMap.getElem?_of_isEmpty hemptyI
      cases hrefines.promotionInfos k key hk <;> simp_all
    case neg =>
      exact hrefines.unallocated key fun k hk => hallocated ⟨k, hk⟩
  case mpr =>
    intro hempty
    rw [Std.HashMap.isEmpty_iff_forall_not_mem]
    intro k
    cases hk : ks.keys[k]?
    case none =>
      have := hrefines.beyondEnd k hk
      simp_all
    case some key =>
      have := hempty key
      cases hrefines.promotionInfos k key hk <;> simp_all

omit [DecidableEq ℓ] in
/--
An algorithmic flow model whose `promotionInfo` is empty refines the specification's empty flow
model, whatever the key store.

The conclusion is spelled out as `⟨fun _ => none⟩` rather than `FlowModel.empty` because `simp`
matches conclusions syntactically; stating it in terms of `FlowModel.empty` would stop this lemma
from firing on the goals that arise in `FlowModelImpl.refines.join`.
-/
@[simp]
theorem FlowModelImpl.refines.empty_of_isEmpty {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    (hempty : fmI.promotionInfo.isEmpty) : fmI.refines ks ⟨fun _ => none⟩ where
  promotionInfos _ _ _ := .absent (Std.HashMap.getElem?_of_isEmpty hempty) (by simp)
  unallocated _ _ := by simp
  beyondEnd _ _ := Std.HashMap.getElem?_of_isEmpty hempty

omit [DecidableEq ℓ] in
/--
A single algorithmic flow model can't refine two different specification flow models relative to the
same key store, since it determines each allocated key's promotion model up to
`PromotionModelImpl.refines`, which is itself unique, and every unallocated key reads as `none`.
-/
theorem FlowModelImpl.refines.unique {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm₁ fm₂ : FlowModel} (hrefines₁ : fmI.refines ks fm₁) (hrefines₂ : fmI.refines ks fm₂) :
    fm₁ = fm₂ := by
  apply FlowModel.extensionality; intro key
  by_cases hallocated : ∃ k : PromotionKey, ks.keys[k]? = some key
  case neg =>
    have hunallocated : ∀ k : PromotionKey, ks.keys[k]? ≠ some key := fun k hk => hallocated ⟨k, hk⟩
    rw [hrefines₁.unallocated key hunallocated, hrefines₂.unallocated key hunallocated]
  case pos =>
  obtain ⟨k, hk⟩ := hallocated
  cases hrefines₁.promotionInfos k key hk
  case absent hlookupI₁ hlookup₁ => cases hrefines₂.promotionInfos k key hk <;> simp_all
  case present pmI₁ pm₁ hlookupI₁ hlookup₁ hrefines_pm₁ =>
    cases hrefines₂.promotionInfos k key hk
    case absent hlookupI₂ hlookup₂ => simp_all
    case present pmI₂ pm₂ hlookupI₂ hlookup₂ hrefines_pm₂ =>
      -- `fmI` has a single entry for `k`, so `pm₁` and `pm₂` refine the same `PromotionModelImpl`,
      -- and `PromotionModelImpl.refines` determines the promotion model it refines uniquely.
      have hpmIs : pmI₁ = pmI₂ := by simp_all
      subst hpmIs
      rw [hlookup₁, hlookup₂, hrefines_pm₁.unique hrefines_pm₂]

omit [DecidableEq ℓ] in
/--
Refinement survives the allocation of more keys.

This is what lets a flow model saved before analyzing one branch of an `if` statement be used after
it: the branch may have allocated keys, but a key the saved flow model never heard of reads as
`none` on both sides.  On the algorithm's side that is `beyondEnd`; on the specification's side, it
takes `keys_inj` to see that no *old* key already stood for the same specification key.
-/
theorem FlowModelImpl.refines.mono {fmI : FlowModelImpl} {ks ks' : PromotionKeyStore}
    {fm : FlowModel} (hrefines : fmI.refines ks fm) (hwf' : ks'.WellFormed)
    (hext : ks.Extends ks') : fmI.refines ks' fm where
  promotionInfos k key hk' := by
    cases hk : ks.keys[k]?
    case some key₀ =>
      -- `k` was already allocated, and `Extends` says it still stands for the same key.
      have heq : key₀ = key := by
        have := hext k key₀ hk
        rw [hk'] at this
        exact (Option.some.inj this).symm
      subst heq
      exact hrefines.promotionInfos k key₀ hk
    case none =>
      -- `k` is newly allocated.  No old key stood for `key`, since `Extends` would have carried it
      -- over to `ks'`, where `keys_inj` would have identified it with `k`.
      refine .absent (hrefines.beyondEnd k hk) (hrefines.unallocated key ?_)
      intro k'' hk''
      have heq := hwf'.keys_inj k'' k key (hext k'' key hk'') hk'
      subst heq
      simp [hk] at hk''
  unallocated key hunallocated' :=
    hrefines.unallocated key fun k hk => hunallocated' k (hext k key hk)
  beyondEnd k hk' := by
    apply hrefines.beyondEnd k
    cases hk : ks.keys[k]?
    case none => rfl
    case some key => simp [hext k key hk] at hk'

/--
Refinement is preserved by adding an entry to both flow models, under a promotion key and the
specification key it stands for, provided the promotion models being added are themselves related by
`refines`.
-/
theorem FlowModelImpl.refines.insert {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm : FlowModel} {pmI : PromotionModelImpl} {pm : PromotionModel} {k : PromotionKey}
    {key : Key} (hrefines_fm : fmI.refines ks fm) (hwf : ks.WellFormed)
    (hk : ks.keys[k]? = some key) (hrefines_pm : pmI.refines pm) :
    (FlowModelImpl.mk (fmI.promotionInfo.insert k pmI)).refines ks (fm.set key pm) := by
  constructor
  case promotionInfos =>
    intro k' key' hk'
    by_cases heq : k = k'
    case pos =>
      subst heq
      have hkey : key = key' := by
        rw [hk] at hk'
        exact Option.some.inj hk'
      subst hkey
      exact .present (by simp) (by simp) hrefines_pm
    case neg =>
      -- Distinct promotion keys stand for distinct specification keys, so neither side's entry for
      -- `k'` is disturbed.
      have hne : key ≠ key' := by
        rintro rfl
        exact heq (hwf.keys_inj k k' key hk hk')
      cases hrefines_fm.promotionInfos k' key' hk'
      case absent hlookupI hlookup =>
        exact .absent (by simp [Std.HashMap.getElem?_insert, heq, hlookupI]) (by simp [hne, hlookup])
      case present pmI' pm' hlookupI hlookup hrefines_pm' =>
        exact .present (by simp [Std.HashMap.getElem?_insert, heq, hlookupI])
          (by simp [hne, hlookup]) hrefines_pm'
  case unallocated =>
    intro key' hunallocated
    have hne : key ≠ key' := by
      rintro rfl
      exact hunallocated k hk
    simp [hne, hrefines_fm.unallocated key' hunallocated]
  case beyondEnd =>
    intro k' hk'
    have hne : k ≠ k' := by
      rintro rfl
      simp [hk] at hk'
    simp [Std.HashMap.getElem?_insert, hne, hrefines_fm.beyondEnd k' hk']

/--
`finishTypeTest` refines the specification's promotion of a single promotion model, whenever the
promotion it records is one the algorithm has checked is valid.
-/
theorem FlowModelImpl.refines.finishTypeTest
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {k : PromotionKey} {key : Key} (hk : ks.keys[k]? = some key)
    {pmI : PromotionModelImpl} {pm : PromotionModel} (hrefines_pm : pmI.refines pm) {T : τ}
    (hchain : isPromotionChain (pmI.promotedTypes ++ [T])) (hwc : ¬pm.writeCaptured) :
    (fmI.finishTypeTest k pmI T).refines ks (fm.set key (pm.tryPromote T hwc)) :=
  hrefines.insert hwf hk (hrefines_pm.promote hchain hwc)

/--
`rI.refines ks r` says that the algorithm's reference `rI`, whose promotion key is interpreted by
the key store `ks`, faithfully represents the specification's reference `r`: the promotion key
stands for `r.key`, and the version is `r`'s, placed at the path of `r.key`.

The version needs the path because the specification's versions don't carry one (see
`ValueVersionImpl`).
-/
structure ReferenceImpl.refines (rI : ReferenceImpl) (ks : PromotionKeyStore) (r : Reference) :
    Prop where
  /-- The promotion key stands for the reference's key. -/
  key : ks.keys[rI.promotionKey]? = some r.key
  /-- The versions agree, once the specification's is placed at the path of the key. -/
  version? : rI.version? = r.version?.map (⟨·, r.key.path⟩)

omit [DecidableEq ℓ] in
/-- Refinement of a reference survives the allocation of more keys. -/
theorem ReferenceImpl.refines.mono {rI : ReferenceImpl} {ks ks' : PromotionKeyStore}
    {r : Reference} (hr : rI.refines ks r) (hext : ks.Extends ks') : rI.refines ks' r :=
  ⟨hext _ _ hr.key, hr.version?⟩

/--
The algorithm's `tryPromoteForTypeCast` refines the specification's `FlowModel.tryPromote`.

`tryMarkNonNullable` differs only in how it computes the type to promote to, so its counterpart,
`FlowModelImpl.refines.tryMarkNonNullable`, is a corollary.
-/
theorem FlowModelImpl.refines.tryPromoteForTypeCast
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {rI : ReferenceImpl} {r : Reference} (hr : rI.refines ks r)
    (previousType T : τ) :
    (fmI.tryPromoteForTypeCast rI previousType T).refines ks
      (fm.tryPromote (some r) previousType T) := by
  simp only [FlowModelImpl.tryPromoteForTypeCast, FlowModel.tryPromote]
  cases hrefines.promotionInfos rI.promotionKey r.key hr.key
  case absent hlookupI hlookup =>
    -- Neither side has a stored model, so `infoFor` supplies a fresh one on both sides, at the
    -- version that was read (if any).
    simp only [FlowModelImpl.infoFor, FlowModel.infoFor, hlookupI, hlookup, hr.version?]
    cases r.version?
    case none => exact hrefines
    case some v =>
      have hwcI : (PromotionModelImpl.fresh v : PromotionModelImpl).writeCaptured = false := rfl
      have hwc : ¬(PromotionModel.fresh v : PromotionModel).writeCaptured := by
        simp [PromotionModel.fresh]
      simp only [Option.map_some, hwcI, hwc, Bool.false_eq_true, ↓reduceIte, not_false_eq_true,
        true_and]
      by_cases hT_lt : T < previousType
      case neg => simp [hT_lt, hrefines]
      case pos =>
        -- A fresh model has no promotions, so appending `T` always yields a promotion chain.
        have hchain : isPromotionChain
            ((PromotionModelImpl.fresh v : PromotionModelImpl).promotedTypes ++ [T]) := by
          simp [PromotionModelImpl.fresh]
        simp only [hT_lt, hchain, and_self, ↓reduceIte, ↓reduceDIte]
        exact hrefines.finishTypeTest hwf hr.key (PromotionModelImpl.refines.fresh v) hchain hwc
  case present pmI pm hlookupI hlookup hrefines_pm =>
    simp only [FlowModelImpl.infoFor, FlowModel.infoFor, hlookupI, hlookup]
    -- Neither the algorithm nor the specification promotes a write-captured location, so dispose
    -- of that case first; afterwards both guards reduce to the same conditions.
    have hwcs : pmI.writeCaptured = pm.writeCaptured := hrefines_pm.writeCaptured
    by_cases hwc : pm.writeCaptured
    case pos => simp [hwcs, hwc, hrefines]
    case neg =>
      simp only [hwcs, hwc, Bool.false_eq_true, ↓reduceIte, not_false_eq_true, true_and]
      by_cases hT_lt : T < previousType
      case neg => simp [hT_lt, hrefines]
      case pos =>
        simp only [hT_lt, true_and, ↓reduceDIte]
        -- Unlike `FlowModel.tryPromote`, which promotes using `PromotionChain.tryPromote`, the
        -- algorithm checks explicitly whether appending `T` produces a valid promotion chain, and
        -- leaves `promotionInfo` untouched if it doesn't. So we need to consider the two cases
        -- separately.
        by_cases hchain : isPromotionChain (pmI.promotedTypes ++ [T])
        case pos =>
          simp only [hchain, ↓reduceIte]
          exact hrefines.finishTypeTest hwf hr.key hrefines_pm hchain hwc
        case neg =>
          -- Neither the algorithm nor the spec promoted `key`, so neither one changed its state;
          -- for the spec, this is because `PromotionModel.tryPromote` was a no-op, so the `set`
          -- assigned `key` the promotion model it already had.
          simp only [hchain, ↓reduceIte]
          rw [hrefines_pm.tryPromote_eq_self hchain, FlowModel.set_self hlookup]
          exact hrefines

/-- The algorithm's `tryMarkNonNullable` refines the specification's `promoteToNonNull`. -/
theorem FlowModelImpl.refines.tryMarkNonNullable
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {rI : ReferenceImpl} {r : Reference} (hr : rI.refines ks r)
    (previousType : τ) :
    (fmI.tryMarkNonNullable rI previousType).refines ks
      (fm.promoteToNonNull (some r) previousType) :=
  hrefines.tryPromoteForTypeCast hwf hr previousType (NonNull previousType)

section
variable {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {f : β → β → β} {m₁ m₂ : Std.HashMap α β}

/-- A key that's absent from the first map being merged is absent from the merged map. -/
theorem mergeMaps_none₁ {k : α} : k ∉ m₁ → k ∉ mergeMaps f m₁ m₂ := by
  simp_all [mergeMaps, Std.HashMap.mem_filterMap]

/-- A key that's absent from the second map being merged is absent from the merged map. -/
theorem mergeMaps_none₂ {k : α} : k ∉ m₂ → k ∉ mergeMaps f m₁ m₂ := by
  simp_all [mergeMaps, Std.HashMap.mem_filterMap]

/-- A key that's present in both maps being merged is mapped to the combination of its values. -/
theorem mergeMaps_some {k : α} {v₁ v₂ : β} :
    m₁[k]? = some v₁ → m₂[k]? = some v₂ → (mergeMaps f m₁ m₂)[k]? = f v₁ v₂ := by
  simp_all [mergeMaps]

end

/-- Refinement is preserved by joining the two flow models pointwise. -/
theorem FlowModelImpl.refines.join {fmI₁ fmI₂ : FlowModelImpl} {ks : PromotionKeyStore}
    {fm₁ fm₂ : FlowModel} (hrefines₁ : fmI₁.refines ks fm₁) (hrefines₂ : fmI₂.refines ks fm₂) :
    (fmI₁.join fmI₂).refines ks (fm₁.join fm₂) := by
  simp [FlowModelImpl.join, FlowModel.join]
  by_cases_iff hrefines₁.isEmpty <;> simp_all
  case neg hnonEmpty₁ hnonEmptyI₁ =>
    by_cases_iff hrefines₂.isEmpty <;> simp_all
    case pos => (conv => enter [3, 1, v]; tactic => split); simp_all
    case neg hnonEmpty₂ hnonEmptyI₂ =>
      constructor
      case promotionInfos =>
        intro k key hk
        cases hrefines₁.promotionInfos k key hk
        case absent hlookupI₁ hlookup₁ =>
          exact .absent (by simp_all [mergeMaps_none₁]) (by simp_all)
        case present pmI₁ pm₁ hlookupI₁ hlookup₁ hrefines_pm₁ =>
          cases hrefines₂.promotionInfos k key hk
          case absent hlookupI₂ hlookup₂ =>
            exact .absent (by simp_all [mergeMaps_none₂]) (by simp_all)
          case present pmI₂ pm₂ hlookupI₂ hlookup₂ hrefines_pm₂ =>
            exact .present
              (by simp_all [mergeMaps_some])
              (by simp_all)
              (hrefines_pm₁.join hrefines_pm₂)
      case unallocated =>
        intro key hunallocated
        simp [hrefines₁.unallocated key hunallocated]
      case beyondEnd =>
        intro k hk
        have := hrefines₁.beyondEnd k hk
        simp_all [mergeMaps_none₁]

/--
`emI.refines ks fmI em` says that the algorithm's expression model `emI`, interpreted in the
algorithmic flow model `fmI` that the algorithm reached after analyzing the expression, and with its
promotion keys interpreted by the key store `ks`, faithfully represents the specification's
expression model `em`.

`fmI` is needed because the algorithm only records flow models for an expression when they differ
between the `true` and `false` cases, whereas the specification always records both.
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
  ref?s : Option.Rel (fun rI r => rI.refines ks r) emI.ref? em.ref?
  /-- The flow models that apply when the expression evaluates to `true` are related. -/
  fm_trues : (emI.boolInfo.getD (fmI, fmI)).fst.refines ks em.fm_true
  /-- The flow models that apply when the expression evaluates to `false` are related. -/
  fm_falses : (emI.boolInfo.getD (fmI, fmI)).snd.refines ks em.fm_false

omit [DecidableEq ℓ] in
/--
An algorithmic expression model that records no boolean information refines a specification
expression model whose `true` and `false` flow models are both the flow model the algorithm reached.
-/
theorem ExprModelImpl.refines.noBoolInfo {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm : FlowModel} (hrefines : fmI.refines ks fm) (T : τ) {refI? : Option ReferenceImpl}
    {ref? : Option Reference} (hrefs : Option.Rel (fun rI r => rI.refines ks r) refI? ref?) :
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

omit [DecidableEq ℓ] in
/--
Looking up the key for a variable, allocating it if necessary, preserves refinement, and yields a
key that stands for the variable.
-/
theorem AlgState.refines.keyForVariable {s : AlgState} {fm : FlowModel} (hrefines : s.refines fm)
    (v : Variable) :
    ∃ k ks, s.promotionKeyStore.keyForVariable v = (k, ks) ∧ ks.keys[k]? = some (.var v) ∧
      s.promotionKeyStore.Extends ks ∧
      ({ s with promotionKeyStore := ks } : AlgState).refines fm := by
  rcases hr : s.promotionKeyStore.keyForVariable v with ⟨k, ks⟩
  have hwf' := PromotionKeyStore.keyForVariable_wellFormed hrefines.wf hr
  have hext := PromotionKeyStore.keyForVariable_extends hr
  exact ⟨k, ks, rfl, PromotionKeyStore.keyForVariable_keys hrefines.wf hr, hext,
    ⟨hwf', hrefines.current.mono hwf' hext⟩⟩

/--
Looking up the key for a property of a value, allocating it if necessary, preserves refinement, and
yields a key that stands for the property.
-/
theorem AlgState.refines.getOrCreatePropertyVersion {s : AlgState} {fm : FlowModel}
    (hrefines : s.refines fm) (target : ValueVersionImpl) (name : String) :
    ∃ k ks, s.promotionKeyStore.getOrCreatePropertyVersion target name = (k, ks) ∧
      ks.keys[k]? = some (.loc target.roots (target.path ++ [name])) ∧
      s.promotionKeyStore.Extends ks ∧
      ({ s with promotionKeyStore := ks } : AlgState).refines fm := by
  rcases hr : s.promotionKeyStore.getOrCreatePropertyVersion target name with ⟨k, ks⟩
  have hwf' := PromotionKeyStore.getOrCreatePropertyVersion_wellFormed hrefines.wf hr
  have hext := PromotionKeyStore.getOrCreatePropertyVersion_extends hr
  exact ⟨k, ks, rfl, PromotionKeyStore.getOrCreatePropertyVersion_keys hrefines.wf hr, hext,
    ⟨hwf', hrefines.current.mono hwf' hext⟩⟩

/--
`handlePropertyM` computes the type and reference that the specification's property read rule
(`ElabExpr.propertyGet`) prescribes, and preserves refinement. It leaves the flow model alone, so
the specification's flow model `fm` is unchanged.
-/
theorem handlePropertyM.correct {s₁ : AlgState} {fm : FlowModel} (hrefines : s₁.refines fm)
    {refI? : Option ReferenceImpl} {ref? : Option Reference}
    (hrefs : Option.Rel (fun rI r => rI.refines s₁.promotionKeyStore r) refI? ref?)
    (p : Property) :
    ∃ s₂ refI?',
      handlePropertyM refI? p cfg s₁ =
        .ok ((fm.currentTypeOf (ref?.bind (·.property? p)) p.type, refI?'), s₂) ∧
      s₁.promotionKeyStore.Extends s₂.promotionKeyStore ∧ s₂.refines fm ∧
      Option.Rel (fun rI r => rI.refines s₂.promotionKeyStore r) refI?'
        (ref?.bind (·.property? p)) := by
  cases hrefs
  case none =>
    exact ⟨s₁, none, by simp [handlePropertyM, FlowModel.currentTypeOf], .refl _, hrefines, .none⟩
  case some rI r hr =>
    cases hv : r.version?
    case none =>
      have hvI : rI.version? = none := by simp [hr.version?, hv]
      refine ⟨s₁, none, ?_, .refl _, hrefines, ?_⟩
      · simp [handlePropertyM, hvI, Reference.property?_eq, hv, FlowModel.currentTypeOf]
      · simp [Reference.property?_eq, hv]
    case some v =>
      have hvI : rI.version? = some ⟨v, r.key.path⟩ := by simp [hr.version?, hv]
      cases hp : p.isPromotable
      case false =>
        refine ⟨s₁, none, ?_, .refl _, hrefines, ?_⟩
        · simp [handlePropertyM, hvI, hp, Reference.property?_eq, FlowModel.currentTypeOf]
        · simp [Reference.property?_eq, hp]
      case true =>
        obtain ⟨k, ks, hr', hk, hext, hrefines'⟩ :=
          hrefines.getOrCreatePropertyVersion ⟨v, r.key.path⟩ p.name
        have hproperty : r.property? p = some (.property v (r.key.path ++ [p.name])) := by
          simp [Reference.property?_eq, hp, hv]
        refine ⟨{ s₁ with promotionKeyStore := ks },
          some ⟨k, some ⟨v, r.key.path ++ [p.name]⟩⟩, ?_, hext, hrefines', ?_⟩
        · -- The type is the property's promoted type, if the flow model has a promotion model for
          -- it, on both sides.
          simp only [handlePropertyM, hvI, hp, Option.bind_some, AlgM_bind_eq,
            getOrCreatePropertyVersionM_eq, hr', AlgM_get_eq, AlgM_pure_eq, hproperty,
            FlowModel.currentTypeOf, Reference.key_property]
          cases hrefines'.current.promotionInfos k _ hk
          case absent hlookupI hlookup => simp_all
          case present pmI pm hlookupI hlookup hrefines_pm =>
            simp_all [hrefines_pm.currentTypes]
        · simp only [Option.bind_some, hproperty]
          exact .some ⟨hk, by simp⟩

end

/-
The elaboration rules and functions label value versions by AST paths, so from here on labels are
`AstPath`s.
-/

local notation "AlgState" => AlgState (τ := τ) (ℓ := AstPath)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := AstPath)
local notation "FlowModelImpl" => FlowModelImpl (τ := τ) (ℓ := AstPath)
local notation "PromotionKeyStore" => PromotionKeyStore (τ := τ) (ℓ := AstPath)
local notation "Reference" => Reference (τ := τ) (ℓ := AstPath)
local notation "ReferenceImpl" => ReferenceImpl (ℓ := AstPath)

/-
The next two lemmas are stated at `ℓ := AstPath`, rather than for any `ℓ`, because their `match`es
must be the very ones in `elabExprImpl`. Lean shares the auxiliary definition of a `match` between
`match`es that elaborate to the same closed term, and a `match` on `Option (ReferenceImpl ℓ)`
doesn't elaborate to the same term as one on `Option (ReferenceImpl AstPath)`. A stuck `match`
doesn't unfold, so differing auxiliary definitions wouldn't be recognized as equal.
-/

/--
The `as` elaboration case's call to `tryPromoteForTypeCast`, including the check for a missing
reference that guards it, refines the specification's `FlowModel.tryPromote`.
-/
theorem FlowModelImpl.refines.tryPromoteForTypeCast?
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {refI? : Option ReferenceImpl} {ref? : Option Reference}
    (hrefs : Option.Rel (fun rI r => rI.refines ks r) refI? ref?) (previousType T : τ) :
    (match refI? with
      | some ref => fmI.tryPromoteForTypeCast ref previousType T
      | none => fmI).refines ks (fm.tryPromote ref? previousType T) := by
  cases hrefs
  case none => exact hrefines
  case some rI r hr => exact hrefines.tryPromoteForTypeCast hwf hr previousType T

/--
The null check elaboration case's call to `tryMarkNonNullable`, including the check for a missing
reference that guards it, refines the specification's `FlowModel.promoteToNonNull`.
-/
theorem FlowModelImpl.refines.tryMarkNonNullable?
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {refI? : Option ReferenceImpl} {ref? : Option Reference}
    (hrefs : Option.Rel (fun rI r => rI.refines ks r) refI? ref?) (previousType : τ) :
    (match refI? with
      | some ref => fmI.tryMarkNonNullable ref previousType
      | none => fmI).refines ks (fm.promoteToNonNull ref? previousType) := by
  cases hrefs
  case none => exact hrefines
  case some rI r hr => exact hrefines.tryMarkNonNullable hwf hr previousType

/--
`elabExprImpl.Correctness π e` says that `elabExprImpl` is complete and sound with respect to
`ElabExpr` for the expression `e` at AST path `π`.

The path is a parameter, rather than being fixed for the whole proof, because the proof for a node
relies on the proofs for its children, which are at different paths.
-/
structure elabExprImpl.Correctness (π : AstPath) (e : Expr) : Prop where
  complete : ∀ {fm₀ m em} {s₀ : AlgState}, s₀.refines fm₀ →
    ElabExpr π fm₀ e m em → ∃ s emI,
      elabExprImpl e ⟨π⟩ s₀ = Except.ok ((m, emI), s) ∧
      s₀.promotionKeyStore.Extends s.promotionKeyStore ∧
      s.refines em.fm_after ∧ emI.refines s.promotionKeyStore s.current em
  sound : ∀ {fm₀ m emI s} {s₀ : AlgState}, s₀.refines fm₀ →
      elabExprImpl e ⟨π⟩ s₀ = Except.ok ((m, emI), s) → ∃ em,
      ElabExpr π fm₀ e m em ∧ s₀.promotionKeyStore.Extends s.promotionKeyStore ∧
      s.refines em.fm_after ∧ emI.refines s.promotionKeyStore s.current em

theorem elabExprImpl.correct.var {π} (v : Variable) :
    elabExprImpl.Correctness (τ := τ) π (.var v) := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases helab; case var pm T hT hlookup =>
    subst hT
    simp only [ExprModel.simple_after]
    obtain ⟨k, ks₁, hr, hk, hext, hrefines₁⟩ := hrefines₀.keyForVariable v
    cases hrefines₁.current.promotionInfos k (.var v) hk
    case absent hlookupI hlookup' => simp_all
    case present pmI pm' hlookupI hlookup' hrefines_pm =>
      have hpm : pm' = pm := by simp_all
      subst hpm
      refine ⟨{ s₀ with promotionKeyStore := ks₁ },
        ⟨pm'.currentType v.type, some ⟨k, pmI.version?.map (⟨·, []⟩)⟩, none⟩, ?_, hext, hrefines₁,
        ExprModelImpl.refines.noBoolInfo hrefines₁.current _
          (.some ⟨hk, by simp [hrefines_pm.version?]⟩)⟩
      simp [elabExprImpl, hr, hlookupI, hrefines_pm.currentTypes]
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    obtain ⟨k, ks₁, hr, hk, hext, hrefines₁⟩ := hrefines₀.keyForVariable v
    simp only [elabExprImpl, AlgM_bind_eq, keyForVariableM_eq, AlgM_get_eq, hr] at hok
    cases hrefines₁.current.promotionInfos k (.var v) hk
    case absent hlookupI hlookup => simp_all
    case present pmI pm hlookupI hlookup hrefines_pm =>
      simp [hlookupI, hrefines_pm.currentTypes] at hok
      rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
      refine ⟨⟨pm.currentType v.type, some (.var v pm.version?), fm₀, fm₀⟩,
        ElabExpr.var hlookup rfl, hext, ?_,
        ExprModelImpl.refines.noBoolInfo hrefines₁.current _
          (.some ⟨hk, by simp [hrefines_pm.version?]⟩)⟩
      simp only [ExprModel.simple_after]
      exact hrefines₁

/--
A property read is correct if the read of its target is: the target's reference is passed to
`handlePropertyM`, which does what `ElabExpr.propertyGet` prescribes.
-/
theorem elabExprImpl.correct.propertyGet {π} (e₁ : Expr) (p : Property)
    (hcorrect₁ : elabExprImpl.Correctness (0 :: π) e₁) :
    elabExprImpl.Correctness π (e₁.property p) := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases helab; case propertyGet m₁ em₁ ref? T helab₁ href hT =>
    subst href hT
    obtain ⟨s₁, emI₁, hok₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.complete hrefines₀ helab₁
    obtain ⟨s₂, refI?, hok₂, hext₂, hrefines₂, hrefs₂⟩ :=
      handlePropertyM.correct (cfg := ⟨π⟩) hrefines₁ hrefines_em₁.ref?s p
    simp only [ExprModel.simple_after]
    refine ⟨s₂, ⟨_, refI?, none⟩, ?_, hext₁.trans hext₂, hrefines₂,
      ExprModelImpl.refines.noBoolInfo hrefines₂.current _ hrefs₂⟩
    simp [elabExprImpl, hok₁, hok₂]
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    simp only [elabExprImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, s₁⟩
    obtain ⟨em₁, helab₁, hext₁, hrefines₁, hrefines_em₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    obtain ⟨s₂, refI?, hok₂, hext₂, hrefines₂, hrefs₂⟩ :=
      handlePropertyM.correct (cfg := ⟨π⟩) hrefines₁ hrefines_em₁.ref?s p
    simp [hok₁, hok₂] at hok
    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
    refine ⟨_, ElabExpr.propertyGet helab₁ rfl rfl, hext₁.trans hext₂, ?_,
      ExprModelImpl.refines.noBoolInfo hrefines₂.current _ hrefs₂⟩
    simp only [ExprModel.simple_after]
    exact hrefines₂

theorem elabExprImpl.correct.nullCheck {π} (e₁ : Expr) (hcorrect₁ :
    elabExprImpl.Correctness (0 :: π) e₁) :
    elabExprImpl.Correctness π e₁.nullCheck := by
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
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π⟩ s₀
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

theorem elabExprImpl.correct.asExpr {π} (e₁ : Expr) T
    (hcorrect₁ : elabExprImpl.Correctness (0 :: π) e₁) :
    elabExprImpl.Correctness π (e₁.as T) := by
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
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π⟩ s₀
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

theorem elabExprImpl.correct.nullLiteral {π} :
    elabExprImpl.Correctness (τ := τ) π .null := by
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

theorem elabExprImpl.correct (π : AstPath) (e : Expr) :
    elabExprImpl.Correctness π e := by
  constructor
  case complete =>
    intro fm₀ m em s₀ hrefines₀ helab
    cases h : e <;> rw [h] at helab
    case var v => apply (elabExprImpl.correct.var v).complete hrefines₀ helab
    case nullCheck e₁ =>
      apply (elabExprImpl.correct.nullCheck e₁ (elabExprImpl.correct (0 :: π) e₁)).complete
        hrefines₀ helab
    case as e₁ T =>
      apply (elabExprImpl.correct.asExpr e₁ T (elabExprImpl.correct (0 :: π) e₁)).complete
        hrefines₀ helab
    case null => apply elabExprImpl.correct.nullLiteral.complete hrefines₀ helab
    case property e₁ p =>
      apply (elabExprImpl.correct.propertyGet e₁ p (elabExprImpl.correct (0 :: π) e₁)).complete
        hrefines₀ helab
  case sound =>
    intro fm₀ m emI s s₀ hrefines₀ hok
    cases h : e <;> rw [h] at hok
    case var v => apply (elabExprImpl.correct.var v).sound hrefines₀ hok
    case nullCheck e₁ =>
      apply (elabExprImpl.correct.nullCheck e₁ (elabExprImpl.correct (0 :: π) e₁)).sound
        hrefines₀ hok
    case as e₁ T =>
      apply (elabExprImpl.correct.asExpr e₁ T (elabExprImpl.correct (0 :: π) e₁)).sound
        hrefines₀ hok
    case null => apply elabExprImpl.correct.nullLiteral.sound hrefines₀ hok
    case property e₁ p =>
      apply (elabExprImpl.correct.propertyGet e₁ p (elabExprImpl.correct (0 :: π) e₁)).sound
        hrefines₀ hok

/--
`elabStmtImpl.Correctness π s` says that `elabStmtImpl` is complete and sound with respect to
`ElabStmt` for the statement `s` at AST path `π`.
-/
structure elabStmtImpl.Correctness (π : AstPath) (s : Stmt) : Prop where
  complete :
    ∀ {fm₀ m fm} {s₀ : AlgState}, s₀.refines fm₀ →
      ElabStmt π fm₀ s m fm →
      ∃ sI, elabStmtImpl s ⟨π⟩ s₀ = Except.ok (m, sI) ∧
        s₀.promotionKeyStore.Extends sI.promotionKeyStore ∧ sI.refines fm
  sound :
    ∀ {fm₀ m sI} {s₀ : AlgState},
      s₀.refines fm₀ → elabStmtImpl s ⟨π⟩ s₀ = Except.ok (m, sI) →
      ∃ fm, ElabStmt π fm₀ s m fm ∧
        s₀.promotionKeyStore.Extends sI.promotionKeyStore ∧ sI.refines fm

/--
`elabStmtsImpl.Correctness π ss` says that `elabStmtsImpl` is complete and sound with respect to
`ElabStmts` for the statement list `ss` at AST path `π`.
-/
structure elabStmtsImpl.Correctness (π : AstPath) (ss : List Stmt) : Prop where
  complete :
    ∀ {fm₀ m fm} {s₀ : AlgState}, s₀.refines fm₀ →
      ElabStmts π fm₀ ss m fm →
      ∃ sI, elabStmtsImpl ss ⟨π⟩ s₀ = Except.ok (m, sI) ∧
        s₀.promotionKeyStore.Extends sI.promotionKeyStore ∧ sI.refines fm
  sound :
    ∀ {fm₀ m sI} {s₀ : AlgState},
      s₀.refines fm₀ → elabStmtsImpl ss ⟨π⟩ s₀ = Except.ok (m, sI) →
      ∃ fm, ElabStmts π fm₀ ss m fm ∧
        s₀.promotionKeyStore.Extends sI.promotionKeyStore ∧ sI.refines fm

theorem elabStmtImpl.correct.declare {π} (n : String) (T : τ) :
    elabStmtImpl.Correctness π (.declare n T) := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases helab; case declare =>
    obtain ⟨k, ks₁, hr, hk, hext, hrefines₁⟩ := hrefines₀.keyForVariable ⟨n, T⟩
    refine ⟨⟨⟨s₀.current.promotionInfo.insert k
          ⟨[], [], true, false, some (ValueVersion.root π)⟩⟩, ks₁⟩, ?_, hext, ⟨hrefines₁.wf,
      hrefines₁.current.insert hrefines₁.wf hk (PromotionModelImpl.refines.declared _)⟩⟩
    simp [elabStmtImpl, hr]
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    obtain ⟨k, ks₁, hr, hk, hext, hrefines₁⟩ := hrefines₀.keyForVariable ⟨n, T⟩
    simp [elabStmtImpl, hr] at hok
    rcases hok with ⟨rfl, rfl⟩
    refine ⟨_, ElabStmt.declare π fm₀ n T, hext, ⟨hrefines₁.wf,
      hrefines₁.current.insert hrefines₁.wf hk (PromotionModelImpl.refines.declared _)⟩⟩

theorem elabStmtImpl.correct.exprStmt {π}
    (e₁ : Expr) (hcorrect₁ : elabExprImpl.Correctness (0 :: π) e₁) :
    elabStmtImpl.Correctness π (.exprStmt e₁) := by
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
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, s₁⟩
    simp [hok₁] at hok
    rcases hok with ⟨rfl, rfl⟩
    obtain ⟨em₁, helab₁, hext₁, hrefines₁, -⟩ := hcorrect₁.sound hrefines₀ hok₁
    exact ⟨_, ElabStmt.exprStmt helab₁, hext₁, hrefines₁⟩

theorem elabStmtImpl.correct.ifStmt {π}
    (e₁ : Expr) (s₂ s₃ : Stmt)
    (hcorrect₁ : elabExprImpl.Correctness (0 :: π) e₁)
    (hcorrect₂ : elabStmtImpl.Correctness (1 :: π) s₂)
    (hcorrect₃ : elabStmtImpl.Correctness (2 :: π) s₃) :
    elabStmtImpl.Correctness π (.ifStmt e₁ s₂ s₃) := by
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
    -- Analyze the `else` branch, starting from the flow model for when the condition is false.  That
    -- flow model was computed before the `then` branch was analyzed, which may have allocated keys,
    -- so its refinement has to be carried over to the enlarged key store.
    obtain ⟨sI₃, hok₃, hext₃, hrefines₃⟩ :=
      hcorrect₃.complete
        (s₀ := { sI₂ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).snd })
        ⟨hrefines₂.wf, hrefines_em₁.fm_falses.mono hrefines₂.wf hext₂⟩ helab₃
    -- Likewise, the `then` branch's final flow model has to be carried over to the key store as
    -- enlarged by the `else` branch.
    refine ⟨{ sI₃ with current := sI₂.current.join sI₃.current }, ?_, hext₁.trans (hext₂.trans hext₃),
      ⟨hrefines₃.wf, (hrefines₂.current.mono hrefines₃.wf hext₃).join hrefines₃.current⟩⟩
    have his_boolI : emI₁.type = Γ.bool := hrefines_em₁.types.trans his_bool
    simp [elabStmtImpl, hok₁, his_boolI, hok₂, hok₃]
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    simp only [elabStmtImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabExprImpl e₁ ⟨0 :: π⟩ s₀
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
    cases hok₂ : elabStmtImpl s₂ ⟨1 :: π⟩
        { s₁ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).fst }
    case error => simp [hok₂] at hok
    case ok result₂ =>
    rcases result₂ with ⟨m₂, sI₂⟩
    obtain ⟨fm₂, helab₂, hext₂, hrefines₂⟩ :=
      hcorrect₂.sound
        (s₀ := { s₁ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).fst })
        ⟨hrefines₁.wf, hrefines_em₁.fm_trues⟩ hok₂
    cases hok₃ : elabStmtImpl s₃ ⟨2 :: π⟩
        { sI₂ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).snd }
    case error => simp [hok₂, hok₃] at hok
    case ok result₃ =>
    rcases result₃ with ⟨m₃, sI₃⟩
    obtain ⟨fm₃, helab₃, hext₃, hrefines₃⟩ :=
      hcorrect₃.sound
        (s₀ := { sI₂ with current := (emI₁.boolInfo.getD (s₁.current, s₁.current)).snd })
        ⟨hrefines₂.wf, hrefines_em₁.fm_falses.mono hrefines₂.wf hext₂⟩ hok₃
    simp [hok₂, hok₃] at hok
    rcases hok with ⟨rfl, rfl⟩
    exact ⟨fm₂.join fm₃, ElabStmt.ifStmt helab₁ his_bool helab₂ helab₃,
      hext₁.trans (hext₂.trans hext₃),
      ⟨hrefines₃.wf, (hrefines₂.current.mono hrefines₃.wf hext₃).join hrefines₃.current⟩⟩

theorem elabStmtImpl.correct.block {π}
    (ss₁ : List Stmt) (hcorrect₁ : elabStmtsImpl.Correctness (0 :: π) ss₁) :
    elabStmtImpl.Correctness π (.block ss₁) := by
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
    cases hok₁ : elabStmtsImpl ss₁ ⟨0 :: π⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨m₁, sI₁⟩
    simp [hok₁] at hok
    rcases hok with ⟨rfl, rfl⟩
    obtain ⟨fm₁, helab₁, hext₁, hrefines₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    exact ⟨fm₁, ElabStmt.block helab₁, hext₁, hrefines₁⟩

theorem elabStmtsImpl.correct.nil {π} :
    elabStmtsImpl.Correctness (τ := τ) π [] := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases helab; case nil =>
    exact ⟨s₀, by simp [elabStmtsImpl], .refl _, hrefines₀⟩
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok; simp [elabStmtsImpl] at hok
    rcases hok with ⟨rfl, rfl⟩
    exact ⟨fm₀, ElabStmts.nil, .refl _, hrefines₀⟩

theorem elabStmtsImpl.correct.cons {π}
    (s₁ : Stmt) (ss₂ : List Stmt)
    (hcorrect₁ : elabStmtImpl.Correctness (0 :: π) s₁)
    (hcorrect₂ : elabStmtsImpl.Correctness (1 :: π) ss₂) :
    elabStmtsImpl.Correctness π (s₁ :: ss₂) := by
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
    simp only [elabStmtsImpl, AlgM_bind_eq, withChild_eq] at hok
    cases hok₁ : elabStmtImpl s₁ ⟨0 :: π⟩ s₀
    case error => simp [hok₁] at hok
    case ok result₁ =>
    rcases result₁ with ⟨m₁, sI₁⟩
    obtain ⟨fm₁, helab₁, hext₁, hrefines₁⟩ := hcorrect₁.sound hrefines₀ hok₁
    cases hok₂ : elabStmtsImpl ss₂ ⟨1 :: π⟩ sI₁
    case error => simp [hok₁, hok₂] at hok
    case ok result₂ =>
    rcases result₂ with ⟨m₂, sI₂⟩
    obtain ⟨fm₂, helab₂, hext₂, hrefines₂⟩ := hcorrect₂.sound hrefines₁ hok₂
    simp [hok₁, hok₂] at hok
    rcases hok with ⟨rfl, rfl⟩
    exact ⟨fm₂, ElabStmts.cons helab₁ helab₂, hext₁.trans hext₂, hrefines₂⟩

mutual
theorem elabStmtImpl.correct (π : AstPath) (s : Stmt) :
    elabStmtImpl.Correctness π s := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases h : s <;> rw [h] at helab
    case declare n T => apply (elabStmtImpl.correct.declare n T).complete hrefines₀ helab
    case exprStmt e₁ =>
      apply (elabStmtImpl.correct.exprStmt e₁ (elabExprImpl.correct (0 :: π) e₁)).complete
        hrefines₀ helab
    case ifStmt e₁ s₂ s₃ =>
      apply
        (elabStmtImpl.correct.ifStmt e₁ s₂ s₃ (elabExprImpl.correct (0 :: π) e₁)
            (elabStmtImpl.correct (1 :: π) s₂) (elabStmtImpl.correct (2 :: π) s₃)).complete
          hrefines₀ helab
    case block ss =>
      apply (elabStmtImpl.correct.block ss (elabStmtsImpl.correct (0 :: π) ss)).complete
        hrefines₀ helab
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    cases h : s <;> rw [h] at hok
    case declare n T => apply (elabStmtImpl.correct.declare n T).sound hrefines₀ hok
    case exprStmt e₁ =>
      apply (elabStmtImpl.correct.exprStmt e₁ (elabExprImpl.correct (0 :: π) e₁)).sound
        hrefines₀ hok
    case ifStmt e₁ s₂ s₃ =>
      apply
        (elabStmtImpl.correct.ifStmt e₁ s₂ s₃ (elabExprImpl.correct (0 :: π) e₁)
            (elabStmtImpl.correct (1 :: π) s₂) (elabStmtImpl.correct (2 :: π) s₃)).sound
          hrefines₀ hok
    case block ss =>
      apply (elabStmtImpl.correct.block ss (elabStmtsImpl.correct (0 :: π) ss)).sound
        hrefines₀ hok

theorem elabStmtsImpl.correct (π : AstPath) (ss : List Stmt) :
    elabStmtsImpl.Correctness π ss := by
  constructor
  case complete =>
    intro fm₀ m fm s₀ hrefines₀ helab
    cases h : ss <;> rw [h] at helab
    case nil => apply elabStmtsImpl.correct.nil.complete hrefines₀ helab
    case cons s ss =>
      apply
        (elabStmtsImpl.correct.cons s ss (elabStmtImpl.correct (0 :: π) s)
            (elabStmtsImpl.correct (1 :: π) ss)).complete
          hrefines₀ helab
  case sound =>
    intro fm₀ m sI s₀ hrefines₀ hok
    cases h : ss <;> rw [h] at hok
    case nil => apply elabStmtsImpl.correct.nil.sound hrefines₀ hok
    case cons s ss =>
      apply
        (elabStmtsImpl.correct.cons s ss (elabStmtImpl.correct (0 :: π) s)
            (elabStmtsImpl.correct (1 :: π) ss)).sound
          hrefines₀ hok
end

end FlowAnalysis
