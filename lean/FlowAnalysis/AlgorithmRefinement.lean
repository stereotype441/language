module
public import FlowAnalysis.Algorithm
public import FlowAnalysis.Elaboration

/-!
# Refinement between the algorithm's flow models and the specification's

This module defines the refinement relation `FlowModelImpl.refines`, which says when the
algorithm's flow model (`FlowModelImpl`), whose integer promotion keys are interpreted by a
promotion key store, faithfully represents the specification's flow model (`FlowModel`), and
proves that the algorithm's operations on flow models refine the specification's: promotion,
declaration and assignment, and join. `FlowAnalysis.AlgorithmTheorems` builds on these to prove the
algorithm correct.

The two flow models name the locations they track differently (see `Key`):

- A variable is named by its promotion key, which the key store relates to the variable's
  declaration (`PromotionKeyStore.variableKeys`), and in the specification by `Key.var`.
- A property is named, as in Dart, by a promotion key found in the property map of the value
  version of its target, so the key for `x._f._g` is found by following the path `[_f, _g]` from
  the version that `x` holds (`PromotionKeyStore.propertyAt`). The specification names it by the
  root variable and the path: `Key.property x [_f, _g]`.

So the relation is *relative to the flow model*: which specification key a property's promotion key
stands for depends on which variable currently holds the version it was found under. Promotion keys
that can't be reached from any variable's current version (for example, those of the properties of
a variable's old value, after an assignment) stand for nothing, and the algorithm's promotion models
for them are ignored. The specification, for its part, erases the property targets rooted at a
variable when it's assigned (`FlowModel.eraseRooted`).

For this to work, the relation also requires that the variables hold distinct versions, none of
which is the version of a property: then distinct paths from distinct variables reach distinct
promotion keys (`PromotionKeyStore.WellFormed.propertyAt_inj`), so promoting one property target
can't affect another.

The hardest proof is that join preserves refinement (`FlowModelImpl.refines.join`). Where a variable
holds the same version on both paths being joined, the algorithm joins its properties' promotion
models pointwise, as the specification does. Where it holds different versions, the algorithm gives
it a new version, and re-keys the properties that both old versions have (`joinProperties`); the
proof shows, by induction over the recursion, that the new version's paths lead to promotion keys
whose promotion models are the joins of those found along the same paths from the old versions,
which is what the specification's pointwise join of `Key.property` entries computes.
-/

namespace FlowAnalysis
open DartLang

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "PromotionModel" => PromotionModel (τ := τ)
local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ)
local notation "FlowModelImpl" => FlowModelImpl (τ := τ)

variable {ℓ : Type}

local notation "FlowModel" => FlowModel (τ := τ) (ℓ := ℓ)
local notation "Key" => Key (ℓ := ℓ)
local notation "PromotionKeyStore" => PromotionKeyStore (ℓ := ℓ)
local notation "Reference" => Reference (ℓ := ℓ)

/-! ### The refinement relation -/

/--
`fmI.rootVersion ks decl` is the value version that the variable declared at `decl` holds in the
algorithm's flow model `fmI`, whose promotion keys are interpreted by the key store `ks`; or `none`,
if the variable has no promotion key or promotion model, or is write captured.
-/
@[expose]
public def FlowModelImpl.rootVersion (fmI : FlowModelImpl) (ks : PromotionKeyStore) (decl : ℓ) :
    Option ValueVersionImpl :=
  (ks.variableKeys decl).bind fun k => (fmI.promotionInfo[k]?).bind (·.version?)

/--
`fmI.PromotionInfoRefinesAt fm k key` says that the `promotionInfo` fields of the algorithm's flow
model `fmI` and the specification's flow model `fm` agree about the promotion key `k`, which stands
for the specification key `key`: either neither flow model has an entry for it, or both do, and the
algorithm's promotion model refines the specification's.
-/
public inductive FlowModelImpl.PromotionInfoRefinesAt (fmI : FlowModelImpl)
    (fm : FlowModel) (k : PromotionKey) (key : Key) : Prop where
  /-- Neither flow model has an entry. -/
  | absent (hlookupI : fmI.promotionInfo[k]? = none) (hlookup : fm.promotionInfo key = none)
  /-- Both flow models have an entry, and their promotion models are related by `refines`. -/
  | present
        {pmI : PromotionModelImpl} {pm : PromotionModel}
        (hlookupI : fmI.promotionInfo[k]? = some pmI)
        (hlookup : fm.promotionInfo key = some pm) (hrefines_pm : pmI.refines pm)

/--
`fmI.PropertyRefinesAt ks fm decl q` says that the algorithm's flow model `fmI` (with key store
`ks`) and the specification's flow model `fm` agree about the property target rooted at `decl` with
path `q`: if the path leads, from the version that `decl` holds, to a property version, they agree
about its promotion key (`PromotionInfoRefinesAt`); and otherwise, the specification has no entry
for it.
-/
@[expose]
public def FlowModelImpl.PropertyRefinesAt (fmI : FlowModelImpl) (ks : PromotionKeyStore)
    (fm : FlowModel) (decl : ℓ) (q : List String) : Prop :=
  match (fmI.rootVersion ks decl).bind (ks.propertyAt · q) with
  | some p => fmI.PromotionInfoRefinesAt fm p.promotionKey (.property decl q)
  | none => fm.promotionInfo (.property decl q) = none

/--
`fmI.refines ks fm` says that the algorithm's flow model `fmI`, whose promotion keys are interpreted
by the key store `ks`, faithfully represents the specification's flow model `fm`.
-/
public structure FlowModelImpl.refines (fmI : FlowModelImpl) (ks : PromotionKeyStore)
    (fm : FlowModel) : Prop where
  /-- The two flow models agree about every variable that has a promotion key. -/
  variableInfos (decl : ℓ) (k : PromotionKey) (hk : ks.variableKeys decl = some k) :
    fmI.PromotionInfoRefinesAt fm k (.var decl)
  /-- The specification records nothing about a variable that has no promotion key. -/
  unallocated (decl : ℓ) (hk : ks.variableKeys decl = none) : fm.promotionInfo (.var decl) = none
  /-- The two flow models agree about every property target (see `PropertyRefinesAt`). -/
  properties (decl : ℓ) (q : List String) : fmI.PropertyRefinesAt ks fm decl q
  /--
  The algorithm's flow model records nothing under a promotion key that hasn't been allocated.
  -/
  beyondEnd (k : PromotionKey) (hk : ks.keys[k]? = none) : fmI.promotionInfo[k]? = none
  /-- Every version that the algorithm's flow model records has been allocated. -/
  versions (k : PromotionKey) (pmI : PromotionModelImpl) (v : ValueVersionImpl)
    (hk : fmI.promotionInfo[k]? = some pmI) (hv : pmI.version? = some v) : v < ks.nextVersion
  /-- No variable holds the version of a property. -/
  roots (decl : ℓ) (v : ValueVersionImpl) (hv : fmI.rootVersion ks decl = some v) : ¬ks.IsChild v
  /-- Distinct variables hold distinct versions. -/
  roots_inj (decl decl' : ℓ) (v : ValueVersionImpl) (hv : fmI.rootVersion ks decl = some v)
    (hv' : fmI.rootVersion ks decl' = some v) : decl = decl'

/--
`rI.refines ks fmI r` says that the algorithm's reference `rI` faithfully represents the
specification's reference `r`, in the algorithm's flow model `fmI` (with key store `ks`) in which
the read happened:
- for a variable, the promotion key is the variable's, the version is the one the variable holds,
  and the specification's reference is tracked exactly when there is a version;
- for a property target, the path leads, from the version that its root holds, to a property
  version, whose promotion key and version the reference records.
-/
@[expose]
public def ReferenceImpl.refines (rI : ReferenceImpl) (ks : PromotionKeyStore)
    (fmI : FlowModelImpl) : Reference → Prop
  | .var decl tracked =>
    ks.variableKeys decl = some rI.promotionKey ∧ rI.version? = fmI.rootVersion ks decl ∧
      tracked = rI.version?.isSome
  | .property root path =>
    ∃ v p, fmI.rootVersion ks root = some v ∧ ks.propertyAt v path = some p ∧
      rI.promotionKey = p.promotionKey ∧ rI.version? = some p.version

/-! ### Basic properties -/

omit Γ in
/-- The root version of a variable whose key is `k` (`hk`) is the version of its model. -/
public theorem FlowModelImpl.rootVersion_eq {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {decl : ℓ} {k : PromotionKey} (hk : ks.variableKeys decl = some k) :
    fmI.rootVersion ks decl = (fmI.promotionInfo[k]?).bind (·.version?) := by
  simp [FlowModelImpl.rootVersion, hk]

omit Γ in
/-- A variable with no key (`hk`) has no root version. -/
public theorem FlowModelImpl.rootVersion_of_none {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {decl : ℓ} (hk : ks.variableKeys decl = none) : fmI.rootVersion ks decl = none := by
  simp [FlowModelImpl.rootVersion, hk]

/--
The algorithm's flow model with no entries refines the specification's initial flow model, relative
to any key store.
-/
public theorem FlowModelImpl.refines.empty {ks : PromotionKeyStore} :
    (.empty : FlowModelImpl).refines ks FlowModel.empty where
  variableInfos _ _ _ := .absent (by simp [FlowModelImpl.empty]) (by simp [FlowModel.empty])
  unallocated _ _ := by simp [FlowModel.empty]
  properties decl q := by
    simp [FlowModelImpl.PropertyRefinesAt, FlowModelImpl.rootVersion, FlowModelImpl.empty,
      FlowModel.empty]
  beyondEnd _ _ := by simp [FlowModelImpl.empty]
  versions _ _ _ hk _ := by simp [FlowModelImpl.empty] at hk
  roots _ _ hv := by simp [FlowModelImpl.rootVersion, FlowModelImpl.empty] at hv
  roots_inj _ _ _ hv _ := by simp [FlowModelImpl.rootVersion, FlowModelImpl.empty] at hv

/--
A specification flow model `fm` refined by an algorithmic flow model `fmI` (`hrefines`) whose
`promotionInfo` is empty (`hempty`) maps every key to `none`.
-/
public theorem FlowModelImpl.refines.eq_none_of_isEmpty {fmI : FlowModelImpl}
    {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hempty : fmI.promotionInfo.isEmpty) (key : Key) : fm.promotionInfo key = none := by
  have hnone : ∀ k, fmI.promotionInfo[k]? = none := fun k => Std.HashMap.getElem?_of_isEmpty hempty
  cases key
  case var decl =>
    cases hk : ks.variableKeys decl
    case none => exact hrefines.unallocated decl hk
    case some k => cases hrefines.variableInfos decl k hk <;> simp_all
  case property root path =>
    have := hrefines.properties root path
    simp only [FlowModelImpl.PropertyRefinesAt, FlowModelImpl.rootVersion, hnone,
      Option.bind_none] at this
    cases ks.variableKeys root <;> simpa using this

/--
Refinement survives the allocation of more keys and versions: if `fmI` refines `fm` relative to `ks`
(`hrefines`), it does so relative to any well-formed (`hwf'`) extension `ks'` of the well-formed
store `ks` (`hwf`, `hext`). The variables keep the versions they hold.

This is what lets a flow model saved before analyzing one branch of an `if` statement be used after
it: the branch may have allocated keys and versions, and added properties to versions the saved
flow model holds; but a key allocated since, whether for a variable or a property, is one that the
saved flow model has no entry for, and the specification has no entry for what it stands for
either: a variable that had no key, or a path that didn't lead anywhere before.
-/
public theorem FlowModelImpl.refines.mono {fmI : FlowModelImpl} {ks ks' : PromotionKeyStore}
    {fm : FlowModel} (hrefines : fmI.refines ks fm) (hwf : ks.WellFormed) (hwf' : ks'.WellFormed)
    (hext : ks.Extends ks') : fmI.refines ks' fm := by
  -- Every variable holds the same version in `ks'` as in `ks`.
  have hroot : ∀ d, fmI.rootVersion ks' d = fmI.rootVersion ks d := by
    intro d
    cases hk : ks.variableKeys d
    case some k =>
      rw [FlowModelImpl.rootVersion_eq hk, FlowModelImpl.rootVersion_eq
        (hext.variableKeys_of_some hwf hwf' hk)]
    case none =>
      rw [FlowModelImpl.rootVersion_of_none hk]
      cases hk' : ks'.variableKeys d
      case none => exact FlowModelImpl.rootVersion_of_none hk'
      case some k' =>
        rw [FlowModelImpl.rootVersion_eq hk',
          hrefines.beyondEnd k' (hext.variableKeys_fresh hwf hwf' hk hk')]
        rfl
  exact {
    variableInfos := fun decl k hk => by
      cases hold : ks.variableKeys decl
      case some k₀ =>
        have := hext.variableKeys_of_some hwf hwf' hold
        rw [hk] at this
        obtain rfl := Option.some.inj this
        exact hrefines.variableInfos decl k hold
      case none =>
        exact .absent (hrefines.beyondEnd k (hext.variableKeys_fresh hwf hwf' hold hk))
          (hrefines.unallocated decl hold)
    unallocated := fun decl hk => by
      apply hrefines.unallocated decl
      cases hold : ks.variableKeys decl
      case none => rfl
      case some k₀ => simp [hext.variableKeys_of_some hwf hwf' hold] at hk
    properties := fun decl q => by
      have := hrefines.properties decl q
      simp only [FlowModelImpl.PropertyRefinesAt, hroot] at this ⊢
      cases hv : fmI.rootVersion ks decl
      case none => simpa [hv] using this
      case some v =>
        simp only [hv, Option.bind_some] at this ⊢
        rcases hext.propertyAt hwf v q with heq | ⟨hnone, hfresh⟩
        · rw [heq]; exact this
        · rw [hnone] at this
          cases hp : ks'.propertyAt v q
          case none => exact this
          case some p => exact .absent (hrefines.beyondEnd _ (hfresh p hp)) this
    beyondEnd := fun k hk => by
      apply hrefines.beyondEnd k
      cases hk' : ks.keys[k]?
      case none => rfl
      case some o => simp [hext.keys k o hk'] at hk
    versions := fun k pmI v hk hv =>
      Nat.lt_of_lt_of_le (hrefines.versions k pmI v hk hv) hext.nextVersion
    roots := fun decl v hv => by
      rw [hroot] at hv
      have hnot := hrefines.roots decl v hv
      -- `v` was allocated, so a property added since, whose version is fresh, can't be `v`.
      have hlt : v < ks.nextVersion := by
        simp only [FlowModelImpl.rootVersion, Option.bind_eq_some_iff] at hv
        obtain ⟨k, -, pmI, hk, hv⟩ := hv
        exact hrefines.versions k pmI v hk hv
      rintro ⟨u, n, p, hp, rfl⟩
      cases hold : (ks.promotableProperties u)[n]?
      case some p₀ =>
        have := hext.properties u n p₀ hold
        rw [hp] at this
        obtain rfl := Option.some.inj this
        exact hnot ⟨u, n, _, hold, rfl⟩
      case none =>
        exact absurd hlt (Nat.not_lt_of_le (hext.properties_fresh u n p hold hp).2)
    roots_inj := fun decl decl' v hv hv' =>
      hrefines.roots_inj decl decl' v (hroot decl ▸ hv) (hroot decl' ▸ hv') }

/--
In a well-formed store (`hwf`), a variable's key (`hk`) is never a property's key (`hp`):
`p.promotionKey ≠ k`.
-/
public theorem PromotionKeyStore.WellFormed.propertyAt_ne_variableKey {ks : PromotionKeyStore}
    (hwf : ks.WellFormed) {decl : ℓ} {k : PromotionKey} (hk : ks.variableKeys decl = some k)
    {v : ValueVersionImpl} {q : List String} {p : PropertyValueVersionImpl}
    (hp : ks.propertyAt v q = some p) : p.promotionKey ≠ k := by
  intro heq
  obtain ⟨u, n, hun⟩ := PromotionKeyStore.mem_of_propertyAt hp
  have h₁ := hwf.properties_key u n p hun
  rw [heq, hwf.variableKeys_keys decl k hk] at h₁
  cases h₁

/--
In a well-formed store (`hwf`), distinct variables have distinct keys: if `decl` and `decl'` both
have the key `k` (`hk`, `hk'`), then `decl = decl'`.
-/
public theorem PromotionKeyStore.WellFormed.variableKeys_inj {ks : PromotionKeyStore}
    (hwf : ks.WellFormed) {decl decl' : ℓ} {k : PromotionKey} (hk : ks.variableKeys decl = some k)
    (hk' : ks.variableKeys decl' = some k) : decl = decl' := by
  have h := hwf.variableKeys_keys decl k hk
  rw [hwf.variableKeys_keys decl' k hk'] at h
  cases h
  rfl

/-- A property's key is allocated (`ks.keys[p.promotionKey]? ≠ none`). -/
public theorem PromotionKeyStore.WellFormed.propertyAt_allocated {ks : PromotionKeyStore}
    (hwf : ks.WellFormed) {v : ValueVersionImpl} {q : List String} {p : PropertyValueVersionImpl}
    (hp : ks.propertyAt v q = some p) : ks.keys[p.promotionKey]? ≠ none := by
  obtain ⟨u, n, hun⟩ := PromotionKeyStore.mem_of_propertyAt hp
  simp [hwf.properties_key u n p hun]

/-- A property's version is allocated (`p.version < ks.nextVersion`). -/
public theorem PromotionKeyStore.WellFormed.propertyAt_version {ks : PromotionKeyStore}
    (hwf : ks.WellFormed) {v : ValueVersionImpl} {q : List String} {p : PropertyValueVersionImpl}
    (hp : ks.propertyAt v q = some p) : p.version < ks.nextVersion := by
  obtain ⟨u, n, hun⟩ := PromotionKeyStore.mem_of_propertyAt hp
  exact (hwf.properties_version u n p hun).2

/-- A variable's key is allocated (`ks.keys[k]? ≠ none`). -/
public theorem PromotionKeyStore.WellFormed.variableKey_allocated {ks : PromotionKeyStore}
    (hwf : ks.WellFormed) {decl : ℓ} {k : PromotionKey} (hk : ks.variableKeys decl = some k) :
    ks.keys[k]? ≠ none := by
  simp [hwf.variableKeys_keys decl k hk]

/-! ### Updating a single entry -/

section
variable [DecidableEq ℓ]

/--
Refinement (`hrefines`, relative to a well-formed store, `hwf`) is preserved by replacing the
promotion model of the variable declared at `decl`, whose key is `k` (`hk`), on both sides, provided
the new models are related by `refines` (`hrefines_pm`), and the algorithm's new model holds the
same version as the old one (`hversion`), as a promotion does.
-/
public theorem FlowModelImpl.refines.insertVar {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm : FlowModel} (hrefines : fmI.refines ks fm) (hwf : ks.WellFormed) {decl : ℓ}
    {k : PromotionKey} (hk : ks.variableKeys decl = some k) {pmI : PromotionModelImpl}
    {pm : PromotionModel} (hrefines_pm : pmI.refines pm)
    (hversion : pmI.version? = (fmI.promotionInfo[k]?).bind (·.version?)) :
    (FlowModelImpl.mk (fmI.promotionInfo.insert k pmI)).refines ks (fm.set (.var decl) pm) := by
  -- The update doesn't change the version any variable holds.
  have hroot : ∀ d, (FlowModelImpl.mk (fmI.promotionInfo.insert k pmI)).rootVersion ks d =
      fmI.rootVersion ks d := by
    intro d
    cases hd : ks.variableKeys d
    case none => simp [FlowModelImpl.rootVersion, hd]
    case some k' =>
      simp only [FlowModelImpl.rootVersion, hd, Option.bind_some, Std.HashMap.getElem?_insert,
        beq_iff_eq]
      split
      case isTrue heq => subst heq; simpa using hversion
      case isFalse => rfl
  exact {
    variableInfos := fun d k' hk' => by
      by_cases heq : k = k'
      · subst heq
        obtain rfl := hwf.variableKeys_inj hk hk'
        exact .present (by simp) (by simp) hrefines_pm
      · have hne : decl ≠ d := fun h => heq (by subst h; simpa [hk] using hk')
        cases hrefines.variableInfos d k' hk'
        case absent hlookupI hlookup =>
          exact .absent (by simp [Std.HashMap.getElem?_insert, heq, hlookupI])
            (by simp [hne, hlookup])
        case present hlookupI hlookup hrefines_pm' =>
          exact .present (by simp [Std.HashMap.getElem?_insert, heq, hlookupI])
            (by simp [hne, hlookup]) hrefines_pm'
    unallocated := fun d hd => by
      have hne : decl ≠ d := fun h => by subst h; simp [hk] at hd
      simp [hne, hrefines.unallocated d hd]
    properties := fun d q => by
      have := hrefines.properties d q
      simp only [FlowModelImpl.PropertyRefinesAt, hroot] at this ⊢
      split
      case h_1 p hp =>
        rw [hp] at this
        simp only [Option.bind_eq_some_iff] at hp
        obtain ⟨v, -, hp⟩ := hp
        have hne : k ≠ p.promotionKey := (hwf.propertyAt_ne_variableKey hk hp).symm
        cases this
        case absent hlookupI hlookup =>
          exact .absent (by simp [Std.HashMap.getElem?_insert, hne, hlookupI]) (by simp [hlookup])
        case present hlookupI hlookup hrefines_pm' =>
          exact .present (by simp [Std.HashMap.getElem?_insert, hne, hlookupI]) (by simp [hlookup])
            hrefines_pm'
      case h_2 hp =>
        rw [hp] at this
        simpa using this
    beyondEnd := fun k' hk' => by
      have hne : k ≠ k' := fun h => hwf.variableKey_allocated hk (h ▸ hk')
      simp [Std.HashMap.getElem?_insert, hne, hrefines.beyondEnd k' hk']
    versions := fun k' pmI' v hk' hv => by
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hk'
      split at hk'
      case isTrue heq =>
        cases hk'
        rw [hversion, Option.bind_eq_some_iff] at hv
        obtain ⟨pmI₀, h₀, hv⟩ := hv
        exact hrefines.versions k pmI₀ v h₀ hv
      case isFalse => exact hrefines.versions k' pmI' v hk' hv
    roots := fun d v hv => hrefines.roots d v (hroot d ▸ hv)
    roots_inj := fun d d' v hv hv' =>
      hrefines.roots_inj d d' v (hroot d ▸ hv) (hroot d' ▸ hv') }

/--
Refinement (`hrefines`, relative to a well-formed store, `hwf`) is preserved by replacing the
promotion model of the property target rooted at `decl` with path `q` on both sides, where `decl`
holds the version `v` (`hv`), and the path leads from it to the property version `p` (`hp`), whose
key is the one replaced on the algorithm's side; provided the new models are related by `refines`
(`hrefines_pm`), and the algorithm's new model holds an allocated version, if any (`hversion`).
-/
public theorem FlowModelImpl.refines.insertProperty {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm : FlowModel} (hrefines : fmI.refines ks fm) (hwf : ks.WellFormed) {decl : ℓ}
    {v : ValueVersionImpl} (hv : fmI.rootVersion ks decl = some v) {q : List String}
    {p : PropertyValueVersionImpl} (hp : ks.propertyAt v q = some p) {pmI : PromotionModelImpl}
    {pm : PromotionModel} (hrefines_pm : pmI.refines pm)
    (hversion : ∀ w, pmI.version? = some w → w < ks.nextVersion) :
    (FlowModelImpl.mk (fmI.promotionInfo.insert p.promotionKey pmI)).refines ks
      (fm.set (.property decl q) pm) := by
  -- The update doesn't change the version any variable holds, since it isn't a variable's key.
  have hroot : ∀ d, (FlowModelImpl.mk (fmI.promotionInfo.insert p.promotionKey pmI)).rootVersion
      ks d = fmI.rootVersion ks d := by
    intro d
    cases hd : ks.variableKeys d
    case none => simp [FlowModelImpl.rootVersion, hd]
    case some k' =>
      have hne : p.promotionKey ≠ k' := hwf.propertyAt_ne_variableKey hd hp
      simp [FlowModelImpl.rootVersion, hd, Std.HashMap.getElem?_insert, hne]
  exact {
    variableInfos := fun d k' hk' => by
      have hne : p.promotionKey ≠ k' := hwf.propertyAt_ne_variableKey hk' hp
      cases hrefines.variableInfos d k' hk'
      case absent hlookupI hlookup =>
        exact .absent (by simp [Std.HashMap.getElem?_insert, hne, hlookupI]) (by simp [hlookup])
      case present hlookupI hlookup hrefines_pm' =>
        exact .present (by simp [Std.HashMap.getElem?_insert, hne, hlookupI]) (by simp [hlookup])
          hrefines_pm'
    unallocated := fun d hd => by simp [hrefines.unallocated d hd]
    properties := fun d q' => by
      have := hrefines.properties d q'
      simp only [FlowModelImpl.PropertyRefinesAt, hroot] at this ⊢
      split
      case h_1 p' hp' =>
        rw [hp'] at this
        simp only [Option.bind_eq_some_iff] at hp'
        obtain ⟨v', hv', hp'⟩ := hp'
        by_cases hkeq : p.promotionKey = p'.promotionKey
        · -- The same key: by injectivity, the same property target.
          obtain ⟨rfl, rfl⟩ := hwf.propertyAt_inj (hrefines.roots decl v hv)
            (hrefines.roots d v' hv') hp hp' hkeq
          obtain rfl := hrefines.roots_inj decl d v hv hv'
          rw [hp] at hp'
          obtain rfl := Option.some.inj hp'
          exact .present (by simp) (by simp) hrefines_pm
        · have hne : (Key.property decl q : Key) ≠ .property d q' := by
            rintro ⟨⟩
            rw [hv] at hv'
            obtain rfl := Option.some.inj hv'
            rw [hp] at hp'
            obtain rfl := Option.some.inj hp'
            exact hkeq rfl
          cases this
          case absent hlookupI hlookup =>
            exact .absent (by simp [Std.HashMap.getElem?_insert, hkeq, hlookupI])
              (by simp [hne, hlookup])
          case present hlookupI hlookup hrefines_pm' =>
            exact .present (by simp [Std.HashMap.getElem?_insert, hkeq, hlookupI])
              (by simp [hne, hlookup]) hrefines_pm'
      case h_2 hp' =>
        rw [hp'] at this
        have hne : (Key.property decl q : Key) ≠ .property d q' := by
          rintro ⟨⟩
          simp [hv, hp] at hp'
        simp [hne, this]
    beyondEnd := fun k' hk' => by
      have hne : p.promotionKey ≠ k' := fun h => hwf.propertyAt_allocated hp (h ▸ hk')
      simp [Std.HashMap.getElem?_insert, hne, hrefines.beyondEnd k' hk']
    versions := fun k' pmI' w hk' hw => by
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hk'
      split at hk'
      case isTrue => cases hk'; exact hversion w hw
      case isFalse => exact hrefines.versions k' pmI' w hk' hw
    roots := fun d w hw => hrefines.roots d w (hroot d ▸ hw)
    roots_inj := fun d d' w hw hw' =>
      hrefines.roots_inj d d' w (hroot d ▸ hw) (hroot d' ▸ hw') }

/--
Refinement (`hrefines`, relative to a well-formed store, `hwf`) is preserved by giving the variable
declared at `decl`, whose key is `k` (`hk`), a new value, as a declaration or an assignment does: on
the algorithm's side, its promotion model is replaced by `pmI`, which holds no version, or the
version that `ks.newVersion` allocates (`hversion`); on the specification's side, every property
target rooted at `decl` is forgotten (`FlowModel.eraseRooted`), and its promotion model is replaced
by `pm`, which `pmI` refines (`hrefines_pm`). The result is relative to the store after the
allocation.

The old value's properties stay in the algorithm's flow model, but the new version has no
properties, so nothing can reach them from `decl`.
-/
public theorem FlowModelImpl.refines.insertFresh {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm : FlowModel} (hrefines : fmI.refines ks fm) (hwf : ks.WellFormed) {decl : ℓ}
    {k : PromotionKey} (hk : ks.variableKeys decl = some k) {pmI : PromotionModelImpl}
    {pm : PromotionModel} (hrefines_pm : pmI.refines pm)
    (hversion : pmI.version? = none ∨ pmI.version? = some ks.nextVersion) :
    (FlowModelImpl.mk (fmI.promotionInfo.insert k pmI)).refines ks.newVersion.2
      ((fm.eraseRooted decl).set (.var decl) pm) := by
  let fmI' : FlowModelImpl := ⟨fmI.promotionInfo.insert k pmI⟩
  -- The new flow model's versions.
  have hroot_decl : fmI'.rootVersion ks.newVersion.2 decl = pmI.version? := by
    simp [fmI', FlowModelImpl.rootVersion, PromotionKeyStore.newVersion, hk]
  have hroot : ∀ d, d ≠ decl → fmI'.rootVersion ks.newVersion.2 d = fmI.rootVersion ks d := by
    intro d hne
    cases hd : ks.variableKeys d
    case none => simp [FlowModelImpl.rootVersion, PromotionKeyStore.newVersion, hd]
    case some k' =>
      have hk' : k ≠ k' := fun h => hne (hwf.variableKeys_inj hd (h ▸ hk))
      simp [fmI', FlowModelImpl.rootVersion, PromotionKeyStore.newVersion, hd,
        Std.HashMap.getElem?_insert, hk']
  -- An old version is allocated, so it isn't the new one.
  have hold_lt : ∀ d w, fmI.rootVersion ks d = some w → w < ks.nextVersion := by
    intro d w hw
    simp only [FlowModelImpl.rootVersion, Option.bind_eq_some_iff] at hw
    obtain ⟨k', -, pmI', hk', hw⟩ := hw
    exact hrefines.versions k' pmI' w hk' hw
  have hpropertyAt : ∀ w q, ks.newVersion.2.propertyAt w q = ks.propertyAt w q :=
    PromotionKeyStore.propertyAt_eq_of_promotableProperties_eq rfl
  -- The new version has no properties, and isn't a property's version.
  have hnew_none : ∀ q, ks.propertyAt ks.nextVersion q = none := by
    intro q
    cases q with
    | nil => simp
    | cons n q => cases q <;> simp [hwf.properties_beyond _ n (Nat.le_refl _)]
  have hnew_child : ¬ks.IsChild ks.nextVersion := by
    rintro ⟨u, n, p, hp, hpv⟩
    exact absurd (hwf.properties_version u n p hp).2 (by rw [hpv]; exact Nat.lt_irrefl _)
  have hversion' : ∀ w, pmI.version? = some w → w = ks.nextVersion := by
    intro w hw
    rcases hversion with h | h <;> rw [h] at hw <;> cases hw
    rfl
  exact {
    variableInfos := fun d k' hk' => by
      change ks.variableKeys d = some k' at hk'
      by_cases heq : k = k'
      · subst heq
        obtain rfl := hwf.variableKeys_inj hk hk'
        exact .present (by simp) (by simp) hrefines_pm
      · have hne : decl ≠ d := fun h => heq (by subst h; simpa [hk] using hk')
        cases hrefines.variableInfos d k' hk'
        case absent hlookupI hlookup =>
          exact .absent (by simp [Std.HashMap.getElem?_insert, heq, hlookupI])
            (by simp [hne, hlookup])
        case present hlookupI hlookup hrefines_pm' =>
          exact .present (by simp [Std.HashMap.getElem?_insert, heq, hlookupI])
            (by simp [hne, hlookup]) hrefines_pm'
    unallocated := fun d hd => by
      change ks.variableKeys d = none at hd
      have hne : decl ≠ d := fun h => by subst h; simp [hk] at hd
      simp [hne, hrefines.unallocated d hd]
    properties := fun d q => by
      simp only [FlowModelImpl.PropertyRefinesAt, hpropertyAt]
      by_cases hd : d = decl
      · subst hd
        rw [hroot_decl]
        have hspec : ((fm.eraseRooted d).set (.var d) pm).promotionInfo (.property d q) = none := by
          simp
        rcases hversion with h | h
        · simp [h]
        · simp [h, hnew_none]
      · rw [hroot d hd]
        have := hrefines.properties d q
        simp only [FlowModelImpl.PropertyRefinesAt] at this
        have hspec : ((fm.eraseRooted decl).set (.var decl) pm).promotionInfo (.property d q) =
            fm.promotionInfo (.property d q) := by
          simp [hd]
        rw [hspec]
        split
        case h_1 p hp =>
          rw [hp] at this
          simp only [Option.bind_eq_some_iff] at hp
          obtain ⟨v, -, hp⟩ := hp
          have hne : k ≠ p.promotionKey := (hwf.propertyAt_ne_variableKey hk hp).symm
          cases this
          case absent hlookupI hlookup =>
            exact .absent (by simp [Std.HashMap.getElem?_insert, hne, hlookupI])
              (hspec ▸ hlookup)
          case present hlookupI hlookup hrefines_pm' =>
            exact .present (by simp [Std.HashMap.getElem?_insert, hne, hlookupI])
              (hspec ▸ hlookup) hrefines_pm'
        case h_2 hp =>
          rw [hp] at this
          exact this
    beyondEnd := fun k' hk' => by
      change ks.keys[k']? = none at hk'
      have hne : k ≠ k' := fun h => hwf.variableKey_allocated hk (h ▸ hk')
      simp [Std.HashMap.getElem?_insert, hne, hrefines.beyondEnd k' hk']
    versions := fun k' pmI' w hk' hw => by
      change w < ks.nextVersion + 1
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hk'
      split at hk'
      case isTrue =>
        cases hk'
        rw [hversion' w hw]
        exact Nat.lt_succ_self _
      case isFalse => exact Nat.lt_succ_of_lt (hrefines.versions k' pmI' w hk' hw)
    roots := fun d w hw => by
      change ¬ks.IsChild w
      by_cases hd : d = decl
      · subst hd
        rw [hroot_decl] at hw
        rw [hversion' w hw]
        exact hnew_child
      · rw [hroot d hd] at hw
        exact hrefines.roots d w hw
    roots_inj := fun d d' w hw hw' => by
      by_cases hd : d = decl <;> by_cases hd' : d' = decl
      · rw [hd, hd']
      · subst hd
        rw [hroot_decl] at hw
        rw [hroot d' hd'] at hw'
        have := hold_lt d' w hw'
        rw [hversion' w hw] at this
        exact absurd this (Nat.lt_irrefl _)
      · subst hd'
        rw [hroot_decl] at hw'
        rw [hroot d hd] at hw
        have := hold_lt d w hw
        rw [hversion' w hw'] at this
        exact absurd this (Nat.lt_irrefl _)
      · rw [hroot d hd] at hw
        rw [hroot d' hd'] at hw'
        exact hrefines.roots_inj d d' w hw hw' }

/-! ### Promotion -/

/--
`finishTypeTest` refines the specification's promotion of the location that a reference `r` reads,
when the reference `rI` refines `r` (`hr`) and the promotion is one the algorithm has checked is
valid (`hchain`), given refinement of the flow model (`hrefines`) relative to a well-formed key
store (`hwf`), a promotion model `pmI` that refines `pm` (`hrefines_pm`), that isn't write captured
(`hwc`), and that is the one `infoFor` supplies on both sides (`hinfoI`, `hinfo`).
-/
theorem FlowModelImpl.refines.finishTypeTest
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {rI : ReferenceImpl} {r : Reference} (hr : rI.refines ks fmI r)
    {pmI : PromotionModelImpl} {pm : PromotionModel} (hrefines_pm : pmI.refines pm)
    (hinfoI : fmI.infoFor rI = some pmI) (hinfo : fm.infoFor r = some pm) {T : τ}
    (hchain : isPromotionChain (pmI.promotedTypes ++ [T])) (hwc : ¬pm.writeCaptured) :
    (fmI.finishTypeTest rI.promotionKey pmI T).refines ks (fm.set r.key (pm.tryPromote T hwc)) := by
  have hpromote := hrefines_pm.promote hchain hwc
  cases r
  case var decl tracked =>
    obtain ⟨hk, hv, -⟩ := hr
    refine hrefines.insertVar hwf hk hpromote ?_
    -- The model `infoFor` supplied is the stored one: a fresh one would need a version, which would
    -- have to be the stored model's.
    simp only [FlowModelImpl.infoFor] at hinfoI
    rw [FlowModelImpl.rootVersion_eq hk] at hv
    split at hinfoI
    case h_1 pmI' hlookup => cases hinfoI; simp [hlookup]
    case h_2 hlookup =>
      rw [hlookup] at hv
      simp [hv] at hinfoI
  case property root path =>
    obtain ⟨v, p, hv, hp, hk, hver⟩ := hr
    simp only [FlowModelImpl.finishTypeTest, hk]
    refine hrefines.insertProperty hwf hv hp hpromote ?_
    -- The version is that of a stored model, or the property's, both allocated.
    intro w hw
    simp only [FlowModelImpl.infoFor] at hinfoI
    split at hinfoI
    case h_1 pmI' hlookup => cases hinfoI; exact hrefines.versions _ _ w hlookup hw
    case h_2 =>
      rw [hver] at hinfoI
      simp only [Option.map_some, Option.some.injEq] at hinfoI
      subst hinfoI
      simp only [PromotionModelImpl.fresh, Option.some.injEq] at hw
      subst hw
      exact hwf.propertyAt_version hp

omit [DecidableEq ℓ] in
/--
The algorithm and the specification find corresponding promotion models for the location that a
reference reads (`FlowModelImpl.infoFor`, `FlowModel.infoFor`), given refinement of the flow model
(`hrefines`) and of the reference (`hr`): either both find none, or both find one, and the
algorithm's refines the specification's
(`Option.Rel PromotionModelImpl.refines (fmI.infoFor rI) (fm.infoFor r)`).
-/
theorem FlowModelImpl.refines.infoFor {fmI : FlowModelImpl} {ks : PromotionKeyStore}
    {fm : FlowModel} (hrefines : fmI.refines ks fm) {rI : ReferenceImpl} {r : Reference}
    (hr : rI.refines ks fmI r) :
    Option.Rel PromotionModelImpl.refines (fmI.infoFor rI) (fm.infoFor r) := by
  cases r
  case var decl tracked =>
    obtain ⟨hk, hv, htracked⟩ := hr
    rw [FlowModelImpl.rootVersion_eq hk] at hv
    simp only [FlowModelImpl.infoFor, FlowModel.infoFor, Reference.key_var, Reference.tracked_var]
    cases hrefines.variableInfos decl _ hk
    case absent hlookupI hlookup =>
      rw [hlookupI] at hv
      simp only [Option.bind_none] at hv
      simp [hlookupI, hlookup, hv, htracked]
    case present pmI pm hlookupI hlookup hrefines_pm =>
      simp only [hlookupI, hlookup]
      exact .some hrefines_pm
  case property root path =>
    obtain ⟨v, p, hv, hp, hk, hver⟩ := hr
    have := hrefines.properties root path
    simp only [FlowModelImpl.PropertyRefinesAt, hv, Option.bind_some, hp] at this
    simp only [FlowModelImpl.infoFor, FlowModel.infoFor, Reference.key_property,
      Reference.tracked_property, hk, hver]
    cases this
    case absent hlookupI hlookup =>
      simp only [hlookupI, hlookup, Option.map_some, ↓reduceIte]
      exact .some (PromotionModelImpl.refines.fresh _)
    case present pmI pm hlookupI hlookup hrefines_pm =>
      simp only [hlookupI, hlookup]
      exact .some hrefines_pm

/--
The algorithm's `tryPromoteForTypeCast` refines the specification's `FlowModel.tryPromote`, given
refinement of the flow model (`hrefines`) relative to a well-formed key store (`hwf`) and of the
reference (`hr`).

`tryMarkNonNullable` differs only in how it computes the type to promote to, so its counterpart,
`FlowModelImpl.refines.tryMarkNonNullable`, is a corollary.
-/
public theorem FlowModelImpl.refines.tryPromoteForTypeCast
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {rI : ReferenceImpl} {r : Reference} (hr : rI.refines ks fmI r)
    (previousType T : τ) :
    (fmI.tryPromoteForTypeCast rI previousType T).refines ks
      (fm.tryPromote (some r) previousType T) := by
  simp only [FlowModelImpl.tryPromoteForTypeCast, FlowModel.tryPromote]
  have hinfo := hrefines.infoFor hr
  cases hinfoI' : fmI.infoFor rI <;> cases hinfoS' : fm.infoFor r <;>
    rw [hinfoI', hinfoS'] at hinfo <;> cases hinfo
  case none.none => exact hrefines
  case some.some pmI pm hrefines_pm =>
    have hinfoI := hinfoI'.symm
    have hinfoS := hinfoS'.symm
    simp only
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
          exact hrefines.finishTypeTest hwf hr hrefines_pm hinfoI.symm hinfoS.symm hchain hwc
        case neg =>
          -- Neither the algorithm nor the spec promoted the location, so neither one changed its
          -- state; for the spec, this is because `PromotionModel.tryPromote` was a no-op, so the
          -- `set` assigned the key the promotion model it already had, or a fresh one, which
          -- the specification treats the same as none.
          simp only [hchain, ↓reduceIte]
          rw [hrefines_pm.tryPromote_eq_self hchain]
          -- A fresh model has no promotions, so `T` could have been appended to it: the model was
          -- the stored one.
          have hstored : fm.promotionInfo r.key = some pm := by
            have h := hinfoS.symm
            simp only [FlowModel.infoFor] at h
            split at h
            case h_1 pm' hlookup => cases h; exact hlookup
            case h_2 =>
              split at h
              · cases h
                exfalso; apply hchain
                rw [hrefines_pm.promotedTypes]
                simp [PromotionModel.fresh]
              · cases h
          rw [FlowModel.set_self hstored]
          exact hrefines

/--
The algorithm's `tryMarkNonNullable` refines the specification's `promoteToNonNull`, given
refinement of the flow model (`hrefines`) relative to a well-formed key store (`hwf`) and of the
reference (`hr`).
-/
public theorem FlowModelImpl.refines.tryMarkNonNullable
    {fmI : FlowModelImpl} {ks : PromotionKeyStore} {fm : FlowModel} (hrefines : fmI.refines ks fm)
    (hwf : ks.WellFormed) {rI : ReferenceImpl} {r : Reference} (hr : rI.refines ks fmI r)
    (previousType : τ) :
    (fmI.tryMarkNonNullable rI previousType).refines ks
      (fm.promoteToNonNull (some r) previousType) :=
  hrefines.tryPromoteForTypeCast hwf hr previousType (NonNull previousType)

end

/-! ### Joining the properties of two versions -/

/--
`JoinInv ks₀ st` is the invariant of the state `st` (the flow model being built, and the key store)
of a join that started from the well-formed key store `ks₀`:
- the key store is well formed, extends `ks₀`, and has the same variable keys;
- the property maps of the versions that `ks₀` had allocated are unchanged (only new versions get
  properties); and
- the flow model being built records nothing under an unallocated key, and only allocated
  versions.
-/
public structure JoinInv (ks₀ : PromotionKeyStore) (st : FlowModelImpl × PromotionKeyStore) :
    Prop where
  /-- The key store is well formed. -/
  wf : st.2.WellFormed
  /-- The key store extends `ks₀`. -/
  ext : ks₀.Extends st.2
  /-- No variable keys have been allocated. -/
  variableKeys : st.2.variableKeys = ks₀.variableKeys
  /-- The property maps of the versions that `ks₀` had allocated are unchanged. -/
  old : ∀ u, u < ks₀.nextVersion → ∀ n : String,
    (st.2.promotableProperties u)[n]? = (ks₀.promotableProperties u)[n]?
  /-- The flow model being built records nothing under an unallocated key. -/
  beyondEnd : ∀ k : PromotionKey, st.2.keys[k]? = none → st.1.promotionInfo[k]? = none
  /-- The flow model being built records only allocated versions. -/
  versions : ∀ (k : PromotionKey) (pmI : PromotionModelImpl) (v : ValueVersionImpl),
    st.1.promotionInfo[k]? = some pmI → pmI.version? = some v →
    v < st.2.nextVersion

/--
`JoinPropertiesPre ks₀ v v₁ v₂ st` is the precondition of joining the properties of versions `v₁`
and `v₂` into the version `v`, from the state `st`, in a join that started from `ks₀`: `st`
satisfies the invariant (`JoinInv`); `v` is a new version, allocated since `ks₀`, with no properties
yet; and `v₁` and `v₂` were allocated in `ks₀`.
-/
public structure JoinPropertiesPre (ks₀ : PromotionKeyStore) (v v₁ v₂ : ValueVersionImpl)
    (st : FlowModelImpl × PromotionKeyStore) : Prop where
  /-- The state satisfies the invariant. -/
  inv : JoinInv ks₀ st
  /-- `v` is newer than every version of `ks₀`. -/
  v_fresh : ks₀.nextVersion ≤ v
  /-- `v` has been allocated. -/
  v_lt : v < st.2.nextVersion
  /-- `v` has no properties yet. -/
  v_empty : ∀ n : String, (st.2.promotableProperties v)[n]? = none
  /-- `v₁` was allocated in `ks₀`. -/
  v₁_lt : v₁ < ks₀.nextVersion
  /-- `v₂` was allocated in `ks₀`. -/
  v₂_lt : v₂ < ks₀.nextVersion

/--
`JoinPropertiesPost fmI₁ fmI₂ ks₀ v v₁ v₂ st st'` is the postcondition of joining the properties of
versions `v₁` and `v₂` (held on the paths whose flow models are `fmI₁` and `fmI₂`) into the version
`v`, from the state `st` to the state `st'`, in a join that started from `ks₀`:
- `st'` satisfies the invariant (`JoinInv`), and its key store extends `st`'s;
- only the property maps of `v` and of versions allocated since `st` have changed;
- the flow model being built is unchanged at the keys allocated in `st`; and
- a path from `v` leads to a property exactly when it leads to properties `p₁` and `p₂` from `v₁`
  and `v₂` in `ks₀`; and then the property has a key that `st` hadn't allocated, under which the
  flow model being built has the join of the promotion models of `p₁` and `p₂`, if they both have
  one (`joinPropertyModels`).
-/
public structure JoinPropertiesPost (fmI₁ fmI₂ : FlowModelImpl) (ks₀ : PromotionKeyStore)
    (v v₁ v₂ : ValueVersionImpl) (st st' : FlowModelImpl × PromotionKeyStore) : Prop where
  /-- The new state satisfies the invariant. -/
  inv : JoinInv ks₀ st'
  /-- The new key store extends the old one. -/
  ext : st.2.Extends st'.2
  /-- Only the property maps of `v` and of new versions have changed. -/
  tables : ∀ u, u < st.2.nextVersion → u ≠ v → ∀ n : String,
    (st'.2.promotableProperties u)[n]? = (st.2.promotableProperties u)[n]?
  /-- The flow model being built is unchanged at the keys allocated in `st`. -/
  acc : ∀ k : PromotionKey, st.2.keys[k]? ≠ none → st'.1.promotionInfo[k]? = st.1.promotionInfo[k]?
  /-- A path that leads from `v` to a property leads from both `v₁` and `v₂` too. -/
  charSome : ∀ (q : List String) (p : PropertyValueVersionImpl),
    st'.2.propertyAt v q = some p → ∃ p₁ p₂,
    ks₀.propertyAt v₁ q = some p₁ ∧ ks₀.propertyAt v₂ q = some p₂ ∧
    st.2.keys[p.promotionKey]? = none ∧
    st'.1.promotionInfo[p.promotionKey]? = joinPropertyModels fmI₁ fmI₂ p₁ p₂ p.version
  /-- A path that leads nowhere from `v` leads nowhere from `v₁` or from `v₂`. -/
  charNone : ∀ q : List String, st'.2.propertyAt v q = none →
    ks₀.propertyAt v₁ q = none ∨ ks₀.propertyAt v₂ q = none

/-- The version of a joined property model, if any, is the joined property's version. -/
theorem joinPropertyModels_version {fmI₁ fmI₂ : FlowModelImpl} {p₁ p₂ : PropertyValueVersionImpl}
    {c : ValueVersionImpl} {pmI : PromotionModelImpl}
    (h : joinPropertyModels fmI₁ fmI₂ p₁ p₂ c = some pmI) {w : ValueVersionImpl}
    (hw : pmI.version? = some w) : w = c := by
  simp only [joinPropertyModels] at h
  split at h
  · cases h
    simp only [PromotionModelImpl.joinWith] at hw
    split at hw
    · cases hw
    · cases hw; rfl
  · cases h

/--
The loop in `joinProperties`, in a join that started from a well-formed store `ks₀` (`hwf₀`), over a
list `L` of properties of `v₁` (`hL`, with distinct names, `hnodup`), from a state `stA` that
satisfies the invariant (`hinv`), in which `v`, newer than every version of `ks₀` (`hv₀`), is
allocated (`hv`) and has none of the properties in `L` (`hempty`), satisfies the postcondition for
those properties, provided the recursive joins (`recurse`) do (`hrec`). `second` is the property map
of `v₂` (`hsecond`).

The postcondition is that of `JoinPropertiesPost`, restricted to paths that start with a property in
`L`, together with the fact that the properties of `v` not in `L` are unchanged. That is, the state
`stB` after the loop is such that:
- `stB` satisfies the invariant (`JoinInv ks₀ stB`);
- its key store extends `stA`'s (`stA.2.Extends stB.2`);
- only the property maps of `v` and of versions allocated since `stA` have changed
  (`∀ u, u < stA.2.nextVersion → u ≠ v → ∀ n, (stB.2.promotableProperties u)[n]? = …`);
- the flow model being built is unchanged at the keys allocated in `stA`
  (`∀ k, stA.2.keys[k]? ≠ none → stB.1.promotionInfo[k]? = stA.1.promotionInfo[k]?`);
- the properties of `v` not in `L` are unchanged
  (`∀ n, (∀ e ∈ L, e.1 ≠ n) → (stB.2.promotableProperties v)[n]? = …`);
- a path from `v` that starts with a property in `L` and leads to a property `p` leads to
  properties `p₁` and `p₂` from `v₁` and `v₂` in `ks₀`; `p` has a key that `stA` hadn't allocated,
  under which the flow model being built has the join of the promotion models of `p₁` and `p₂`
  (`∀ e ∈ L, ∀ r p, stB.2.propertyAt v (e.1 :: r) = some p → ∃ p₁ p₂, … ∧
  stB.1.promotionInfo[p.promotionKey]? = joinPropertyModels fmI₁ fmI₂ p₁ p₂ p.version`); and
- such a path that leads nowhere from `v` leads nowhere from `v₁` or from `v₂`
  (`∀ e ∈ L, ∀ r, stB.2.propertyAt v (e.1 :: r) = none → ks₀.propertyAt v₁ (e.1 :: r) = none ∨
  ks₀.propertyAt v₂ (e.1 :: r) = none`).
-/
theorem joinPropertiesStep_foldl {fmI₁ fmI₂ : FlowModelImpl} {ks₀ : PromotionKeyStore}
    (hwf₀ : ks₀.WellFormed)
    {recurse : ValueVersionImpl → ValueVersionImpl → ValueVersionImpl →
      FlowModelImpl × PromotionKeyStore → FlowModelImpl × PromotionKeyStore}
    {v v₁ v₂ : ValueVersionImpl} (hv₀ : ks₀.nextVersion ≤ v)
    (hrec : ∀ c c₁ c₂ st, JoinPropertiesPre ks₀ c c₁ c₂ st → v₁ < c₁ →
      JoinPropertiesPost fmI₁ fmI₂ ks₀ c c₁ c₂ st (recurse c c₁ c₂ st))
    {second : Std.HashMap String PropertyValueVersionImpl}
    (hsecond : ∀ n : String, second[n]? = (ks₀.promotableProperties v₂)[n]?)
    (L : List (String × PropertyValueVersionImpl)) (stA : FlowModelImpl × PromotionKeyStore)
    (hL : ∀ e ∈ L, (ks₀.promotableProperties v₁)[e.1]? = some e.2)
    (hnodup : L.Pairwise (fun a b => a.1 ≠ b.1)) (hinv : JoinInv ks₀ stA)
    (hv : v < stA.2.nextVersion) (hempty : ∀ e ∈ L, (stA.2.promotableProperties v)[e.1]? = none) :
    let stB := L.foldl (joinPropertiesStep fmI₁ fmI₂ recurse v second) stA
    JoinInv ks₀ stB ∧ stA.2.Extends stB.2 ∧
    (∀ u, u < stA.2.nextVersion → u ≠ v → ∀ n : String,
      (stB.2.promotableProperties u)[n]? = (stA.2.promotableProperties u)[n]?) ∧
    (∀ k : PromotionKey, stA.2.keys[k]? ≠ none →
      stB.1.promotionInfo[k]? = stA.1.promotionInfo[k]?) ∧
    (∀ n : String, (∀ e ∈ L, e.1 ≠ n) →
      (stB.2.promotableProperties v)[n]? = (stA.2.promotableProperties v)[n]?) ∧
    (∀ e ∈ L, ∀ (r : List String) (p : PropertyValueVersionImpl),
      stB.2.propertyAt v (e.1 :: r) = some p → ∃ p₁ p₂,
      ks₀.propertyAt v₁ (e.1 :: r) = some p₁ ∧ ks₀.propertyAt v₂ (e.1 :: r) = some p₂ ∧
      stA.2.keys[p.promotionKey]? = none ∧
      stB.1.promotionInfo[p.promotionKey]? = joinPropertyModels fmI₁ fmI₂ p₁ p₂ p.version) ∧
    (∀ e ∈ L, ∀ r : List String, stB.2.propertyAt v (e.1 :: r) = none →
      ks₀.propertyAt v₁ (e.1 :: r) = none ∨ ks₀.propertyAt v₂ (e.1 :: r) = none) := by
  induction L generalizing stA with
  | nil =>
    simp only [List.foldl_nil]
    exact ⟨hinv, .refl _, by simp, by simp, by simp, by simp, by simp⟩
  | cons e L ih =>
    simp only [List.foldl_cons]
    have hnodup' := List.pairwise_cons.mp hnodup
    have hL' : ∀ e' ∈ L, (ks₀.promotableProperties v₁)[e'.1]? = some e'.2 :=
      fun e' he' => hL e' (List.mem_cons_of_mem _ he')
    have he : (ks₀.promotableProperties v₁)[e.1]? = some e.2 := hL e List.mem_cons_self
    have hempty_e : (stA.2.promotableProperties v)[e.1]? = none := hempty e List.mem_cons_self
    have hne : ∀ e' ∈ L, e'.1 ≠ e.1 := fun e' he' => (hnodup'.1 e' he').symm
    cases hsec : second[e.1]?
    case none =>
      -- `v₂` doesn't have the property, so the step does nothing.
      have hstep : joinPropertiesStep fmI₁ fmI₂ recurse v second stA e = stA := by
        simp [joinPropertiesStep, hsec]
      rw [hstep]
      obtain ⟨hinvB, hextB, htablesB, haccB, hothersB, hsomeB, hnoneB⟩ :=
        ih stA hL' hnodup'.2 hinv hv (fun e' he' => hempty e' (List.mem_cons_of_mem _ he'))
      refine ⟨hinvB, hextB, htablesB, haccB, ?_, ?_, ?_⟩
      · intro n hn
        exact hothersB n fun e' he' => hn e' (List.mem_cons_of_mem _ he')
      · intro e' he' r p hp
        rcases List.mem_cons.mp he' with rfl | he'
        · -- `v` doesn't have the property either.
          rw [PromotionKeyStore.propertyAt_cons_of_none (by
            rw [hothersB e'.1 hne]; exact hempty_e)] at hp
          cases hp
        · exact hsomeB e' he' r p hp
      · intro e' he' r hp
        rcases List.mem_cons.mp he' with rfl | he'
        · right
          rw [hsecond] at hsec
          exact PromotionKeyStore.propertyAt_cons_of_none hsec r
        · exact hnoneB e' he' r hp
    case some p₂ =>
      -- `v` gets a new property version `p`, then its properties are joined.
      rcases hadd : stA.2.addPropertyVersion v e.1 with ⟨p, ks₁⟩
      obtain ⟨hwf₁, hext₁, hpk, hpv, hkeys₁, hnext₁, hvar₁, hp₁, hothers₁⟩ :=
        PromotionKeyStore.addPropertyVersion_spec hinv.wf hv hempty_e hadd
      let acc₁ : FlowModelImpl :=
        match joinPropertyModels fmI₁ fmI₂ e.2 p₂ p.version with
        | some pmI => ⟨stA.1.promotionInfo.insert p.promotionKey pmI⟩
        | none => stA.1
      have hstep : joinPropertiesStep fmI₁ fmI₂ recurse v second stA e =
          recurse p.version e.2.version p₂.version (acc₁, ks₁) := by
        unfold joinPropertiesStep
        rw [hsec]
        dsimp only
        rw [hadd]
        rfl
      rw [hstep]
      have hp₂ : (ks₀.promotableProperties v₂)[e.1]? = some p₂ := by rw [← hsecond]; exact hsec
      -- The key and version of `p` are fresh.
      have hpk_fresh : stA.2.keys[p.promotionKey]? = none := by
        rw [hpk]; exact PromotionKeyStore.getElem?_length_eq_none
      have hacc₁ : ∀ k, k ≠ p.promotionKey → acc₁.promotionInfo[k]? = stA.1.promotionInfo[k]? := by
        intro k hk
        simp only [acc₁]
        split
        · simp [Std.HashMap.getElem?_insert, Ne.symm hk]
        · rfl
      have hacc₁_p : acc₁.promotionInfo[p.promotionKey]? =
          joinPropertyModels fmI₁ fmI₂ e.2 p₂ p.version := by
        simp only [acc₁]
        split
        case h_1 pmI h => simp [h]
        case h_2 h => rw [h]; exact hinv.beyondEnd _ hpk_fresh
      have hvp : v < p.version := by rw [hpv]; exact hv
      have hv₀p : ks₀.nextVersion ≤ p.version := by rw [hpv]; exact hinv.ext.nextVersion
      have hinv₁ : JoinInv ks₀ (acc₁, ks₁) := {
        wf := hwf₁
        ext := hinv.ext.trans hext₁
        variableKeys := hvar₁.trans hinv.variableKeys
        old := fun u hu n => by
          rw [hothers₁ u n (fun h => Nat.not_lt_of_le hv₀ ((Prod.mk.inj h).1 ▸ hu))]
          exact hinv.old u hu n
        beyondEnd := fun k hk => by
          have hk' : stA.2.keys[k]? = none := hext₁.keys_none hk
          have hne : k ≠ p.promotionKey := fun h => by
            subst h; rw [hkeys₁, hpk] at hk; simp at hk
          rw [hacc₁ k hne]
          exact hinv.beyondEnd k hk'
        versions := fun k pmI w hk hw => by
          by_cases hkp : k = p.promotionKey
          · subst hkp
            rw [hacc₁_p] at hk
            rw [joinPropertyModels_version hk hw, hnext₁, hpv]
            exact Nat.lt_succ_self _
          · rw [hacc₁ k hkp] at hk
            rw [hnext₁]
            exact Nat.lt_succ_of_lt (hinv.versions k pmI w hk hw) }
      have hpre : JoinPropertiesPre ks₀ p.version e.2.version p₂.version (acc₁, ks₁) := {
        inv := hinv₁
        v_fresh := hv₀p
        v_lt := by rw [hnext₁, hpv]; exact Nat.lt_succ_self _
        v_empty := fun n => by
          rw [hothers₁ _ n (fun h => Nat.ne_of_gt hvp (Prod.mk.inj h).1)]
          exact hinv.wf.properties_beyond _ n (Nat.le_of_eq hpv.symm)
        v₁_lt := (hwf₀.properties_version v₁ e.1 e.2 he).2
        v₂_lt := (hwf₀.properties_version v₂ e.1 p₂ hp₂).2 }
      have hpost := hrec p.version e.2.version p₂.version (acc₁, ks₁) hpre
        (hwf₀.properties_version v₁ e.1 e.2 he).1
      set st₁ := recurse p.version e.2.version p₂.version (acc₁, ks₁) with hst₁
      -- `v`'s properties after the recursive join.
      have hv₁_tables : ∀ n : String, (st₁.2.promotableProperties v)[n]? =
          (ks₁.promotableProperties v)[n]? := by
        intro n
        exact hpost.tables v (by rw [hnext₁]; exact Nat.lt_succ_of_lt hv) (Nat.ne_of_lt hvp) n
      have hv_lt₁ : v < st₁.2.nextVersion :=
        Nat.lt_of_lt_of_le hv (hext₁.trans hpost.ext).nextVersion
      obtain ⟨hinvB, hextB, htablesB, haccB, hothersB, hsomeB, hnoneB⟩ :=
        ih st₁ hL' hnodup'.2 hpost.inv hv_lt₁ (fun e' he' => by
          rw [hv₁_tables, hothers₁ v e'.1 (by
            intro h; exact hne e' he' (Prod.mk.inj h).2)]
          exact hempty e' (List.mem_cons_of_mem _ he'))
      set stB := L.foldl (joinPropertiesStep fmI₁ fmI₂ recurse v second) st₁ with hstB
      have hextAB : stA.2.Extends stB.2 := hext₁.trans (hpost.ext.trans hextB)
      -- `v`'s property `e.1` is `p` in the final state.
      have hvB : (stB.2.promotableProperties v)[e.1]? = some p := by
        rw [hothersB e.1 hne, hv₁_tables, hp₁]
      refine ⟨hinvB, hextAB, ?_, ?_, ?_, ?_, ?_⟩
      · -- Tables.
        intro u hu huv n
        rw [htablesB u (Nat.lt_of_lt_of_le hu (hext₁.trans hpost.ext).nextVersion) huv n,
          hpost.tables u (by rw [hnext₁]; exact Nat.lt_succ_of_lt hu)
            (by rintro rfl; rw [hpv] at hu; exact Nat.lt_irrefl _ hu) n,
          hothers₁ u n (fun h => huv (Prod.mk.inj h).1)]
      · -- The flow model being built.
        intro k hk
        have hk₁ : ks₁.keys[k]? ≠ none := fun h => hk (hext₁.keys_none h)
        have hkst₁ : st₁.2.keys[k]? ≠ none := fun h => hk₁ (hpost.ext.keys_none h)
        rw [haccB k hkst₁, hpost.acc k hk₁, hacc₁ k (by rintro rfl; exact hk hpk_fresh)]
      · -- The other properties of `v`.
        intro n hn
        rw [hothersB n (fun e' he' => hn e' (List.mem_cons_of_mem _ he')), hv₁_tables,
          hothers₁ v n (by intro h; exact hn e List.mem_cons_self (Prod.mk.inj h).2.symm)]
      · -- Paths that lead somewhere.
        have hk₁p : ks₁.keys[p.promotionKey]? = some none := by rw [hkeys₁, hpk]; simp
        have hkst₁p : st₁.2.keys[p.promotionKey]? = some none := hpost.ext.keys _ _ hk₁p
        have hp_lt : p.version < st₁.2.nextVersion :=
          Nat.lt_of_lt_of_le hpre.v_lt hpost.ext.nextVersion
        -- Paths from `p`'s version are the same in the final state as after the recursive join.
        have hcongr : ∀ r, stB.2.propertyAt p.version r = st₁.2.propertyAt p.version r :=
          PromotionKeyStore.propertyAt_congr hpost.inv.wf hp_lt fun u hu hu' n =>
            htablesB u hu' (fun h => by subst h; exact Nat.lt_irrefl _ (hvp.trans_le hu)) n
        intro e' he' r q hq
        rcases List.mem_cons.mp he' with rfl | he'
        · cases r with
          | nil =>
            simp only [PromotionKeyStore.propertyAt_singleton, hvB, Option.some.injEq] at hq
            subst hq
            refine ⟨e'.2, p₂, by simp [he], by simp [hp₂], hpk_fresh, ?_⟩
            rw [haccB _ (by rw [hkst₁p]; simp), hpost.acc _ (by rw [hk₁p]; simp), hacc₁_p]
          | cons m r =>
            rw [PromotionKeyStore.propertyAt_cons_cons_of_some hvB, hcongr] at hq
            obtain ⟨p₁', p₂', h₁, h₂, hfresh, hval⟩ := hpost.charSome (m :: r) q hq
            refine ⟨p₁', p₂', ?_, ?_, hext₁.keys_none hfresh, ?_⟩
            · rw [PromotionKeyStore.propertyAt_cons_cons_of_some he]; exact h₁
            · rw [PromotionKeyStore.propertyAt_cons_cons_of_some hp₂]; exact h₂
            · rw [haccB _ (hpost.inv.wf.propertyAt_allocated hq), hval]
        · obtain ⟨p₁', p₂', h₁, h₂, hfresh, hval⟩ := hsomeB e' he' r q hq
          exact ⟨p₁', p₂', h₁, h₂, (hext₁.trans hpost.ext).keys_none hfresh, hval⟩
      · -- Paths that lead nowhere.
        have hp_lt : p.version < st₁.2.nextVersion :=
          Nat.lt_of_lt_of_le hpre.v_lt hpost.ext.nextVersion
        have hcongr : ∀ r, stB.2.propertyAt p.version r = st₁.2.propertyAt p.version r :=
          PromotionKeyStore.propertyAt_congr hpost.inv.wf hp_lt fun u hu hu' n =>
            htablesB u hu' (fun h => by subst h; exact Nat.lt_irrefl _ (hvp.trans_le hu)) n
        intro e' he' r hq
        rcases List.mem_cons.mp he' with rfl | he'
        · cases r with
          | nil => simp [hvB] at hq
          | cons m r =>
            rw [PromotionKeyStore.propertyAt_cons_cons_of_some hvB, hcongr] at hq
            rw [PromotionKeyStore.propertyAt_cons_cons_of_some he,
              PromotionKeyStore.propertyAt_cons_cons_of_some hp₂]
            exact hpost.charNone (m :: r) hq
        · exact hnoneB e' he' r hq

/--
`joinProperties` satisfies its postcondition (`JoinPropertiesPost`), given its precondition
(`hpre`), in a join that started from a well-formed store `ks₀` (`hwf₀`), provided `fuel` is enough
(`hfuel`): every version reachable from `v₁` is newer than `v₁`, and older than
`ks₀.nextVersion`, so a recursion `ks₀.nextVersion - v₁` deep is enough.
-/
public theorem joinProperties_spec (fmI₁ fmI₂ : FlowModelImpl) {ks₀ : PromotionKeyStore}
    (hwf₀ : ks₀.WellFormed) (fuel : Nat) (v v₁ v₂ : ValueVersionImpl)
    (st : FlowModelImpl × PromotionKeyStore) (hpre : JoinPropertiesPre ks₀ v v₁ v₂ st)
    (hfuel : ks₀.nextVersion ≤ v₁ + fuel) :
    JoinPropertiesPost fmI₁ fmI₂ ks₀ v v₁ v₂ st (joinProperties fmI₁ fmI₂ fuel v v₁ v₂ st) := by
  induction fuel generalizing v v₁ v₂ st with
  | zero =>
    exact absurd hpre.v₁_lt (Nat.not_lt_of_le hfuel)
  | succ fuel ih =>
    have hrec : ∀ c c₁ c₂ st', JoinPropertiesPre ks₀ c c₁ c₂ st' → v₁ < c₁ →
        JoinPropertiesPost fmI₁ fmI₂ ks₀ c c₁ c₂ st' (joinProperties fmI₁ fmI₂ fuel c c₁ c₂ st') :=
      fun c c₁ c₂ st' hpre' hlt => ih c c₁ c₂ st' hpre' (Nat.le_trans hfuel (by
        rw [Nat.add_comm fuel 1, ← Nat.add_assoc]; exact Nat.add_le_add_right hlt fuel))
    have hold₁ : ∀ n : String,
        (st.2.promotableProperties v₁)[n]? = (ks₀.promotableProperties v₁)[n]? :=
      hpre.inv.old v₁ hpre.v₁_lt
    have hL : ∀ e ∈ (st.2.promotableProperties v₁).toList,
        (ks₀.promotableProperties v₁)[e.1]? = some e.2 := by
      rintro ⟨n, p⟩ he
      rw [← hold₁]
      exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp he
    have hnodup : (st.2.promotableProperties v₁).toList.Pairwise (fun a b => a.1 ≠ b.1) :=
      Std.HashMap.distinct_keys_toList.imp fun h heq => by simp [heq] at h
    obtain ⟨hinvB, hextB, htablesB, haccB, hothersB, hsomeB, hnoneB⟩ :=
      joinPropertiesStep_foldl hwf₀ hpre.v_fresh hrec
        (second := st.2.promotableProperties v₂) (hpre.inv.old v₂ hpre.v₂_lt) _ st hL hnodup
        hpre.inv hpre.v_lt (fun e _ => hpre.v_empty e.1)
    -- A property of `v₁` that isn't in the list doesn't exist.
    have hnot_mem : ∀ n : String, (∀ e ∈ (st.2.promotableProperties v₁).toList, e.1 ≠ n) →
        (ks₀.promotableProperties v₁)[n]? = none := by
      intro n hn
      cases h : (ks₀.promotableProperties v₁)[n]?
      case none => rfl
      case some p₁ =>
        rw [← hold₁] at h
        exact absurd rfl (hn (n, p₁) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h))
    show JoinPropertiesPost fmI₁ fmI₂ ks₀ v v₁ v₂ st
      ((st.2.promotableProperties v₁).toList.foldl
        (joinPropertiesStep fmI₁ fmI₂ (joinProperties fmI₁ fmI₂ fuel) v
          (st.2.promotableProperties v₂)) st)
    exact {
      inv := hinvB
      ext := hextB
      tables := htablesB
      acc := haccB
      charSome := fun q p hq => by
        cases q with
        | nil => simp at hq
        | cons n r =>
          by_cases hn : ∃ e ∈ (st.2.promotableProperties v₁).toList, e.1 = n
          · obtain ⟨e, he, rfl⟩ := hn
            exact hsomeB e he r p hq
          · rw [PromotionKeyStore.propertyAt_cons_of_none (by
              rw [hothersB n (fun e he heq => hn ⟨e, he, heq⟩)]; exact hpre.v_empty n)] at hq
            cases hq
      charNone := fun q hq => by
        cases q with
        | nil => left; simp
        | cons n r =>
          by_cases hn : ∃ e ∈ (st.2.promotableProperties v₁).toList, e.1 = n
          · obtain ⟨e, he, rfl⟩ := hn
            exact hnoneB e he r hq
          · left
            exact PromotionKeyStore.propertyAt_cons_of_none
              (hnot_mem n fun e he heq => hn ⟨e, he, heq⟩) r }

/-! ### Joining two promotion models -/

/--
`JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ ver ksA st` says what the version `ver` of the join of the
promotion models `pmI₁` and `pmI₂` (on the paths whose flow models are `fmI₁` and `fmI₂`) is, in a
join that started from the store `ks₀`, at a point where the store was `ksA` before joining these
models and the state is now `st`:
- if both models hold a version, and they're the same, `ver` is that version;
- if both models hold a version, and they're different, `ver` is a new version `v`, allocated since
  `ksA`, that isn't a property's version, and from which a path leads to a property exactly when it
  leads to properties `p₁` and `p₂` from the two old versions; and then the property has a key that
  `ks₀` hadn't allocated, under which the flow model being built has the join of the promotion
  models of `p₁` and `p₂`, if they both have one (`joinPropertyModels`);
- otherwise (if either is write captured), `ver` is `none`.
-/
@[expose]
public def JoinedVersion (fmI₁ fmI₂ : FlowModelImpl) (ks₀ : PromotionKeyStore)
    (pmI₁ pmI₂ : PromotionModelImpl) (ver : Option ValueVersionImpl) (ksA : PromotionKeyStore)
    (st : FlowModelImpl × PromotionKeyStore) : Prop :=
  match pmI₁.version?, pmI₂.version? with
  | some v₁, some v₂ =>
    (v₁ = v₂ ∧ ver = some v₁) ∨
    (v₁ ≠ v₂ ∧ ∃ v, ver = some v ∧ ksA.nextVersion ≤ v ∧ v < st.2.nextVersion ∧
      ¬st.2.IsChild v ∧
      (∀ (q : List String) (p : PropertyValueVersionImpl), st.2.propertyAt v q = some p →
        ∃ p₁ p₂, ks₀.propertyAt v₁ q = some p₁ ∧ ks₀.propertyAt v₂ q = some p₂ ∧
          ks₀.keys[p.promotionKey]? = none ∧
          st.1.promotionInfo[p.promotionKey]? = joinPropertyModels fmI₁ fmI₂ p₁ p₂ p.version) ∧
      (∀ q : List String, st.2.propertyAt v q = none →
        ks₀.propertyAt v₁ q = none ∨ ks₀.propertyAt v₂ q = none))
  | _, _ => ver = none

/--
The joined version is absent precisely when one of the models being joined is write captured (given
`h`), as `PromotionModelImpl.refines.joinWith` requires.
-/
public theorem JoinedVersion.isNone {fmI₁ fmI₂ : FlowModelImpl} {ks₀ : PromotionKeyStore}
    {pmI₁ pmI₂ : PromotionModelImpl} {ver : Option ValueVersionImpl} {ksA : PromotionKeyStore}
    {st : FlowModelImpl × PromotionKeyStore}
    (h : JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ ver ksA st) :
    ver.isNone = (pmI₁.writeCaptured || pmI₂.writeCaptured) := by
  unfold JoinedVersion at h
  unfold PromotionModelImpl.writeCaptured
  split at h
  case h_1 v₁ v₂ h₁ h₂ =>
    rw [h₁, h₂]
    rcases h with ⟨-, rfl⟩ | ⟨-, v, rfl, -⟩ <;> rfl
  case h_2 hnot =>
    subst h
    cases h₁ : pmI₁.version? <;> cases h₂ : pmI₂.version? <;> simp_all

/--
`JoinedVersion` survives later steps of the join, from state `st` to state `st'`: if `st`'s store is
well formed (`hwf`), `st'`'s extends it (`hext`), the property maps of the versions it had allocated
are unchanged (`htables`), and the flow model being built is unchanged at the keys allocated in `st`
but not in `ks₀` (`hacc`).
-/
public theorem JoinedVersion.mono {fmI₁ fmI₂ : FlowModelImpl} {ks₀ : PromotionKeyStore}
    {pmI₁ pmI₂ : PromotionModelImpl} {ver : Option ValueVersionImpl} {ksA : PromotionKeyStore}
    {st st' : FlowModelImpl × PromotionKeyStore}
    (h : JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ ver ksA st) (hwf : st.2.WellFormed)
    (hext : st.2.Extends st'.2)
    (htables : ∀ u, u < st.2.nextVersion → ∀ n : String,
      (st'.2.promotableProperties u)[n]? = (st.2.promotableProperties u)[n]?)
    (hacc : ∀ k : PromotionKey, st.2.keys[k]? ≠ none → ks₀.keys[k]? = none →
      st'.1.promotionInfo[k]? = st.1.promotionInfo[k]?) :
    JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ ver ksA st' := by
  unfold JoinedVersion at h ⊢
  split at h
  case h_1 v₁ v₂ h₁ h₂ =>
    rcases h with h | ⟨hne, v, hver, hvA, hvlt, hchild, hsome, hnone⟩
    · exact Or.inl h
    · have hcongr : ∀ q, st'.2.propertyAt v q = st.2.propertyAt v q :=
        PromotionKeyStore.propertyAt_congr hwf hvlt fun u _ hu n => htables u hu n
      refine Or.inr ⟨hne, v, hver, hvA, Nat.lt_of_lt_of_le hvlt hext.nextVersion,
        hext.not_isChild hvlt hchild, fun q p hq => ?_, fun q hq => ?_⟩
      · rw [hcongr] at hq
        obtain ⟨p₁, p₂, h₁, h₂, hfresh, hval⟩ := hsome q p hq
        exact ⟨p₁, p₂, h₁, h₂, hfresh, by rw [hacc _ (hwf.propertyAt_allocated hq) hfresh, hval]⟩
      · rw [hcongr] at hq
        exact hnone q hq
  case h_2 hnot => exact h

/--
What `PromotionModelImpl.join` does, from a state `stA` that satisfies the invariant (`hinv`) of a
join that started from the well-formed store `ks₀` (`hwf₀`), when the versions of the two models
being joined were allocated in `ks₀` (`hv₁`, `hv₂`). The result `r` is such that:
- the joined model is their `joinWith`, at a version described by `JoinedVersion`
  (`∃ ver, r.1 = pmI₁.joinWith pmI₂ ver ∧ JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ ver stA.2 r.2`);
- the new state satisfies the invariant (`JoinInv ks₀ r.2`);
- its store extends `stA`'s (`stA.2.Extends r.2.2`);
- the property maps of the versions allocated in `stA` are unchanged
  (`∀ u, u < stA.2.nextVersion → ∀ n, (r.2.2.promotableProperties u)[n]? =
  (stA.2.promotableProperties u)[n]?`); and
- the flow model being built is unchanged at the keys allocated in `stA`
  (`∀ k, stA.2.keys[k]? ≠ none → r.2.1.promotionInfo[k]? = stA.1.promotionInfo[k]?`).
-/
public theorem PromotionModelImpl.join_spec {fmI₁ fmI₂ : FlowModelImpl} {ks₀ : PromotionKeyStore}
    (hwf₀ : ks₀.WellFormed) {pmI₁ pmI₂ : PromotionModelImpl}
    (hv₁ : ∀ v, pmI₁.version? = some v → v < ks₀.nextVersion)
    (hv₂ : ∀ v, pmI₂.version? = some v → v < ks₀.nextVersion)
    {stA : FlowModelImpl × PromotionKeyStore} (hinv : JoinInv ks₀ stA) :
    let r := PromotionModelImpl.join fmI₁ fmI₂ pmI₁ pmI₂ stA
    (∃ ver, r.1 = pmI₁.joinWith pmI₂ ver ∧ JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ ver stA.2 r.2) ∧
    JoinInv ks₀ r.2 ∧ stA.2.Extends r.2.2 ∧
    (∀ u, u < stA.2.nextVersion → ∀ n : String,
      (r.2.2.promotableProperties u)[n]? = (stA.2.promotableProperties u)[n]?) ∧
    (∀ k : PromotionKey, stA.2.keys[k]? ≠ none →
      r.2.1.promotionInfo[k]? = stA.1.promotionInfo[k]?) := by
  intro r
  simp only [r, PromotionModelImpl.join]
  split
  case h_1 v₁ v₂ h₁ h₂ =>
    simp only [joinVersions]
    split
    case isTrue heq =>
      subst heq
      exact ⟨⟨some v₁, rfl, by simp [JoinedVersion, h₁, h₂]⟩, hinv, .refl _, fun _ _ _ => rfl,
        fun _ _ => rfl⟩
    case isFalse hne =>
      -- A new version `v`, whose properties are joined.
      let v := stA.2.nextVersion
      let st₀ : FlowModelImpl × PromotionKeyStore := (stA.1, stA.2.newVersion.2)
      have hinv₀ : JoinInv ks₀ st₀ := {
        wf := PromotionKeyStore.newVersion_wellFormed hinv.wf
        ext := hinv.ext.trans PromotionKeyStore.newVersion_extends
        variableKeys := hinv.variableKeys
        old := hinv.old
        beyondEnd := hinv.beyondEnd
        versions := fun k pmI w hk hw => Nat.lt_succ_of_lt (hinv.versions k pmI w hk hw) }
      have hpre : JoinPropertiesPre ks₀ v v₁ v₂ st₀ := {
        inv := hinv₀
        v_fresh := hinv.ext.nextVersion
        v_lt := Nat.lt_succ_self _
        v_empty := fun n => hinv.wf.properties_beyond _ n (Nat.le_refl _)
        v₁_lt := hv₁ v₁ h₁
        v₂_lt := hv₂ v₂ h₂ }
      have hpost := joinProperties_spec fmI₁ fmI₂ hwf₀ (stA.2.nextVersion + 1) v v₁ v₂ st₀ hpre
        (Nat.le_trans hinv.ext.nextVersion (Nat.le_trans (Nat.le_succ _)
          (Nat.le_add_left _ _)))
      set st' := joinProperties fmI₁ fmI₂ (stA.2.nextVersion + 1) v v₁ v₂ st₀ with hst'
      refine ⟨⟨some v, rfl, ?_⟩, hpost.inv, PromotionKeyStore.newVersion_extends.trans hpost.ext,
        fun u hu n => hpost.tables u (Nat.lt_succ_of_lt hu) (Nat.ne_of_lt hu) n,
        fun k hk => hpost.acc k hk⟩
      simp only [JoinedVersion, h₁, h₂]
      refine Or.inr ⟨hne, v, rfl, Nat.le_refl _,
        Nat.lt_of_lt_of_le hpre.v_lt hpost.ext.nextVersion, ?_, fun q p hq => ?_, hpost.charNone⟩
      · -- No property's version is `v`: the old ones are older, and the new ones newer.
        apply hpost.ext.not_isChild hpre.v_lt
        rintro ⟨u, n, p, hp, hpv⟩
        exact absurd (hinv.wf.properties_version u n p hp).2 (by
          rw [hpv]; exact Nat.lt_irrefl _)
      · obtain ⟨p₁, p₂, h₁', h₂', hfresh, hval⟩ := hpost.charSome q p hq
        exact ⟨p₁, p₂, h₁', h₂', hinv.ext.keys_none hfresh, hval⟩
  case h_2 hnot =>
    refine ⟨⟨none, rfl, ?_⟩, hinv, PromotionKeyStore.Extends.refl _, fun _ _ _ => rfl,
      fun _ _ => rfl⟩
    unfold JoinedVersion
    split
    case h_1 v₁ v₂ h₁ h₂ => exact (hnot v₁ v₂ h₁ h₂).elim
    case h_2 => rfl

/--
`JoinedVersion` only depends on the store before the join step through its allocation counter, so it
holds for any earlier store `ksA'` (`hle`).
-/
public theorem JoinedVersion.weaken {fmI₁ fmI₂ : FlowModelImpl} {ks₀ : PromotionKeyStore}
    {pmI₁ pmI₂ : PromotionModelImpl} {ver : Option ValueVersionImpl} {ksA ksA' : PromotionKeyStore}
    {st : FlowModelImpl × PromotionKeyStore}
    (h : JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ ver ksA st)
    (hle : ksA'.nextVersion ≤ ksA.nextVersion) :
    JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ ver ksA' st := by
  unfold JoinedVersion at h ⊢
  split at h
  case h_1 v₁ v₂ h₁ h₂ =>
    rcases h with h | ⟨hne, v, hver, hvA, rest⟩
    · exact Or.inl h
    · exact Or.inr ⟨hne, v, hver, Nat.le_trans hle hvA, rest⟩
  case h_2 => exact h

/--
A joined version `v` (`hver`) that `ks₀` hadn't allocated (`hv`), when the versions being joined
had been allocated in `ks₀` (`hv₁`), is a new one, allocated between `ksA` and `st`
(`ksA.nextVersion ≤ v ∧ v < st.2.nextVersion`).
-/
public theorem JoinedVersion.fresh_bounds {fmI₁ fmI₂ : FlowModelImpl} {ks₀ : PromotionKeyStore}
    {pmI₁ pmI₂ : PromotionModelImpl} {ver : Option ValueVersionImpl} {ksA : PromotionKeyStore}
    {st : FlowModelImpl × PromotionKeyStore}
    (h : JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ ver ksA st)
    (hv₁ : ∀ v, pmI₁.version? = some v → v < ks₀.nextVersion) {v : ValueVersionImpl}
    (hver : ver = some v) (hv : ks₀.nextVersion ≤ v) :
    ksA.nextVersion ≤ v ∧ v < st.2.nextVersion := by
  unfold JoinedVersion at h
  split at h
  case h_1 v₁ v₂ h₁ h₂ =>
    rcases h with ⟨-, hver'⟩ | ⟨-, v', hver', hvA, hvlt, -⟩
    · rw [hver] at hver'
      obtain rfl := Option.some.inj hver'
      exact absurd (hv₁ _ h₁) (Nat.not_lt_of_le hv)
    · rw [hver] at hver'
      obtain rfl := Option.some.inj hver'
      exact ⟨hvA, hvlt⟩
  case h_2 => rw [hver] at h; cases h

/-- The version of a model built by `joinWith` is the one it was given. -/
@[simp]
public theorem PromotionModelImpl.version?_joinWith {pmI₁ pmI₂ : PromotionModelImpl}
    {ver : Option ValueVersionImpl} : (pmI₁.joinWith pmI₂ ver).version? = ver := rfl

/--
The loop in `FlowModelImpl.join`, in a join that started from a well-formed store `ks₀` (`hwf₀`),
over a list `L` of entries of `fmI₁` (`hL`, with distinct keys, `hnodup`, allocated in `ks₀`,
`hLkeys`, and holding versions allocated in `ks₀`, `hLv`), from a state `stA` that satisfies the
invariant (`hinv`), whose flow model has no entries for the keys in `L` (`hempty`), when `fmI₂`'s
versions were allocated in `ks₀` too (`hv₂`). The state `stB` after the loop is such that:
- `stB` satisfies the invariant (`JoinInv ks₀ stB`);
- its store extends `stA`'s (`stA.2.Extends stB.2`);
- the property maps of the versions allocated in `stA` are unchanged
  (`∀ u, u < stA.2.nextVersion → ∀ n, (stB.2.promotableProperties u)[n]? =
  (stA.2.promotableProperties u)[n]?`);
- the flow model being built is unchanged at the keys allocated in `stA` that aren't in `L`
  (`∀ k, stA.2.keys[k]? ≠ none → (∀ e ∈ L, e.1 ≠ k) →
  stB.1.promotionInfo[k]? = stA.1.promotionInfo[k]?`);
- for each entry in `L`, the flow model being built has no entry if `fmI₂` has none
  (`∀ e ∈ L, fmI₂.promotionInfo[e.1]? = none → stB.1.promotionInfo[e.1]? = none`);
- for each entry in `L` that `fmI₂` has an entry for too, the flow model being built has the join
  of the two models, at a version described by `JoinedVersion`
  (`∀ e ∈ L, ∀ pmI₂, fmI₂.promotionInfo[e.1]? = some pmI₂ → ∃ ver,
  stB.1.promotionInfo[e.1]? = some (e.2.joinWith pmI₂ ver) ∧
  JoinedVersion fmI₁ fmI₂ ks₀ e.2 pmI₂ ver stA.2 stB`); and
- distinct entries in `L` don't get the same new version
  (`∀ e ∈ L, ∀ e' ∈ L, ∀ v, (stB.1.promotionInfo[e.1]?).bind (·.version?) = some v →
  (stB.1.promotionInfo[e'.1]?).bind (·.version?) = some v → ks₀.nextVersion ≤ v → e.1 = e'.1`).
-/
theorem FlowModelImpl.joinStep_foldl {fmI₁ fmI₂ : FlowModelImpl} {ks₀ : PromotionKeyStore}
    (hwf₀ : ks₀.WellFormed)
    (hv₂ : ∀ (k : PromotionKey) (pmI : PromotionModelImpl) (v : ValueVersionImpl),
      fmI₂.promotionInfo[k]? = some pmI → pmI.version? = some v → v < ks₀.nextVersion)
    (L : List (PromotionKey × PromotionModelImpl)) (stA : FlowModelImpl × PromotionKeyStore)
    (hL : ∀ e ∈ L, fmI₁.promotionInfo[e.1]? = some e.2)
    (hLv : ∀ e ∈ L, ∀ v, e.2.version? = some v → v < ks₀.nextVersion)
    (hLkeys : ∀ e ∈ L, ks₀.keys[e.1]? ≠ none)
    (hnodup : L.Pairwise (fun a b => a.1 ≠ b.1))
    (hinv : JoinInv ks₀ stA) (hempty : ∀ e ∈ L, stA.1.promotionInfo[e.1]? = none) :
    let stB := L.foldl (FlowModelImpl.joinStep fmI₁ fmI₂) stA
    JoinInv ks₀ stB ∧ stA.2.Extends stB.2 ∧
    (∀ u, u < stA.2.nextVersion → ∀ n : String,
      (stB.2.promotableProperties u)[n]? = (stA.2.promotableProperties u)[n]?) ∧
    (∀ k : PromotionKey, stA.2.keys[k]? ≠ none → (∀ e ∈ L, e.1 ≠ k) →
      stB.1.promotionInfo[k]? = stA.1.promotionInfo[k]?) ∧
    (∀ e ∈ L, fmI₂.promotionInfo[e.1]? = none → stB.1.promotionInfo[e.1]? = none) ∧
    (∀ e ∈ L, ∀ pmI₂, fmI₂.promotionInfo[e.1]? = some pmI₂ → ∃ ver,
      stB.1.promotionInfo[e.1]? = some (e.2.joinWith pmI₂ ver) ∧
      JoinedVersion fmI₁ fmI₂ ks₀ e.2 pmI₂ ver stA.2 stB) ∧
    (∀ e ∈ L, ∀ e' ∈ L, ∀ v : ValueVersionImpl,
      (stB.1.promotionInfo[e.1]?).bind (·.version?) = some v →
      (stB.1.promotionInfo[e'.1]?).bind (·.version?) = some v →
      ks₀.nextVersion ≤ v → e.1 = e'.1) := by
  induction L generalizing stA with
  | nil =>
    simp only [List.foldl_nil]
    exact ⟨hinv, .refl _, by simp, by simp, by simp, by simp, by simp⟩
  | cons e L ih =>
    simp only [List.foldl_cons]
    have hnodup' := List.pairwise_cons.mp hnodup
    have hne : ∀ e' ∈ L, e'.1 ≠ e.1 := fun e' he' => (hnodup'.1 e' he').symm
    have hL' := fun e' (he' : e' ∈ L) => hL e' (List.mem_cons_of_mem _ he')
    have hLv' := fun e' (he' : e' ∈ L) => hLv e' (List.mem_cons_of_mem _ he')
    have hLkeys' := fun e' (he' : e' ∈ L) => hLkeys e' (List.mem_cons_of_mem _ he')
    have hekey : stA.2.keys[e.1]? ≠ none := fun h =>
      hLkeys e List.mem_cons_self (hinv.ext.keys_none h)
    cases hsec : fmI₂.promotionInfo[e.1]?
    case none =>
      have hstep : FlowModelImpl.joinStep fmI₁ fmI₂ stA e = stA := by
        simp [FlowModelImpl.joinStep, hsec]
      rw [hstep]
      obtain ⟨hinvB, hextB, htablesB, haccB, hnoneB, hsomeB, hinjB⟩ :=
        ih stA hL' hLv' hLkeys' hnodup'.2 hinv
          (fun e' he' => hempty e' (List.mem_cons_of_mem _ he'))
      -- `e`'s key gets no entry.
      have he_none : (L.foldl (FlowModelImpl.joinStep fmI₁ fmI₂) stA).1.promotionInfo[e.1]? =
          none := by
        rw [haccB e.1 hekey hne]; exact hempty e List.mem_cons_self
      refine ⟨hinvB, hextB, htablesB, ?_, ?_, ?_, ?_⟩
      · intro k hk hkL
        exact haccB k hk fun e' he' => hkL e' (List.mem_cons_of_mem _ he')
      · intro e' he' h
        rcases List.mem_cons.mp he' with rfl | he'
        · exact he_none
        · exact hnoneB e' he' h
      · intro e' he' pmI₂ h
        rcases List.mem_cons.mp he' with rfl | he'
        · rw [hsec] at h; cases h
        · exact hsomeB e' he' pmI₂ h
      · intro e₁ he₁ e₂ he₂ v h₁ h₂ hv
        rcases List.mem_cons.mp he₁ with rfl | he₁
        · simp [he_none] at h₁
        rcases List.mem_cons.mp he₂ with rfl | he₂
        · simp [he_none] at h₂
        exact hinjB e₁ he₁ e₂ he₂ v h₁ h₂ hv
    case some pmI₂ =>
      obtain ⟨⟨ver, hpmI, hver⟩, hinvr, hextr, htablesr, haccr⟩ :=
        PromotionModelImpl.join_spec (fmI₁ := fmI₁) (fmI₂ := fmI₂) hwf₀
          (hLv e List.mem_cons_self) (hv₂ e.1 pmI₂ · hsec) hinv
      set r := PromotionModelImpl.join fmI₁ fmI₂ e.2 pmI₂ stA with hr
      let st₁ : FlowModelImpl × PromotionKeyStore := (⟨r.2.1.promotionInfo.insert e.1 r.1⟩, r.2.2)
      have hstep : FlowModelImpl.joinStep fmI₁ fmI₂ stA e = st₁ := by
        simp only [FlowModelImpl.joinStep, hsec, st₁, r]
      rw [hstep]
      have hekey₁ : r.2.2.keys[e.1]? ≠ none := fun h => hekey (hextr.keys_none h)
      have hst₁_acc : ∀ k, k ≠ e.1 → st₁.1.promotionInfo[k]? = r.2.1.promotionInfo[k]? := by
        intro k hk
        simp [st₁, Std.HashMap.getElem?_insert, Ne.symm hk]
      have hst₁_e : st₁.1.promotionInfo[e.1]? = some (e.2.joinWith pmI₂ ver) := by
        simp [st₁, hpmI]
      have hinv₁ : JoinInv ks₀ st₁ := {
        wf := hinvr.wf
        ext := hinvr.ext
        variableKeys := hinvr.variableKeys
        old := hinvr.old
        beyondEnd := fun k hk => by
          have hk' : k ≠ e.1 := fun h => hekey₁ (h ▸ hk)
          rw [hst₁_acc k hk']
          exact hinvr.beyondEnd k hk
        versions := fun k pmI w hk hw => by
          by_cases hk' : k = e.1
          · subst hk'
            rw [hst₁_e] at hk
            cases hk
            simp only [PromotionModelImpl.version?_joinWith] at hw
            by_cases hw₀ : ks₀.nextVersion ≤ w
            · exact (hver.fresh_bounds (hLv e List.mem_cons_self) hw hw₀).2
            · exact Nat.lt_of_lt_of_le (Nat.lt_of_not_le hw₀) hinvr.ext.nextVersion
          · rw [hst₁_acc k hk'] at hk
            exact hinvr.versions k pmI w hk hw }
      have hver₁ : JoinedVersion fmI₁ fmI₂ ks₀ e.2 pmI₂ ver stA.2 st₁ :=
        hver.mono hinvr.wf (.refl _) (fun _ _ _ => rfl) fun k _ hk₀ => hst₁_acc k (fun h =>
          hLkeys e List.mem_cons_self (h ▸ hk₀))
      obtain ⟨hinvB, hextB, htablesB, haccB, hnoneB, hsomeB, hinjB⟩ :=
        ih st₁ hL' hLv' hLkeys' hnodup'.2 hinv₁ (fun e' he' => by
          rw [hst₁_acc e'.1 (hne e' he'), haccr e'.1 (fun h =>
            hLkeys' e' he' (hinv.ext.keys_none h))]
          exact hempty e' (List.mem_cons_of_mem _ he'))
      set stB := L.foldl (FlowModelImpl.joinStep fmI₁ fmI₂) st₁ with hstB
      have he_B : stB.1.promotionInfo[e.1]? = some (e.2.joinWith pmI₂ ver) := by
        rw [haccB e.1 hekey₁ hne, hst₁_e]
      have hverB : JoinedVersion fmI₁ fmI₂ ks₀ e.2 pmI₂ ver stA.2 stB :=
        hver₁.mono hinv₁.wf hextB htablesB fun k hk hk₀ => haccB k hk fun e' he' h =>
          hLkeys' e' he' (h ▸ hk₀)
      refine ⟨hinvB, hextr.trans hextB, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu n
        rw [htablesB u (Nat.lt_of_lt_of_le hu hextr.nextVersion) n, htablesr u hu n]
      · intro k hk hkL
        have hk₁ : st₁.2.keys[k]? ≠ none := fun h => hk (hextr.keys_none h)
        rw [haccB k hk₁ fun e' he' => hkL e' (List.mem_cons_of_mem _ he'),
          hst₁_acc k (Ne.symm (hkL e List.mem_cons_self)), haccr k hk]
      · intro e' he' h
        rcases List.mem_cons.mp he' with rfl | he'
        · rw [hsec] at h; cases h
        · exact hnoneB e' he' h
      · intro e' he' pmI₂' h
        rcases List.mem_cons.mp he' with rfl | he'
        · rw [hsec] at h
          obtain rfl := Option.some.inj h
          exact ⟨ver, he_B, hverB⟩
        · obtain ⟨ver', h₁, h₂⟩ := hsomeB e' he' pmI₂' h
          exact ⟨ver', h₁, h₂.weaken hextr.nextVersion⟩
      · -- `e`'s new version, if any, was allocated before those of the entries after it.
        have hbound : ∀ e' ∈ L, ∀ v, (stB.1.promotionInfo[e'.1]?).bind (·.version?) = some v →
            ks₀.nextVersion ≤ v → st₁.2.nextVersion ≤ v := by
          intro e' he' v hv hv₀
          cases h' : fmI₂.promotionInfo[e'.1]?
          case none => simp [hnoneB e' he' h'] at hv
          case some pmI₂' =>
            obtain ⟨ver', h₁, h₂⟩ := hsomeB e' he' pmI₂' h'
            rw [h₁] at hv
            exact (h₂.fresh_bounds (hLv' e' he') hv hv₀).1
        have hebound : ∀ v, (stB.1.promotionInfo[e.1]?).bind (·.version?) = some v →
            ks₀.nextVersion ≤ v → v < st₁.2.nextVersion := by
          intro v hv hv₀
          rw [he_B] at hv
          exact (hver.fresh_bounds (hLv e List.mem_cons_self) hv hv₀).2
        intro e₁ he₁ e₂ he₂ v h₁ h₂ hv
        rcases List.mem_cons.mp he₁ with rfl | hm₁ <;> rcases List.mem_cons.mp he₂ with rfl | hm₂
        · rfl
        · exact absurd (hbound e₂ hm₂ v h₂ hv) (Nat.not_le_of_lt (hebound v h₁ hv))
        · exact absurd (hbound e₁ hm₁ v h₁ hv) (Nat.not_le_of_lt (hebound v h₂ hv))
        · exact hinjB e₁ hm₁ e₂ hm₂ v h₁ h₂ hv

/--
A joined version `w` (`h`) older than `ksA`'s allocation counter (`hw`) is the version that both
models being joined hold (`pmI₁.version? = some w ∧ pmI₂.version? = some w`).
-/
public theorem JoinedVersion.kept_of_lt {fmI₁ fmI₂ : FlowModelImpl} {ks₀ : PromotionKeyStore}
    {pmI₁ pmI₂ : PromotionModelImpl} {w : ValueVersionImpl} {ksA : PromotionKeyStore}
    {st : FlowModelImpl × PromotionKeyStore}
    (h : JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ (some w) ksA st) (hw : w < ksA.nextVersion) :
    pmI₁.version? = some w ∧ pmI₂.version? = some w := by
  unfold JoinedVersion at h
  split at h
  case h_1 v₁ v₂ h₁ h₂ =>
    rcases h with ⟨rfl, hver⟩ | ⟨-, v, hver, hvA, -⟩
    · obtain rfl := Option.some.inj hver
      exact ⟨h₁, h₂⟩
    · obtain rfl := Option.some.inj hver
      exact absurd hw (Nat.not_lt_of_le hvA)
  case h_2 => cases h

/--
A joined version `w` (`h`) not older than `ksA`'s allocation counter (`hw`) isn't a property's
version in `st`, given that the versions being joined are older (`hv₁`).
-/
public theorem JoinedVersion.not_isChild {fmI₁ fmI₂ : FlowModelImpl} {ks₀ : PromotionKeyStore}
    {pmI₁ pmI₂ : PromotionModelImpl} {w : ValueVersionImpl} {ksA : PromotionKeyStore}
    {st : FlowModelImpl × PromotionKeyStore}
    (h : JoinedVersion fmI₁ fmI₂ ks₀ pmI₁ pmI₂ (some w) ksA st)
    (hv₁ : ∀ v, pmI₁.version? = some v → v < ksA.nextVersion) (hw : ksA.nextVersion ≤ w) :
    ¬st.2.IsChild w := by
  unfold JoinedVersion at h
  split at h
  case h_1 v₁ v₂ h₁ h₂ =>
    rcases h with ⟨rfl, hver⟩ | ⟨-, v, hver, -, -, hchild, -⟩
    · obtain rfl := Option.some.inj hver
      exact absurd (hv₁ _ h₁) (Nat.not_lt_of_le hw)
    · obtain rfl := Option.some.inj hver
      exact hchild
  case h_2 => cases h

/--
Joins preserve refinement: if `fmI₁` refines `fm₁` (`hrefines₁`) and `fmI₂` refines `fm₂`
(`hrefines₂`), relative to a well-formed key store `ks` (`hwf`), then joining them gives a flow
model and a key store such that:
- the key store is well formed (`(fmI₁.join fmI₂ ks).2.WellFormed`);
- it extends `ks` (`ks.Extends (fmI₁.join fmI₂ ks).2`); and
- the flow model refines `fm₁.join fm₂` relative to it
  (`(fmI₁.join fmI₂ ks).1.refines (fmI₁.join fmI₂ ks).2 (fm₁.join fm₂)`).

Where a variable holds the same version on both paths, its properties' promotion models are joined
pointwise, as in the specification. Where it holds different versions, it gets a new version, whose
paths lead to properties whose promotion models are the joins of those found along the same paths
from the old versions (`JoinedVersion`); and the specification's pointwise join of the
`Key.property` entries rooted at the variable computes the same thing.
-/
public theorem FlowModelImpl.refines.join {fmI₁ fmI₂ : FlowModelImpl} {ks : PromotionKeyStore}
    {fm₁ fm₂ : FlowModel} (hrefines₁ : fmI₁.refines ks fm₁) (hrefines₂ : fmI₂.refines ks fm₂)
    (hwf : ks.WellFormed) :
    (fmI₁.join fmI₂ ks).2.WellFormed ∧ ks.Extends (fmI₁.join fmI₂ ks).2 ∧
      (fmI₁.join fmI₂ ks).1.refines (fmI₁.join fmI₂ ks).2 (fm₁.join fm₂) := by
  unfold FlowModelImpl.join
  split
  case isTrue hempty₁ =>
    -- `fm₁` is empty, and so is the join.
    have heq : fm₁.join fm₂ = fm₁ := by
      apply FlowModel.extensionality; intro key
      rw [FlowModel.promotionInfo_join, hrefines₁.eq_none_of_isEmpty hempty₁ key]; rfl
    rw [heq]; exact ⟨hwf, .refl _, hrefines₁⟩
  case isFalse =>
  split
  case isTrue hempty₂ =>
    -- `fm₂` is empty, and so is the join.
    have heq : fm₁.join fm₂ = fm₂ := by
      apply FlowModel.extensionality; intro key
      rw [FlowModel.promotionInfo_join, hrefines₂.eq_none_of_isEmpty hempty₂ key]
      cases fm₁.promotionInfo key <;> rfl
    rw [heq]; exact ⟨hwf, .refl _, hrefines₂⟩
  case isFalse =>
  have hL : ∀ e ∈ fmI₁.promotionInfo.toList, fmI₁.promotionInfo[e.1]? = some e.2 := by
    rintro ⟨k, pmI⟩ he
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp he
  have hmem : ∀ (k : PromotionKey) (pmI : PromotionModelImpl),
      fmI₁.promotionInfo[k]? = some pmI → (k, pmI) ∈ fmI₁.promotionInfo.toList :=
    fun _ _ h => Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
  have hLv : ∀ e ∈ fmI₁.promotionInfo.toList, ∀ v, e.2.version? = some v → v < ks.nextVersion :=
    fun e he v hv => hrefines₁.versions e.1 e.2 v (hL e he) hv
  have hLkeys : ∀ e ∈ fmI₁.promotionInfo.toList, ks.keys[e.1]? ≠ none := fun e he h => by
    have := hL e he
    rw [hrefines₁.beyondEnd e.1 h] at this
    cases this
  have hnodup : fmI₁.promotionInfo.toList.Pairwise (fun a b => a.1 ≠ b.1) :=
    Std.HashMap.distinct_keys_toList.imp fun h heq => by simp [heq] at h
  have hinv₀ : JoinInv ks ((FlowModelImpl.empty : FlowModelImpl), ks) := {
    wf := hwf
    ext := .refl _
    variableKeys := rfl
    old := fun _ _ _ => rfl
    beyondEnd := fun _ _ => by simp [FlowModelImpl.empty]
    versions := fun _ _ _ h _ => by simp [FlowModelImpl.empty] at h }
  obtain ⟨hinvB, hextB, -, haccB, hnoneB, hsomeB, hinjB⟩ :=
    FlowModelImpl.joinStep_foldl hwf (fun k pmI v hk hv => hrefines₂.versions k pmI v hk hv) _
      ((FlowModelImpl.empty : FlowModelImpl), ks) hL hLv hLkeys hnodup hinv₀
      (fun _ _ => by simp [FlowModelImpl.empty])
  set stB := fmI₁.promotionInfo.toList.foldl (FlowModelImpl.joinStep fmI₁ fmI₂)
    ((FlowModelImpl.empty : FlowModelImpl), ks) with hstB
  -- The entry for each key allocated in `ks`.
  have hat₁ : ∀ k : PromotionKey, ks.keys[k]? ≠ none → fmI₁.promotionInfo[k]? = none →
      stB.1.promotionInfo[k]? = none := by
    intro k hk h
    rw [haccB k hk fun e he heq => by rw [← heq, hL e he] at h; cases h]
    simp [FlowModelImpl.empty]
  have hat₂ : ∀ (k : PromotionKey) (pmI₁ : PromotionModelImpl),
      fmI₁.promotionInfo[k]? = some pmI₁ → fmI₂.promotionInfo[k]? = none →
      stB.1.promotionInfo[k]? = none :=
    fun k pmI₁ h₁ h₂ => hnoneB (k, pmI₁) (hmem k pmI₁ h₁) h₂
  have hat : ∀ (k : PromotionKey) (pmI₁ pmI₂ : PromotionModelImpl),
      fmI₁.promotionInfo[k]? = some pmI₁ →
      fmI₂.promotionInfo[k]? = some pmI₂ → ∃ ver,
        stB.1.promotionInfo[k]? = some (pmI₁.joinWith pmI₂ ver) ∧
        JoinedVersion fmI₁ fmI₂ ks pmI₁ pmI₂ ver ks stB :=
    fun k pmI₁ pmI₂ h₁ h₂ => hsomeB (k, pmI₁) (hmem k pmI₁ h₁) pmI₂ h₂
  -- The specification's join has no entry where either side has none.
  have hspec_none₁ : ∀ key : Key, fm₁.promotionInfo key = none →
      (fm₁.join fm₂).promotionInfo key = none := by
    intro key h; simp [FlowModel.promotionInfo_join, h]
  have hspec_none₂ : ∀ key : Key, fm₂.promotionInfo key = none →
      (fm₁.join fm₂).promotionInfo key = none := by
    intro key h; simp [FlowModel.promotionInfo_join, h]
  -- Where a key means the same thing on both sides, the join is pointwise.
  have hpointwise : ∀ (k : PromotionKey) (key : Key), ks.keys[k]? ≠ none →
      fmI₁.PromotionInfoRefinesAt fm₁ k key → fmI₂.PromotionInfoRefinesAt fm₂ k key →
      stB.1.PromotionInfoRefinesAt (fm₁.join fm₂) k key := by
    intro k key hk h₁ h₂
    cases h₁
    case absent hI₁ hS₁ => exact .absent (hat₁ k hk hI₁) (hspec_none₁ key hS₁)
    case present pmI₁ pm₁ hI₁ hS₁ hr₁ =>
      cases h₂
      case absent hI₂ hS₂ => exact .absent (hat₂ k pmI₁ hI₁ hI₂) (hspec_none₂ key hS₂)
      case present pmI₂ pm₂ hI₂ hS₂ hr₂ =>
        obtain ⟨ver, hB, hver⟩ := hat k pmI₁ pmI₂ hI₁ hI₂
        exact .present hB (by simp [FlowModel.promotionInfo_join, hS₁, hS₂])
          (hr₁.joinWith hr₂ hver.isNone)
  have hvarB : stB.2.variableKeys = ks.variableKeys := hinvB.variableKeys
  -- The version a variable holds after the join comes from a join of two versions.
  have hfinal : ∀ (decl : ℓ) (w : ValueVersionImpl), stB.1.rootVersion stB.2 decl = some w →
      ∃ k pmI₁ pmI₂,
      ks.variableKeys decl = some k ∧ fmI₁.promotionInfo[k]? = some pmI₁ ∧
      fmI₂.promotionInfo[k]? = some pmI₂ ∧
      (stB.1.promotionInfo[k]?).bind (·.version?) = some w ∧
      JoinedVersion fmI₁ fmI₂ ks pmI₁ pmI₂ (some w) ks stB := by
    intro decl w hw
    simp only [FlowModelImpl.rootVersion, hvarB, Option.bind_eq_some_iff] at hw
    obtain ⟨k, hk, pmI, hB, hw⟩ := hw
    have hkalloc := hwf.variableKey_allocated hk
    cases hI₁ : fmI₁.promotionInfo[k]?
    case none => rw [hat₁ k hkalloc hI₁] at hB; cases hB
    case some pmI₁ =>
      cases hI₂ : fmI₂.promotionInfo[k]?
      case none => rw [hat₂ k pmI₁ hI₁ hI₂] at hB; cases hB
      case some pmI₂ =>
        obtain ⟨ver, hB', hver⟩ := hat k pmI₁ pmI₂ hI₁ hI₂
        rw [hB'] at hB
        obtain rfl := Option.some.inj hB
        simp only [PromotionModelImpl.version?_joinWith] at hw
        subst hw
        exact ⟨k, pmI₁, pmI₂, hk, hI₁, hI₂, by simp [hB'], hver⟩
  refine ⟨hinvB.wf, hextB, ?_⟩
  exact {
    variableInfos := fun decl k hk => by
      rw [hvarB] at hk
      exact hpointwise k (.var decl) (hwf.variableKey_allocated hk)
        (hrefines₁.variableInfos decl k hk) (hrefines₂.variableInfos decl k hk)
    unallocated := fun decl hk => by
      rw [hvarB] at hk
      exact hspec_none₁ _ (hrefines₁.unallocated decl hk)
    properties := fun decl q => by
      have hp₁ := hrefines₁.properties decl q
      have hp₂ := hrefines₂.properties decl q
      unfold FlowModelImpl.PropertyRefinesAt at hp₁ hp₂ ⊢
      cases hk : ks.variableKeys decl
      case none =>
        rw [FlowModelImpl.rootVersion_of_none (hvarB ▸ hk)]
        rw [FlowModelImpl.rootVersion_of_none hk] at hp₁
        exact hspec_none₁ _ hp₁
      case some k =>
        rw [FlowModelImpl.rootVersion_eq (hvarB ▸ hk)]
        rw [FlowModelImpl.rootVersion_eq hk] at hp₁ hp₂
        have hkalloc := hwf.variableKey_allocated hk
        cases hI₁ : fmI₁.promotionInfo[k]?
        case none =>
          rw [hat₁ k hkalloc hI₁]
          rw [hI₁] at hp₁
          exact hspec_none₁ _ hp₁
        case some pmI₁ =>
          cases hI₂ : fmI₂.promotionInfo[k]?
          case none =>
            rw [hat₂ k pmI₁ hI₁ hI₂]
            rw [hI₂] at hp₂
            exact hspec_none₂ _ hp₂
          case some pmI₂ =>
            obtain ⟨ver, hB, hver⟩ := hat k pmI₁ pmI₂ hI₁ hI₂
            rw [hB]
            rw [hI₁] at hp₁
            rw [hI₂] at hp₂
            simp only [Option.bind_some, PromotionModelImpl.version?_joinWith] at hp₁ hp₂ ⊢
            unfold JoinedVersion at hver
            split at hver
            case h_1 v₁ v₂ hv₁ hv₂ =>
              rw [hv₁] at hp₁
              rw [hv₂] at hp₂
              simp only [Option.bind_some] at hp₁ hp₂
              rcases hver with ⟨rfl, rfl⟩ | ⟨hne, v, rfl, hvA, hvlt, hchild, hsome, hnone⟩
              · -- The same version on both paths: the paths from it are unchanged.
                simp only [Option.bind_some]
                have hcongr : stB.2.propertyAt v₁ q = ks.propertyAt v₁ q :=
                  PromotionKeyStore.propertyAt_congr hwf
                    (hrefines₁.versions k pmI₁ v₁ hI₁ hv₁) (fun u _ hu n => hinvB.old u hu n) q
                rw [hcongr]
                split
                case h_1 p hp =>
                  rw [hp] at hp₁ hp₂
                  exact hpointwise p.promotionKey _ (hwf.propertyAt_allocated hp) hp₁ hp₂
                case h_2 hp =>
                  rw [hp] at hp₁
                  exact hspec_none₁ _ hp₁
              · -- A new version: its paths lead to the joins of the old versions' properties.
                simp only [Option.bind_some]
                split
                case h_1 p hp =>
                  obtain ⟨p₁, p₂, h₁, h₂, -, hval⟩ := hsome q p hp
                  rw [h₁] at hp₁
                  rw [h₂] at hp₂
                  cases hp₁
                  case absent hI hS =>
                    exact .absent (by rw [hval]; simp [joinPropertyModels, hI])
                      (hspec_none₁ _ hS)
                  case present a pa hIa hSa hra =>
                    cases hp₂
                    case absent hI hS =>
                      exact .absent (by rw [hval]; simp [joinPropertyModels, hIa, hI])
                        (hspec_none₂ _ hS)
                    case present b pb hIb hSb hrb =>
                      refine .present (pmI := a.joinWith b
                          (if a.writeCaptured || b.writeCaptured then none else some p.version))
                        (by rw [hval]; simp only [joinPropertyModels, hIa, hIb])
                        (by simp [FlowModel.promotionInfo_join, hSa, hSb]) (hra.joinWith hrb ?_)
                      cases a.writeCaptured <;> cases b.writeCaptured <;> rfl
                case h_2 hp =>
                  rcases hnone q hp with h | h
                  · rw [h] at hp₁; exact hspec_none₁ _ hp₁
                  · rw [h] at hp₂; exact hspec_none₂ _ hp₂
            case h_2 hnot =>
              subst hver
              simp only [Option.bind_none]
              cases hv₁ : pmI₁.version?
              case none =>
                rw [hv₁] at hp₁
                exact hspec_none₁ _ hp₁
              case some v₁ =>
                cases hv₂ : pmI₂.version?
                case none =>
                  rw [hv₂] at hp₂
                  exact hspec_none₂ _ hp₂
                case some v₂ => exact (hnot v₁ v₂ hv₁ hv₂).elim
    beyondEnd := hinvB.beyondEnd
    versions := hinvB.versions
    roots := fun decl w hw => by
      obtain ⟨k, pmI₁, pmI₂, hk, hI₁, hI₂, -, hver⟩ := hfinal decl w hw
      by_cases hw₀ : ks.nextVersion ≤ w
      · exact hver.not_isChild (fun v hv => hrefines₁.versions k pmI₁ v hI₁ hv) hw₀
      · -- A version kept from both paths.
        have hv₁ := (hver.kept_of_lt (Nat.lt_of_not_le hw₀)).1
        have hroot₁ : fmI₁.rootVersion ks decl = some w := by
          simp [FlowModelImpl.rootVersion, hk, hI₁, hv₁]
        exact hextB.not_isChild (Nat.lt_of_not_le hw₀) (hrefines₁.roots decl w hroot₁)
    roots_inj := fun decl decl' w hw hw' => by
      obtain ⟨k, pmI₁, pmI₂, hk, hI₁, hI₂, hB, hver⟩ := hfinal decl w hw
      obtain ⟨k', pmI₁', pmI₂', hk', hI₁', hI₂', hB', hver'⟩ := hfinal decl' w hw'
      by_cases hw₀ : ks.nextVersion ≤ w
      · -- New versions are distinct for distinct variables.
        have := hinjB (k, pmI₁) (hmem k pmI₁ hI₁) (k', pmI₁') (hmem k' pmI₁' hI₁') w hB hB' hw₀
        simp only at this
        subst this
        exact hwf.variableKeys_inj hk hk'
      · -- Versions kept from both paths are distinct, since they were before.
        have hv₁ := (hver.kept_of_lt (Nat.lt_of_not_le hw₀)).1
        have hv₁' := (hver'.kept_of_lt (Nat.lt_of_not_le hw₀)).1
        exact hrefines₁.roots_inj decl decl' w
          (by simp [FlowModelImpl.rootVersion, hk, hI₁, hv₁])
          (by simp [FlowModelImpl.rootVersion, hk', hI₁', hv₁']) }

end FlowAnalysis
