module
public import Std.Data.HashMap
public import FlowAnalysis.ValueVersion.Impl

/-!
# The promotion key store

This module models the Dart implementation's `PromotionKeyStore`, which hands out the integer
`PromotionKey`s under which flow analysis records what it knows about each promotable part of the
program, together with the parts of Dart's `ValueVersion` objects that, like the key store, are
never saved and restored as the analysis moves between branches: the allocation of fresh versions,
and each version's map of promotable properties (`_promotableProperties`).

The store is *memoizing* for variables: asking twice for the key of the same variable yields the
same key (`keyForVariable_idem`). A promotable property of a value gets a key the first time it is
read, which is recorded in the value version's property map, so reading it again from the same
version yields the same key (`getOrCreatePropertyVersion_idem`).

The well-formedness invariant `PromotionKeyStore.WellFormed` says, among other things, that the
property maps form a forest whose edges lead from older versions to newer ones, and in which no two
edges share a promotion key or a child version. This is what lets the correspondence proofs follow
a *path* of property names from the version held by a variable (`PromotionKeyStore.propertyAt`),
and know that distinct paths from distinct variables reach distinct promotion keys
(`WellFormed.propertyAt_inj`). `PromotionKeyStore.Extends` says how the store may grow: by
allocating keys and versions, and adding properties with fresh keys and versions.
-/

namespace FlowAnalysis

variable {ℓ : Type}

/--
Unique identifier assigned to a value tracked by flow analysis.

Mirrors `extension type PromotionKey(int index)`.  An abbreviation rather than a structure, since
Dart's extension type is likewise a zero-cost wrapper; the price is that nothing at the type level
stops a proof from mentioning a concrete key, so theorems must be careful not to.
-/
public abbrev PromotionKey := Nat

/--
Mirrors Dart's `_PropertyValueVersion`: the value version of a promotable property, as found in the
property map of the version of its target, together with the promotion key under which promotions
of the property are recorded.
-/
public structure PropertyValueVersionImpl where
  /-- The promotion key of the property. -/
  promotionKey : PromotionKey
  /-- The value version of the property's value. -/
  version : ValueVersionImpl
  deriving DecidableEq, Inhabited

/-- Models Dart's `PromotionKeyStore`, together with the allocation state of value versions. -/
public structure PromotionKeyStore where
  /--
  Mirrors `PromotionKeyStore._keyToVariable`: one entry for each allocated promotion key, which is
  `some decl` if the key is that of the variable declared at `decl`, and `none` for a temporary key
  (`makeTemporaryKey`), such as the key of a property.
  -/
  keys : List (Option ℓ)
  /--
  Mirrors `PromotionKeyStore._variableKeys`: `variableKeys decl` is the promotion key of the
  variable declared at `decl`, if it has been allocated.

  Dart's map is an identity map from variable elements; keying by the declaration plays the same
  role (see `Key.var`).
  -/
  variableKeys : ℓ → Option PromotionKey
  /--
  The number of value versions allocated so far, which is also the next one to be allocated (see
  `ValueVersionImpl`). Dart has no counterpart: it allocates `ValueVersion` objects on the heap.
  -/
  nextVersion : Nat
  /--
  Mirrors all of Dart's `ValueVersion._promotableProperties` maps at once:
  `promotableProperties v` is the property map of version `v`, from property names to the versions
  of the properties.

  Dart keeps these maps in the version objects rather than in the key store. They are modelled here
  because, like the rest of the key store, they are never saved and restored as the analysis moves
  between branches.
  -/
  promotableProperties : ValueVersionImpl → Std.HashMap String PropertyValueVersionImpl

local notation "PromotionKeyStore" => PromotionKeyStore (ℓ := ℓ)

namespace «PromotionKeyStore»

/-- The key store at the start of flow analysis, before any key or version has been allocated. -/
@[expose]
public def empty : PromotionKeyStore := ⟨[], fun _ => none, 0, fun _ => ∅⟩

/--
Mirrors `PromotionKeyStore._makeNewKey`: allocates a fresh promotion key, recording `variable?` as
the variable it belongs to, if any.

As in Dart, this does not update `variableKeys`, even when `variable?` is a variable; that is
`keyForVariable`'s job.  So it does not preserve `WellFormed` on its own.
-/
@[expose]
public def makeNewKey (ks : PromotionKeyStore) (variable? : Option ℓ) :
    PromotionKey × PromotionKeyStore :=
  (ks.keys.length, { ks with keys := ks.keys ++ [variable?] })

/--
Mirrors `PromotionKeyStore.keyForVariable`: returns the promotion key for the variable declared at
`decl`, allocating one if it doesn't have one yet.
-/
@[expose]
public def keyForVariable [DecidableEq ℓ] (ks : PromotionKeyStore) (decl : ℓ) :
    PromotionKey × PromotionKeyStore :=
  match ks.variableKeys decl with
  | some k => (k, ks)
  | none =>
    let (k, ks) := ks.makeNewKey (some decl)
    (k, { ks with variableKeys := fun d => if d = decl then some k else ks.variableKeys d })

/--
Mirrors `PromotionKeyStore.makeTemporaryKey`: allocates a fresh promotion key that doesn't stand for
a variable.
-/
@[expose]
public def makeTemporaryKey (ks : PromotionKeyStore) : PromotionKey × PromotionKeyStore :=
  ks.makeNewKey none

/--
Allocates a fresh value version, which has no properties yet. Mirrors Dart's `new ValueVersion()`.
-/
@[expose]
public def newVersion (ks : PromotionKeyStore) : ValueVersionImpl × PromotionKeyStore :=
  (ks.nextVersion, { ks with nextVersion := ks.nextVersion + 1 })

/--
`ks.setProperty v name p` records `p` as the version of property `name` of version `v`. Mirrors
Dart's `v._promotableProperties[name] = p`.
-/
@[expose]
public def setProperty (ks : PromotionKeyStore) (v : ValueVersionImpl) (name : String)
    (p : PropertyValueVersionImpl) : PromotionKeyStore :=
  { ks with
    promotableProperties := fun u =>
      if u = v then (ks.promotableProperties v).insert name p else ks.promotableProperties u }

/--
`ks.addPropertyVersion v name` allocates a fresh promotion key and a fresh value version, and
records them as the version of property `name` of version `v`, returning them. Mirrors Dart's
`v._promotableProperties[name] = new _PropertyValueVersion(promotionKeyStore.makeTemporaryKey())`.
-/
@[expose]
public def addPropertyVersion (ks : PromotionKeyStore) (v : ValueVersionImpl) (name : String) :
    PropertyValueVersionImpl × PromotionKeyStore :=
  let (k, ks) := ks.makeTemporaryKey
  let (c, ks) := ks.newVersion
  (⟨k, c⟩, ks.setProperty v name ⟨k, c⟩)

/--
Mirrors the promotable branch of Dart's `ValueVersion.getOrCreatePropertyVersion`: returns the
version of the property `name` of the value whose version is `target`, allocating it (with a fresh
promotion key) if it doesn't exist yet.

TODO: take an `isPromotable` argument, as Dart does, and mirror the non-promotable branch
too. That branch allocates a fresh version and key on *every* access, so a promotion of a
non-promotable property is never seen again. (Dart also records the new version in
`_nonPromotableProperties`, for why-not-promoted, which isn't modelled.) Until then,
`handlePropertyM` gives a non-promotable property no reference at all, which is observably
equivalent but doesn't parallel Dart.
-/
@[expose]
public def getOrCreatePropertyVersion (ks : PromotionKeyStore) (target : ValueVersionImpl)
    (name : String) : PropertyValueVersionImpl × PromotionKeyStore :=
  match (ks.promotableProperties target)[name]? with
  | some p => (p, ks)
  | none => ks.addPropertyVersion target name

/--
`ks.versionAt v q` is the version reached from version `v` by following the path of property names
`q` through the property maps, if each property on the way has been read.
-/
@[expose]
public def versionAt (ks : PromotionKeyStore) : ValueVersionImpl → List String →
    Option ValueVersionImpl
  | v, [] => some v
  | v, n :: q => ((ks.promotableProperties v)[n]?).bind fun p => ks.versionAt p.version q

/--
`ks.propertyAt v q` is the property version (with its promotion key) reached from version `v` by
following the nonempty path of property names `q`, if each property on the way has been read. For
the empty path, it is `none`: the version itself has no promotion key of its own.
-/
@[expose]
public def propertyAt (ks : PromotionKeyStore) : ValueVersionImpl → List String →
    Option PropertyValueVersionImpl
  | _, [] => none
  | v, n :: q => ((ks.promotableProperties v)[n]?).bind fun p =>
      match q with
      | [] => some p
      | _ :: _ => ks.propertyAt p.version q

/--
`ks.IsChild c` says that version `c` is the version of some property of some version: it appears in
a property map. A version allocated by a declaration, a write or a join is never a child.
-/
@[expose]
public def IsChild (ks : PromotionKeyStore) (c : ValueVersionImpl) : Prop :=
  ∃ (u : ValueVersionImpl) (n : String) (p : PropertyValueVersionImpl),
    (ks.promotableProperties u)[n]? = some p ∧ p.version = c

/-- The invariant that the key store maintains. -/
public structure WellFormed (ks : PromotionKeyStore) : Prop where
  /-- Every memo entry points at an allocated key that really is that variable's key. -/
  variableKeys_keys : ∀ (decl : ℓ) (k : PromotionKey),
    ks.variableKeys decl = some k → ks.keys[k]? = some (some decl)
  /--
  Conversely, every allocated variable key is in the memo table.  This is the clause that makes
  `keyForVariable` a *memoized function* rather than a fresh allocation on each call: if a key for
  `decl` had been allocated without being recorded, `keyForVariable` would allocate a second one.
  -/
  keys_variableKeys : ∀ (k : PromotionKey) (decl : ℓ),
    ks.keys[k]? = some (some decl) → ks.variableKeys decl = some k
  /-- A version that hasn't been allocated yet has no properties. -/
  properties_beyond : ∀ (v : ValueVersionImpl) (n : String),
    ks.nextVersion ≤ v → (ks.promotableProperties v)[n]? = none
  /-- The promotion key of every property is an allocated temporary key. -/
  properties_key : ∀ (v : ValueVersionImpl) (n : String) (p : PropertyValueVersionImpl),
    (ks.promotableProperties v)[n]? = some p → ks.keys[p.promotionKey]? = some none
  /--
  The version of every property is allocated, and newer than the version it is a property of. This
  is what bounds the depth of the property maps, so that the join (`joinProperties`) terminates.
  -/
  properties_version : ∀ (v : ValueVersionImpl) (n : String) (p : PropertyValueVersionImpl),
    (ks.promotableProperties v)[n]? = some p → v < p.version ∧ p.version < ks.nextVersion
  /-- No two properties share a promotion key. -/
  properties_key_inj : ∀ (v₁ v₂ : ValueVersionImpl) (n₁ n₂ : String)
    (p₁ p₂ : PropertyValueVersionImpl),
    (ks.promotableProperties v₁)[n₁]? = some p₁ → (ks.promotableProperties v₂)[n₂]? = some p₂ →
      p₁.promotionKey = p₂.promotionKey → v₁ = v₂ ∧ n₁ = n₂
  /-- No two properties share a version: the property maps form a forest. -/
  properties_version_inj : ∀ (v₁ v₂ : ValueVersionImpl) (n₁ n₂ : String)
    (p₁ p₂ : PropertyValueVersionImpl),
    (ks.promotableProperties v₁)[n₁]? = some p₁ → (ks.promotableProperties v₂)[n₂]? = some p₂ →
      p₁.version = p₂.version → v₁ = v₂ ∧ n₁ = n₂

/--
`ks.Extends ks'` means that `ks'` was reached from `ks` by allocating zero or more keys and
versions, and adding properties: every key allocated in `ks` is still allocated in `ks'`, and
still belongs to the same variable (if any); every property in `ks` is still there, with the same
version; and every property added has a key and a version that weren't allocated in `ks`.
-/
public structure Extends (ks ks' : PromotionKeyStore) : Prop where
  /-- Every allocated key is still allocated, for the same variable. -/
  keys : ∀ (k : PromotionKey) (o : Option ℓ), ks.keys[k]? = some o → ks'.keys[k]? = some o
  /-- Versions are only ever allocated. -/
  nextVersion : ks.nextVersion ≤ ks'.nextVersion
  /-- Every property is still there, with the same version. -/
  properties : ∀ (v : ValueVersionImpl) (n : String) (p : PropertyValueVersionImpl),
    (ks.promotableProperties v)[n]? = some p → (ks'.promotableProperties v)[n]? = some p
  /-- Every property added has a fresh key and a fresh version. -/
  properties_fresh : ∀ (v : ValueVersionImpl) (n : String) (p : PropertyValueVersionImpl),
    (ks.promotableProperties v)[n]? = none → (ks'.promotableProperties v)[n]? = some p →
      ks.keys[p.promotionKey]? = none ∧ ks.nextVersion ≤ p.version

-- Theorems --

/-- The initial key store is well formed, since it holds nothing at all. -/
public theorem WellFormed.empty : (empty : PromotionKeyStore).WellFormed where
  variableKeys_keys _ _ h := by simp [PromotionKeyStore.empty] at h
  keys_variableKeys _ _ h := by simp [PromotionKeyStore.empty] at h
  properties_beyond _ _ _ := by simp [PromotionKeyStore.empty]
  properties_key _ _ _ h := by simp [PromotionKeyStore.empty] at h
  properties_version _ _ _ h := by simp [PromotionKeyStore.empty] at h
  properties_key_inj _ _ _ _ _ _ h := by simp [PromotionKeyStore.empty] at h
  properties_version_inj _ _ _ _ _ _ h := by simp [PromotionKeyStore.empty] at h

/-- Every key store extends itself. -/
@[refl]
public theorem Extends.refl (ks : PromotionKeyStore) : ks.Extends ks where
  keys _ _ h := h
  nextVersion := Nat.le_refl _
  properties _ _ _ h := h
  properties_fresh _ _ _ h h' := by simp [h] at h'

/--
`Extends` is transitive: if `ks₂` extends `ks₁` (`h₁₂`) and `ks₃` extends `ks₂` (`h₂₃`), then `ks₃`
extends `ks₁`.
-/
public theorem Extends.trans {ks₁ ks₂ ks₃ : PromotionKeyStore} (h₁₂ : ks₁.Extends ks₂)
    (h₂₃ : ks₂.Extends ks₃) : ks₁.Extends ks₃ where
  keys k o h := h₂₃.keys k o (h₁₂.keys k o h)
  nextVersion := Nat.le_trans h₁₂.nextVersion h₂₃.nextVersion
  properties v n p h := h₂₃.properties v n p (h₁₂.properties v n p h)
  properties_fresh v n p h₁ h₃ := by
    cases h₂ : (ks₂.promotableProperties v)[n]?
    case none =>
      -- Added after `ks₂`, so fresh in `ks₂`, and hence in `ks₁`.
      obtain ⟨hk, hv⟩ := h₂₃.properties_fresh v n p h₂ h₃
      refine ⟨?_, Nat.le_trans h₁₂.nextVersion hv⟩
      cases hk₁ : ks₁.keys[p.promotionKey]?
      case none => rfl
      case some o => simp [h₁₂.keys _ o hk₁] at hk
    case some p₂ =>
      -- Added by `ks₂`, and kept by `ks₃`.
      have := h₂₃.properties v n p₂ h₂
      rw [h₃] at this
      cases this
      exact h₁₂.properties_fresh v n p h₁ h₂

/--
Looking up an index `k` in a list that has had one element `a` appended (`(l ++ [a])[k]? = some b`):
either the original list has `b` at `k` (`l[k]? = some b`), or `k` is the new last index
(`k = l.length`) and `a = b`.
-/
theorem getElem?_append_singleton_eq_some {α : Type} {l : List α} {a b : α} {k : Nat} :
    (l ++ [a])[k]? = some b ↔ l[k]? = some b ∨ (k = l.length ∧ a = b) := by
  rcases Nat.lt_trichotomy k l.length with h | h | h
  · rw [List.getElem?_append_left h]
    constructor
    · exact Or.inl
    · rintro (h' | ⟨rfl, _⟩)
      · exact h'
      · omega
  · subst h
    simp
  · have h₁ : (l ++ [a])[k]? = none := List.getElem?_eq_none (by simp; omega)
    have h₂ : l[k]? = none := List.getElem?_eq_none (by omega)
    simp only [h₁, h₂, reduceCtorEq, false_or, false_iff, not_and]
    omega

/-- The key at index `l.length` isn't allocated in a list of keys `l`. -/
@[simp]
public theorem getElem?_length_eq_none {α : Type} {l : List α} : l[l.length]? = none :=
  List.getElem?_eq_none (Nat.le_refl _)

/-- `makeNewKey` returns the next unused key. -/
@[simp]
public theorem makeNewKey_fst {ks : PromotionKeyStore} {o : Option ℓ} :
    (ks.makeNewKey o).1 = ks.keys.length := rfl

/-- `makeNewKey` records exactly `o`, and allocates exactly one key. -/
@[simp]
public theorem makeNewKey_keys {ks : PromotionKeyStore} {o : Option ℓ} :
    (ks.makeNewKey o).2.keys = ks.keys ++ [o] := rfl

/-- Allocation only ever grows the store (`ks.Extends (ks.makeNewKey o).2`). -/
public theorem makeNewKey_extends {ks : PromotionKeyStore} {o : Option ℓ} :
    ks.Extends (ks.makeNewKey o).2 where
  keys k o' h := by simp [getElem?_append_singleton_eq_some, h]
  nextVersion := Nat.le_refl _
  properties _ _ _ h := h
  properties_fresh _ _ _ h h' := by simp [makeNewKey, h] at h'

/--
Allocating a temporary key preserves well-formedness: if `ks` is well formed (`hwf`), so is
`ks.makeTemporaryKey.2`.
-/
public theorem makeTemporaryKey_wellFormed {ks : PromotionKeyStore} (hwf : ks.WellFormed) :
    ks.makeTemporaryKey.2.WellFormed where
  variableKeys_keys d k h := by
    simp only [makeTemporaryKey, makeNewKey] at h ⊢
    rw [getElem?_append_singleton_eq_some]
    exact Or.inl (hwf.variableKeys_keys d k h)
  keys_variableKeys k d h := by
    simp only [makeTemporaryKey, makeNewKey] at h ⊢
    rw [getElem?_append_singleton_eq_some] at h
    rcases h with h | ⟨-, h⟩
    · exact hwf.keys_variableKeys k d h
    · cases h
  properties_beyond := hwf.properties_beyond
  properties_key v n p h := by
    simp only [makeTemporaryKey, makeNewKey] at h ⊢
    rw [getElem?_append_singleton_eq_some]
    exact Or.inl (hwf.properties_key v n p h)
  properties_version := hwf.properties_version
  properties_key_inj := hwf.properties_key_inj
  properties_version_inj := hwf.properties_version_inj

/-- Allocating a version preserves well-formedness (`ks.newVersion.2.WellFormed`, given `hwf`). -/
public theorem newVersion_wellFormed {ks : PromotionKeyStore} (hwf : ks.WellFormed) :
    ks.newVersion.2.WellFormed where
  variableKeys_keys := hwf.variableKeys_keys
  keys_variableKeys := hwf.keys_variableKeys
  properties_beyond v n h := hwf.properties_beyond v n (Nat.le_of_succ_le h)
  properties_key := hwf.properties_key
  properties_version v n p h := by
    have := hwf.properties_version v n p h
    exact ⟨this.1, Nat.lt_succ_of_lt this.2⟩
  properties_key_inj := hwf.properties_key_inj
  properties_version_inj := hwf.properties_version_inj

/-- Allocating a version only ever grows the store (`ks.Extends ks.newVersion.2`). -/
public theorem newVersion_extends {ks : PromotionKeyStore} : ks.Extends ks.newVersion.2 where
  keys _ _ h := h
  nextVersion := by simp [newVersion]
  properties _ _ _ h := h
  properties_fresh _ _ _ h h' := by simp [newVersion, h] at h'

/-- The properties of version `u` after `setProperty v name p`. -/
@[simp]
public theorem promotableProperties_setProperty {ks : PromotionKeyStore} {v u : ValueVersionImpl}
    {name : String} {p : PropertyValueVersionImpl} :
    (ks.setProperty v name p).promotableProperties u =
      if u = v then (ks.promotableProperties v).insert name p else ks.promotableProperties u :=
  rfl

/-- Property `m` of version `u` after `setProperty v name p`. -/
public theorem getElem?_setProperty {ks : PromotionKeyStore} {v u : ValueVersionImpl}
    {name m : String} {p : PropertyValueVersionImpl} :
    ((ks.setProperty v name p).promotableProperties u)[m]? =
      if u = v ∧ m = name then some p else (ks.promotableProperties u)[m]? := by
  simp only [promotableProperties_setProperty]
  by_cases hu : u = v
  · subst hu
    simp only [↓reduceIte, Std.HashMap.getElem?_insert, beq_iff_eq, true_and]
    by_cases hm : m = name
    · simp [hm]
    · simp [hm, Ne.symm hm]
  · simp [hu]

/--
What `addPropertyVersion v name` does, starting from a well-formed store `ks` (`hwf`) in which `v`
is allocated (`hv`) and has no property `name` yet (`hn`). It returns a property version `p` and a
store `ks'` (`h`) such that:
- `ks'` is well formed (`ks'.WellFormed`) and extends `ks` (`ks.Extends ks'`);
- `p`'s key is the next unused key in `ks` (`p.promotionKey = ks.keys.length`), and its version is
  the next unused version (`p.version = ks.nextVersion`);
- exactly one key and one version are allocated (`ks'.keys = ks.keys ++ [none]`,
  `ks'.nextVersion = ks.nextVersion + 1`), and no variable keys are
  (`ks'.variableKeys = ks.variableKeys`);
- `p` is recorded as property `name` of `v` (`(ks'.promotableProperties v)[name]? = some p`); and
- no other property changes (`∀ u m, (u, m) ≠ (v, name) → …`).
-/
public theorem addPropertyVersion_spec {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    {v : ValueVersionImpl} {name : String} {p : PropertyValueVersionImpl}
    (hv : v < ks.nextVersion) (hn : (ks.promotableProperties v)[name]? = none)
    (h : ks.addPropertyVersion v name = (p, ks')) :
    ks'.WellFormed ∧ ks.Extends ks' ∧ p.promotionKey = ks.keys.length ∧
      p.version = ks.nextVersion ∧ ks'.keys = ks.keys ++ [none] ∧
      ks'.nextVersion = ks.nextVersion + 1 ∧ ks'.variableKeys = ks.variableKeys ∧
      (ks'.promotableProperties v)[name]? = some p ∧
      ∀ u m, (u, m) ≠ (v, name) →
        (ks'.promotableProperties u)[m]? = (ks.promotableProperties u)[m]? := by
  obtain ⟨rfl, hks'⟩ : p = ⟨ks.keys.length, ks.nextVersion⟩ ∧
      ks' = ({ ks with keys := ks.keys ++ [none], nextVersion := ks.nextVersion + 1 } :
        PromotionKeyStore).setProperty v name ⟨ks.keys.length, ks.nextVersion⟩ := by
    simp only [addPropertyVersion, makeTemporaryKey, makeNewKey, newVersion, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩
  have hkeys : ks'.keys = ks.keys ++ [none] := by rw [hks']; rfl
  have hnext : ks'.nextVersion = ks.nextVersion + 1 := by rw [hks']; rfl
  have hvar : ks'.variableKeys = ks.variableKeys := by rw [hks']; rfl
  have hprops : ∀ u m, (ks'.promotableProperties u)[m]? =
      if u = v ∧ m = name then some ⟨ks.keys.length, ks.nextVersion⟩
      else (ks.promotableProperties u)[m]? := by
    intro u m; rw [hks', getElem?_setProperty]
  clear hks'
  -- No property has the new key, which wasn't allocated, or the new version, which wasn't either.
  have hkfresh : ∀ (u : ValueVersionImpl) (m : String) (q : PropertyValueVersionImpl),
      (ks.promotableProperties u)[m]? = some q → q.promotionKey ≠ ks.keys.length :=
    fun u m q hq heq => by
      have := hwf.properties_key u m q hq
      rw [heq] at this
      simp at this
  have hvfresh : ∀ (u : ValueVersionImpl) (m : String) (q : PropertyValueVersionImpl),
      (ks.promotableProperties u)[m]? = some q → q.version ≠ ks.nextVersion :=
    fun u m q hq heq => by
      have := (hwf.properties_version u m q hq).2
      rw [heq] at this
      exact Nat.lt_irrefl _ this
  refine ⟨?_, ?_, rfl, rfl, hkeys, hnext, hvar, ?_, ?_⟩
  · constructor
    case variableKeys_keys =>
      intro d k hk
      rw [hvar] at hk
      rw [hkeys, getElem?_append_singleton_eq_some]
      exact Or.inl (hwf.variableKeys_keys d k hk)
    case keys_variableKeys =>
      intro k d hk
      rw [hkeys, getElem?_append_singleton_eq_some] at hk
      rw [hvar]
      rcases hk with hk | ⟨-, hk⟩
      · exact hwf.keys_variableKeys k d hk
      · cases hk
    case properties_beyond =>
      intro u m hu
      rw [hnext] at hu
      rw [hprops]
      have : ¬(u = v ∧ m = name) := fun ⟨h, _⟩ => by
        subst h; exact absurd hu (Nat.not_le_of_lt (Nat.lt_succ_of_lt hv))
      simp only [this, ↓reduceIte]
      exact hwf.properties_beyond u m (Nat.le_of_succ_le hu)
    case properties_key =>
      intro u m q hq
      rw [hprops] at hq
      rw [hkeys, getElem?_append_singleton_eq_some]
      split at hq
      · cases hq; exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl (hwf.properties_key u m q hq)
    case properties_version =>
      intro u m q hq
      rw [hprops] at hq
      rw [hnext]
      split at hq
      · cases hq; rename_i h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hv, Nat.lt_succ_self _⟩
      · have := hwf.properties_version u m q hq
        exact ⟨this.1, Nat.lt_succ_of_lt this.2⟩
    case properties_key_inj =>
      intro u₁ u₂ m₁ m₂ q₁ q₂ hq₁ hq₂ heq
      rw [hprops] at hq₁ hq₂
      split at hq₁ <;> split at hq₂
      · rename_i h₁ h₂; exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
      · cases hq₁; exact absurd heq.symm (hkfresh _ _ _ hq₂)
      · cases hq₂; exact absurd heq (hkfresh _ _ _ hq₁)
      · exact hwf.properties_key_inj u₁ u₂ m₁ m₂ q₁ q₂ hq₁ hq₂ heq
    case properties_version_inj =>
      intro u₁ u₂ m₁ m₂ q₁ q₂ hq₁ hq₂ heq
      rw [hprops] at hq₁ hq₂
      split at hq₁ <;> split at hq₂
      · rename_i h₁ h₂; exact ⟨h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm⟩
      · cases hq₁; exact absurd heq.symm (hvfresh _ _ _ hq₂)
      · cases hq₂; exact absurd heq (hvfresh _ _ _ hq₁)
      · exact hwf.properties_version_inj u₁ u₂ m₁ m₂ q₁ q₂ hq₁ hq₂ heq
  · constructor
    case keys =>
      intro k o hk
      rw [hkeys, getElem?_append_singleton_eq_some]
      exact Or.inl hk
    case nextVersion => rw [hnext]; exact Nat.le_succ _
    case properties =>
      intro u m q hq
      rw [hprops]
      have : ¬(u = v ∧ m = name) := fun ⟨h₁, h₂⟩ => by subst h₁ h₂; simp [hn] at hq
      simp [this, hq]
    case properties_fresh =>
      intro u m q hq hq'
      rw [hprops] at hq'
      split at hq'
      · cases hq'; simp
      · simp [hq] at hq'
  · rw [hprops]; simp
  · intro u m hum
    rw [hprops]
    have : ¬(u = v ∧ m = name) := fun ⟨h₁, h₂⟩ => hum (by rw [h₁, h₂])
    simp [this]

section
variable [DecidableEq ℓ]

/--
`keyForVariable` only ever grows the store (`ks.Extends ks'`, where `h` gives `ks'`): on a memo hit
it returns the store unchanged, and on a miss it allocates one key.
-/
public theorem keyForVariable_extends {ks ks' : PromotionKeyStore} {decl : ℓ}
    {k : PromotionKey} (h : ks.keyForVariable decl = (k, ks')) : ks.Extends ks' := by
  obtain rfl : ks' = (ks.keyForVariable decl).2 := by rw [h]
  unfold keyForVariable
  split
  · exact Extends.refl ks
  · exact
      { keys := fun k o h => by simp [makeNewKey, getElem?_append_singleton_eq_some, h]
        nextVersion := Nat.le_refl _
        properties := fun _ _ _ h => h
        properties_fresh := fun _ _ _ h h' => by simp [makeNewKey, h] at h' }

/--
`keyForVariable` preserves well-formedness: if `ks` is well formed (`hwf`), so is the store `ks'`
that it returns (`h`).
-/
public theorem keyForVariable_wellFormed {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    {decl : ℓ} {k : PromotionKey} (h : ks.keyForVariable decl = (k, ks')) : ks'.WellFormed := by
  obtain rfl : ks' = (ks.keyForVariable decl).2 := by rw [h]
  unfold keyForVariable
  split
  case h_1 => exact hwf
  case h_2 hmiss =>
    -- No allocated key already belongs to `decl`, because otherwise `keys_variableKeys` would
    -- have put it in the memo table.  So the new key is the only one that belongs to `decl`, which
    -- is what lets `keys_variableKeys` record it as that variable's key.
    have hfresh : ∀ k : PromotionKey, ks.keys[k]? ≠ some (some decl) := fun k h => by
      simp [hwf.keys_variableKeys k decl h] at hmiss
    constructor
    case variableKeys_keys =>
      intro d k h
      simp only [makeNewKey] at h ⊢
      rw [getElem?_append_singleton_eq_some]
      split at h
      case isTrue heq => cases h; subst heq; simp
      case isFalse => exact Or.inl (hwf.variableKeys_keys d k h)
    case keys_variableKeys =>
      intro k d h
      simp only [makeNewKey] at h ⊢
      rw [getElem?_append_singleton_eq_some] at h
      rcases h with hk | ⟨rfl, heq⟩
      · have hne : d ≠ decl := fun heq => hfresh k (heq ▸ hk)
        simp [hne, hwf.keys_variableKeys k d hk]
      · cases heq; simp
    -- `keyForVariable` doesn't touch the property maps, and the key it allocates isn't a
    -- property's key.
    case properties_beyond => exact hwf.properties_beyond
    case properties_key =>
      intro v n p h
      simp only [makeNewKey]
      rw [getElem?_append_singleton_eq_some]
      exact Or.inl (hwf.properties_key v n p h)
    case properties_version => exact hwf.properties_version
    case properties_key_inj => exact hwf.properties_key_inj
    case properties_version_inj => exact hwf.properties_version_inj

/--
The key `k` that `keyForVariable` returns (`h`) is the variable's key in the store it returns
(`ks'.variableKeys decl = some k`).
-/
public theorem keyForVariable_variableKeys {ks ks' : PromotionKeyStore} {decl : ℓ}
    {k : PromotionKey} (h : ks.keyForVariable decl = (k, ks')) :
    ks'.variableKeys decl = some k := by
  obtain ⟨rfl, rfl⟩ : k = (ks.keyForVariable decl).1 ∧ ks' = (ks.keyForVariable decl).2 := by
    simp [h]
  unfold keyForVariable
  split
  case h_1 k hhit => exact hhit
  case h_2 => simp

/--
`keyForVariable` memoizes: asking a second time for the key of the same variable (after `h`)
returns the same key, and leaves the store unchanged (`(k, ks')`).
-/
public theorem keyForVariable_idem {ks ks' : PromotionKeyStore} {decl : ℓ} {k : PromotionKey}
    (h : ks.keyForVariable decl = (k, ks')) : ks'.keyForVariable decl = (k, ks') := by
  have := keyForVariable_variableKeys h
  simp [keyForVariable, this]

/--
`keyForVariable` allocates no versions and adds no properties (given `h`): it leaves the version
counter unchanged (`ks'.nextVersion = ks.nextVersion`), and the property maps too
(`ks'.promotableProperties = ks.promotableProperties`).
-/
public theorem keyForVariable_versions {ks ks' : PromotionKeyStore} {decl : ℓ}
    {k : PromotionKey} (h : ks.keyForVariable decl = (k, ks')) :
    ks'.nextVersion = ks.nextVersion ∧ ks'.promotableProperties = ks.promotableProperties := by
  obtain rfl : ks' = (ks.keyForVariable decl).2 := by rw [h]
  unfold keyForVariable
  split <;> simp [makeNewKey]

end

/--
What `getOrCreatePropertyVersion target name` does, starting from a well-formed store `ks` (`hwf`)
in which `target` is allocated (`htarget`): it returns a property version `p` and a store `ks'`
(`h`) that is well formed (`ks'.WellFormed`), extends `ks` (`ks.Extends ks'`), has the same variable
keys (`ks'.variableKeys = ks.variableKeys`), and records `p` as property `name` of `target`
(`(ks'.promotableProperties target)[name]? = some p`).
-/
public theorem getOrCreatePropertyVersion_spec {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    {target : ValueVersionImpl} {name : String} {p : PropertyValueVersionImpl}
    (htarget : target < ks.nextVersion) (h : ks.getOrCreatePropertyVersion target name = (p, ks')) :
    ks'.WellFormed ∧ ks.Extends ks' ∧ ks'.variableKeys = ks.variableKeys ∧
      (ks'.promotableProperties target)[name]? = some p := by
  unfold getOrCreatePropertyVersion at h
  split at h
  case h_1 p' hhit =>
    cases h
    exact ⟨hwf, .refl _, rfl, hhit⟩
  case h_2 hmiss =>
    obtain ⟨hwf', hext, -, -, -, -, hvar, hp, -⟩ := addPropertyVersion_spec hwf htarget hmiss h
    exact ⟨hwf', hext, hvar, hp⟩

/--
`getOrCreatePropertyVersion` memoizes: asking a second time for the property `name` of the same
version (after `h`) returns the same property version, and leaves the store unchanged (`(p, ks')`),
provided the store was well formed (`hwf`) and `target` allocated (`htarget`).
-/
public theorem getOrCreatePropertyVersion_idem {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    {target : ValueVersionImpl} {name : String} {p : PropertyValueVersionImpl}
    (htarget : target < ks.nextVersion) (h : ks.getOrCreatePropertyVersion target name = (p, ks')) :
    ks'.getOrCreatePropertyVersion target name = (p, ks') := by
  unfold getOrCreatePropertyVersion at h
  split at h
  case h_1 p' hhit =>
    cases h
    simp [getOrCreatePropertyVersion, hhit]
  case h_2 hmiss =>
    obtain ⟨-, -, -, -, -, -, -, hp, -⟩ := addPropertyVersion_spec hwf htarget hmiss h
    simp [getOrCreatePropertyVersion, hp]

/-! ### Paths of properties -/

/-- `versionAt v []` is `v` itself. -/
@[simp]
public theorem versionAt_nil {ks : PromotionKeyStore} {v : ValueVersionImpl} :
    ks.versionAt v [] = some v := rfl

/-- `versionAt` follows the first property of the path, then the rest. -/
@[simp]
public theorem versionAt_cons {ks : PromotionKeyStore} {v : ValueVersionImpl} {n : String}
    {q : List String} :
    ks.versionAt v (n :: q) =
      ((ks.promotableProperties v)[n]?).bind fun p => ks.versionAt p.version q := rfl

/-- `propertyAt v []` is `none`. -/
@[simp]
public theorem propertyAt_nil {ks : PromotionKeyStore} {v : ValueVersionImpl} :
    ks.propertyAt v [] = none := rfl

/-- `propertyAt v [n]` is property `n` of `v`. -/
@[simp]
public theorem propertyAt_singleton {ks : PromotionKeyStore} {v : ValueVersionImpl}
    {n : String} : ks.propertyAt v [n] = (ks.promotableProperties v)[n]? := by
  simp only [propertyAt]
  cases (ks.promotableProperties v)[n]? <;> rfl

/-- `propertyAt` follows the first property of a path of length at least two, then the rest. -/
@[simp]
public theorem propertyAt_cons_cons {ks : PromotionKeyStore} {v : ValueVersionImpl}
    {n m : String} {q : List String} :
    ks.propertyAt v (n :: m :: q) =
      ((ks.promotableProperties v)[n]?).bind fun p => ks.propertyAt p.version (m :: q) := rfl

/--
`versionAt` along a path with one more property at the end: the property of the version reached
along the shorter path.
-/
public theorem versionAt_append_singleton {ks : PromotionKeyStore} {v : ValueVersionImpl}
    {q : List String} {n : String} :
    ks.versionAt v (q ++ [n]) =
      (ks.versionAt v q).bind fun u => ((ks.promotableProperties u)[n]?).map (·.version) := by
  induction q generalizing v with
  | nil => simp; cases (ks.promotableProperties v)[n]? <;> rfl
  | cons m q ih => simp [ih, Option.bind_assoc]

/--
`propertyAt` along a nonempty path, split into its last property and the rest: the last property of
the version reached along the rest.
-/
public theorem propertyAt_append_singleton {ks : PromotionKeyStore} {v : ValueVersionImpl}
    {q : List String} {n : String} :
    ks.propertyAt v (q ++ [n]) =
      (ks.versionAt v q).bind fun u => (ks.promotableProperties u)[n]? := by
  induction q generalizing v with
  | nil => simp
  | cons m q ih =>
    cases q with
    | nil => simp [Option.bind_assoc]
    | cons m' q =>
      have ih' := @ih
      simp only [List.cons_append] at ih' ⊢
      simp only [propertyAt_cons_cons, ih', versionAt_cons, Option.bind_assoc]

/-- A list is either empty, or a list with one more element at the end. -/
theorem eq_nil_or_append_singleton {α : Type} (l : List α) : l = [] ∨ ∃ l' a, l = l' ++ [a] := by
  rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨L, b, by simpa using h⟩

/-- A version reached along a nonempty path is a child (`h` gives `ks.IsChild u`). -/
public theorem isChild_of_versionAt {ks : PromotionKeyStore} {v u : ValueVersionImpl}
    {q : List String} {n : String} (h : ks.versionAt v (q ++ [n]) = some u) : ks.IsChild u := by
  rw [versionAt_append_singleton] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨w, -, p, hp, rfl⟩ := h
  exact ⟨w, n, p, hp, rfl⟩

/--
Distinct paths from versions that aren't children lead to distinct versions: in a well-formed
store (`hwf`), if `v` and `v'` aren't children (`hv`, `hv'`), and the paths `q` from `v` and `q'`
from `v'` both lead to `u` (`h`, `h'`), then `v = v'` and `q = q'`.
-/
public theorem WellFormed.versionAt_inj {ks : PromotionKeyStore} (hwf : ks.WellFormed)
    {v v' u : ValueVersionImpl} {q q' : List String} (hv : ¬ks.IsChild v)
    (hv' : ¬ks.IsChild v') (h : ks.versionAt v q = some u) (h' : ks.versionAt v' q' = some u) :
    v = v' ∧ q = q' := by
  -- By induction on the length of `q`, peeling properties off the end of the paths.
  generalize hlen : q.length = len
  induction len generalizing q q' u with
  | zero =>
    obtain rfl : q = [] := List.eq_nil_of_length_eq_zero hlen
    simp only [versionAt_nil, Option.some.injEq] at h
    subst h
    rcases eq_nil_or_append_singleton q' with rfl | ⟨q'', n', rfl⟩
    · simp at h'; exact ⟨h'.symm, rfl⟩
    · exact absurd (isChild_of_versionAt h') hv
  | succ len ih =>
    rcases eq_nil_or_append_singleton q with rfl | ⟨q₀, n, rfl⟩
    · simp at hlen
    rcases eq_nil_or_append_singleton q' with rfl | ⟨q'', n', rfl⟩
    · simp only [versionAt_nil, Option.some.injEq] at h'
      subst h'
      exact absurd (isChild_of_versionAt h) hv'
    · rw [versionAt_append_singleton] at h h'
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
      obtain ⟨w, hw, p, hp, rfl⟩ := h
      obtain ⟨w', hw', p', hp', heq⟩ := h'
      obtain ⟨rfl, rfl⟩ := hwf.properties_version_inj w w' n n' p p' hp hp' heq.symm
      obtain ⟨rfl, rfl⟩ := ih hw hw' (by simpa using hlen)
      exact ⟨rfl, rfl⟩

/--
Distinct paths from versions that aren't children lead to properties with distinct keys: in a
well-formed store (`hwf`), if `v` and `v'` aren't children (`hv`, `hv'`), and the paths `q` from
`v` and `q'` from `v'` lead to properties `p` and `p'` (`h`, `h'`) with the same promotion key
(`hk`), then `v = v'` and `q = q'`.
-/
public theorem WellFormed.propertyAt_inj {ks : PromotionKeyStore} (hwf : ks.WellFormed)
    {v v' : ValueVersionImpl} {q q' : List String} {p p' : PropertyValueVersionImpl}
    (hv : ¬ks.IsChild v) (hv' : ¬ks.IsChild v') (h : ks.propertyAt v q = some p)
    (h' : ks.propertyAt v' q' = some p') (hk : p.promotionKey = p'.promotionKey) :
    v = v' ∧ q = q' := by
  rcases eq_nil_or_append_singleton q with rfl | ⟨q₀, n, rfl⟩
  · simp at h
  rcases eq_nil_or_append_singleton q' with rfl | ⟨q₀', n', rfl⟩
  · simp at h'
  rw [propertyAt_append_singleton, Option.bind_eq_some_iff] at h h'
  obtain ⟨w, hw, hp⟩ := h
  obtain ⟨w', hw', hp'⟩ := h'
  obtain ⟨rfl, rfl⟩ := hwf.properties_key_inj w w' n n' p p' hp hp' hk
  obtain ⟨rfl, rfl⟩ := hwf.versionAt_inj hv hv' hw hw'
  exact ⟨rfl, rfl⟩

/--
The property reached along a path is in some version's property map (`h` gives
`∃ u n, (ks.promotableProperties u)[n]? = some p`).
-/
public theorem mem_of_propertyAt {ks : PromotionKeyStore} {v : ValueVersionImpl}
    {q : List String} {p : PropertyValueVersionImpl} (h : ks.propertyAt v q = some p) :
    ∃ (u : ValueVersionImpl) (n : String), (ks.promotableProperties u)[n]? = some p := by
  rcases eq_nil_or_append_singleton q with rfl | ⟨q₀, n, rfl⟩
  · simp at h
  rw [propertyAt_append_singleton, Option.bind_eq_some_iff] at h
  obtain ⟨w, -, hp⟩ := h
  exact ⟨w, n, hp⟩

/-- The version reached along a path that leads to a property `p` (`h`) is `p`'s version. -/
public theorem versionAt_of_propertyAt {ks : PromotionKeyStore} {v : ValueVersionImpl}
    {q : List String} {p : PropertyValueVersionImpl} (h : ks.propertyAt v q = some p) :
    ks.versionAt v q = some p.version := by
  rcases eq_nil_or_append_singleton q with rfl | ⟨q₀, n, rfl⟩
  · simp at h
  rw [propertyAt_append_singleton, Option.bind_eq_some_iff] at h
  obtain ⟨w, hw, hp⟩ := h
  rw [versionAt_append_singleton, hw]
  simp [hp]

/--
In a well-formed store (`hwf`), a version reached along a path (`h`) from an allocated version
(`hv`) is allocated (`u < ks.nextVersion`).
-/
public theorem WellFormed.versionAt_lt {ks : PromotionKeyStore} (hwf : ks.WellFormed)
    {v u : ValueVersionImpl} {q : List String} (hv : v < ks.nextVersion)
    (h : ks.versionAt v q = some u) : u < ks.nextVersion := by
  induction q generalizing v with
  | nil => simp only [versionAt_nil, Option.some.injEq] at h; subst h; exact hv
  | cons n q ih =>
    simp only [versionAt_cons, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, h⟩ := h
    exact ih (hwf.properties_version v n p hp).2 h

/--
A path that leads somewhere in a store `ks` (`h`) leads to the same version in any extension `ks'`
of `ks` (`hext`).
-/
public theorem Extends.versionAt {ks ks' : PromotionKeyStore} (hext : ks.Extends ks')
    {v u : ValueVersionImpl} {q : List String} (h : ks.versionAt v q = some u) :
    ks'.versionAt v q = some u := by
  induction q generalizing v with
  | nil => exact h
  | cons n q ih =>
    simp only [versionAt_cons, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨p, hp, h⟩ := h
    exact ⟨p, hext.properties v n p hp, ih h⟩

/--
In a store `ks'` that extends a well-formed store `ks` (`hwf`, `hext`), every property reached from
a version that `ks` hadn't allocated (`hv`) is fresh (`h` gives `ks.keys[p.promotionKey]? = none`).
-/
theorem Extends.propertyAt_fresh {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    (hext : ks.Extends ks') {v : ValueVersionImpl} {q : List String}
    {p : PropertyValueVersionImpl} (hv : ks.nextVersion ≤ v) (h : ks'.propertyAt v q = some p) :
    ks.keys[p.promotionKey]? = none := by
  induction q generalizing v with
  | nil => simp at h
  | cons n q ih =>
    cases hp₀ : (ks'.promotableProperties v)[n]?
    case none => cases q <;> simp [hp₀] at h
    case some p₀ =>
      obtain ⟨hk, hver⟩ := hext.properties_fresh v n p₀ (hwf.properties_beyond v n hv) hp₀
      cases q with
      | nil => simp only [propertyAt_singleton, hp₀, Option.some.injEq] at h; subst h; exact hk
      | cons m q =>
        simp only [propertyAt_cons_cons, hp₀, Option.bind_some] at h
        exact ih hver h

/--
In a well-formed store `ks'` (`hwf'`) that extends a well-formed store `ks` (`hwf`, `hext`), every
variable that had a key still has the same key (`ks.variableKeys decl = some k →
ks'.variableKeys decl = some k`).
-/
public theorem Extends.variableKeys_of_some {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    (hwf' : ks'.WellFormed) (hext : ks.Extends ks') {decl : ℓ} {k : PromotionKey}
    (h : ks.variableKeys decl = some k) : ks'.variableKeys decl = some k :=
  hwf'.keys_variableKeys k decl (hext.keys k _ (hwf.variableKeys_keys decl k h))

/--
In a well-formed store `ks'` (`hwf'`) that extends a well-formed store `ks` (`hwf`, `hext`), a
variable that has a key `k` in `ks'` (`h'`) but had none in `ks` (`h`) has a key that `ks` hadn't
allocated (`ks.keys[k]? = none`).
-/
public theorem Extends.variableKeys_fresh {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    (hwf' : ks'.WellFormed) (hext : ks.Extends ks') {decl : ℓ} {k : PromotionKey}
    (h : ks.variableKeys decl = none) (h' : ks'.variableKeys decl = some k) :
    ks.keys[k]? = none := by
  cases hk : ks.keys[k]?
  case none => rfl
  case some o =>
    have h₁ := hext.keys k o hk
    rw [hwf'.variableKeys_keys decl k h'] at h₁
    cases h₁
    rw [hwf.keys_variableKeys k decl hk] at h
    cases h

/--
Following a path in a store `ks'` that extends a well-formed store `ks` (`hwf`, `hext`) either
- gives the same result as in `ks` (`ks'.propertyAt v q = ks.propertyAt v q`), or
- leads nowhere in `ks` (`ks.propertyAt v q = none`) and, in `ks'`, reaches only properties whose
  keys `ks` hadn't allocated
  (`∀ p, ks'.propertyAt v q = some p → ks.keys[p.promotionKey]? = none`).
-/
public theorem Extends.propertyAt {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    (hext : ks.Extends ks') (v : ValueVersionImpl) (q : List String) :
    ks'.propertyAt v q = ks.propertyAt v q ∨
      (ks.propertyAt v q = none ∧
        ∀ p, ks'.propertyAt v q = some p → ks.keys[p.promotionKey]? = none) := by
  induction q generalizing v with
  | nil => simp
  | cons n q ih =>
    cases hp : (ks.promotableProperties v)[n]?
    case some p₀ =>
      have hp' := hext.properties v n p₀ hp
      cases q with
      | nil => left; simp [hp, hp']
      | cons m q =>
        simp only [propertyAt_cons_cons, hp, hp', Option.bind_some]
        exact ih p₀.version
    case none =>
      cases hp' : (ks'.promotableProperties v)[n]?
      case none => left; cases q <;> simp [hp, hp']
      case some p₀ =>
        obtain ⟨hk, hver⟩ := hext.properties_fresh v n p₀ hp hp'
        right
        refine ⟨by cases q <;> simp [hp], fun p h => ?_⟩
        cases q with
        | nil => simp only [propertyAt_singleton, hp', Option.some.injEq] at h; subst h; exact hk
        | cons m q =>
          simp only [propertyAt_cons_cons, hp', Option.bind_some] at h
          exact hext.propertyAt_fresh hwf hver h

/--
Following a path depends only on the property maps: stores with the same property maps (`h`) give
the same results.
-/
public theorem propertyAt_eq_of_promotableProperties_eq {ks ks' : PromotionKeyStore}
    (h : ks'.promotableProperties = ks.promotableProperties) (v : ValueVersionImpl)
    (q : List String) : ks'.propertyAt v q = ks.propertyAt v q := by
  induction q generalizing v with
  | nil => simp
  | cons n q ih =>
    cases q with
    | nil => simp [h]
    | cons m q => simp only [propertyAt_cons_cons, h, ih]

/--
Following a path from an allocated version `c` (`hc`) of a well-formed store `ks` (`hwf`) gives the
same result in any store `ks'` that has the same property maps for every allocated version from `c`
on (`hsame`): a path only ever leads to newer versions.
-/
public theorem propertyAt_congr {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    {c : ValueVersionImpl} (hc : c < ks.nextVersion)
    (hsame : ∀ u, c ≤ u → u < ks.nextVersion → ∀ n : String,
      (ks'.promotableProperties u)[n]? = (ks.promotableProperties u)[n]?)
    (q : List String) : ks'.propertyAt c q = ks.propertyAt c q := by
  induction q generalizing c with
  | nil => simp
  | cons n q ih =>
    have hc' := hsame c (Nat.le_refl c) hc n
    cases hp : (ks.promotableProperties c)[n]?
    case none => cases q <;> simp [hc', hp]
    case some p =>
      obtain ⟨hlt, hlt'⟩ := hwf.properties_version c n p hp
      cases q with
      | nil => simp [hc', hp]
      | cons m q =>
        simp only [propertyAt_cons_cons, hc', hp, Option.bind_some]
        exact ih hlt' fun u hu hu' => hsame u (Nat.le_trans (Nat.le_of_lt hlt) hu) hu'

/-- Following a path from a version with no property `n` (`h`) along a path starting with `n`. -/
public theorem propertyAt_cons_of_none {ks : PromotionKeyStore} {v : ValueVersionImpl}
    {n : String} (h : (ks.promotableProperties v)[n]? = none) (r : List String) :
    ks.propertyAt v (n :: r) = none := by
  cases r <;> simp [h]

/--
Following a path starting with `n` from a version whose property `n` is `p` (`h`) follows the rest
of the path from `p`'s version.
-/
public theorem propertyAt_cons_cons_of_some {ks : PromotionKeyStore} {v : ValueVersionImpl}
    {n m : String} {p : PropertyValueVersionImpl}
    (h : (ks.promotableProperties v)[n]? = some p) (r : List String) :
    ks.propertyAt v (n :: m :: r) = ks.propertyAt p.version (m :: r) := by
  simp [h]

/-- A key that an extension `ks'` of `ks` (`hext`) hasn't allocated (`h`), `ks` hadn't either. -/
public theorem Extends.keys_none {ks ks' : PromotionKeyStore} (hext : ks.Extends ks')
    {k : PromotionKey} (h : ks'.keys[k]? = none) : ks.keys[k]? = none := by
  cases hk : ks.keys[k]?
  case none => rfl
  case some o => simp [hext.keys k o hk] at h

/--
A version that `ks` had allocated (`hv`) and that wasn't a child there (`hnot`) isn't a child in an
extension `ks'` of `ks` (`hext`) either: a property added since has a fresh version.
-/
public theorem Extends.not_isChild {ks ks' : PromotionKeyStore} (hext : ks.Extends ks')
    {v : ValueVersionImpl} (hv : v < ks.nextVersion) (hnot : ¬ks.IsChild v) : ¬ks'.IsChild v := by
  rintro ⟨u, n, p, hp, rfl⟩
  cases hold : (ks.promotableProperties u)[n]?
  case some p₀ =>
    have := hext.properties u n p₀ hold
    rw [hp] at this
    obtain rfl := Option.some.inj this
    exact hnot ⟨u, n, _, hold, rfl⟩
  case none =>
    exact absurd hv (Nat.not_lt_of_le (hext.properties_fresh u n p hold hp).2)

end «PromotionKeyStore»
end FlowAnalysis
