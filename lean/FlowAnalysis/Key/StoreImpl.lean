module
public import Std.Data.HashMap
public import FlowAnalysis.Elements
public import FlowAnalysis.Key.Basic
public import FlowAnalysis.ValueVersion.Impl

/-
This module models the Dart implementation's `PromotionKeyStore`, which hands out the integer
`PromotionKey`s under which flow analysis records what it knows about each promotable part of the
program.

The store is *memoizing*: asking twice for the key of the same variable, or of the same property of
the same value, yields the same key.  That property is what makes it sound for the implementation
to key its flow models by integers rather than by the things the integers stand for, and it is
verified here as `keyForVariable_idem` and `getOrCreatePropertyVersion_idem`, on top of the
well-formedness invariant `PromotionKeyStore.WellFormed`.
-/

namespace FlowAnalysis

variable {τ : Type} [DartTypeRepr τ] {ℓ : Type}

local notation "Key" => Key (τ := τ) (ℓ := ℓ)
local notation "ValueVersion" => ValueVersion (ℓ := ℓ)
local notation "ValueVersionImpl" => ValueVersionImpl (ℓ := ℓ)
local notation "Variable" => Variable (τ := τ)

/--
Unique identifier assigned to a value tracked by flow analysis.

Mirrors `extension type PromotionKey(int index)`.  An abbreviation rather than a structure, since
Dart's extension type is likewise a zero-cost wrapper; the price is that nothing at the type level
stops a proof from mentioning a concrete key, so theorems must be careful not to.
-/
public abbrev PromotionKey := Nat

/-- Models Dart's `PromotionKeyStore`. -/
public structure PromotionKeyStore where
  /--
  The specification key denoted by each allocated promotion key: `keys[k]?` is `some key` precisely
  when promotion key `k` has been allocated, and `key` is what it stands for.

  Generalizes Dart's `_keyToVariable`, which records only a `Variable?` for each key because that is
  all the implementation ever needs to recover.  The correspondence proofs need the full
  specification key, and this is the only place the implementation model mentions `Key` at all,
  apart from the argument of `makeTemporaryKey` that says what to record here.
  -/
  keys : List Key
  /-- Mirrors `PromotionKeyStore._variableKeys`. -/
  variableKeys : Std.HashMap Variable PromotionKey
  /--
  Mirrors all of Dart's `ValueVersion._promotableProperties` maps at once: `propertyKeys r q` is the
  promotion key of the property version reached from the root `r` by the path `q`, if it has been
  allocated (see `ValueVersionImpl`).

  Dart keeps these maps in the version objects rather than in the key store. They are modelled here
  because, like the rest of the key store, they are never saved and restored as the analysis moves
  between branches.
  -/
  propertyKeys : ValueVersion → List String → Option PromotionKey

local notation "PromotionKeyStore" => PromotionKeyStore (τ := τ) (ℓ := ℓ)

namespace «PromotionKeyStore»

/-- The key store at the start of flow analysis, before any key has been allocated. -/
@[expose]
public def empty : PromotionKeyStore := ⟨[], ∅, fun _ _ => none⟩

/--
Mirrors `PromotionKeyStore._makeNewKey`: allocates a fresh promotion key, standing for `key`.

As in Dart, this does not update `variableKeys`, even when `key` is a variable; that is
`keyForVariable`'s job.  So it does not preserve `WellFormed` on its own.
-/
@[expose]
public def makeNewKey (ks : PromotionKeyStore) (key : Key) : PromotionKey × PromotionKeyStore :=
  (ks.keys.length, { ks with keys := ks.keys ++ [key] })

/--
Mirrors `PromotionKeyStore.keyForVariable`: returns the promotion key for `v`, allocating one if `v`
doesn't have one yet.
-/
@[expose]
public def keyForVariable (ks : PromotionKeyStore) (v : Variable) :
    PromotionKey × PromotionKeyStore :=
  match ks.variableKeys[v]? with
  | some k => (k, ks)
  | none =>
    let (k, ks) := ks.makeNewKey (Key.var v)
    (k, { ks with variableKeys := ks.variableKeys.insert v k })

/--
Mirrors `PromotionKeyStore.makeTemporaryKey`: allocates a fresh promotion key that doesn't stand for
a variable.

`key` is *ghost*: it is the specification key that the new promotion key stands for, which is
recorded in `keys` for the benefit of the correspondence proofs, but which the algorithm never
reads. Dart's `makeTemporaryKey` has no such argument.
-/
@[expose]
public def makeTemporaryKey (ks : PromotionKeyStore) (key : Key) :
    PromotionKey × PromotionKeyStore :=
  ks.makeNewKey key

/--
Mirrors the promotable branch of Dart's `ValueVersion.getOrCreatePropertyVersion`: returns the
promotion key of the property `name` of the value whose version is `target`, allocating one if it
doesn't have one yet.

Dart looks the property up in `target._promotableProperties`, and on a miss stores a new
`_PropertyValueVersion` holding a key from `makeTemporaryKey`. Here the lookup and the update are on
`propertyKeys`, at the property version's root and path, and the caller constructs the property
version itself as `⟨target.roots, target.path ++ [name]⟩`.

TODO(stage 7): take an `isPromotable` argument, as Dart does, and mirror the non-promotable branch
too. That branch allocates a fresh key on *every* access, so a promotion of a non-promotable
property is never seen again. (Dart also records the new version in `_nonPromotableProperties`,
for why-not-promoted, which isn't modelled.) To preserve `WellFormed.keys_inj`, each such key needs
a specification key that no other promotion key stands for; the `.temp site` keys planned for
temporaries may serve. Until then, `handlePropertyM` gives a non-promotable property no reference
at all, which is observably equivalent but doesn't parallel Dart.
-/
@[expose]
public def getOrCreatePropertyVersion [DecidableEq ℓ] (ks : PromotionKeyStore)
    (target : ValueVersionImpl) (name : String) : PromotionKey × PromotionKeyStore :=
  match ks.propertyKeys target.roots (target.path ++ [name]) with
  | some k => (k, ks)
  | none =>
    let (k, ks) := ks.makeTemporaryKey (.loc target.roots (target.path ++ [name]))
    (k, { ks with
      propertyKeys := fun r q =>
        if r = target.roots ∧ q = target.path ++ [name] then some k else ks.propertyKeys r q })

/-- The invariant that the key store maintains. -/
public structure WellFormed (ks : PromotionKeyStore) : Prop where
  /-- Every memo entry points at an allocated key that really is that variable's key. -/
  variableKeys_keys : ∀ (v : Variable) (k : PromotionKey),
    ks.variableKeys[v]? = some k → ks.keys[k]? = some (.var v)
  /--
  Conversely, every allocated variable key is in the memo table.  This is the clause that makes
  `keyForVariable` a *memoized function* rather than a fresh allocation on each call: if a key for
  `v` had been allocated without being recorded, `keyForVariable` would allocate a second one.
  -/
  keys_variableKeys : ∀ (k : PromotionKey) (v : Variable),
    ks.keys[k]? = some (.var v) → ks.variableKeys[v]? = some k
  /-- Every property memo entry points at an allocated key that really is that property's key. -/
  propertyKeys_keys : ∀ (r : ValueVersion) (q : List String) (k : PromotionKey),
    ks.propertyKeys r q = some k → ks.keys[k]? = some (.loc r q)
  /--
  Conversely, every allocated property key is in the property memo table.  This plays the same
  role for `getOrCreatePropertyVersion` as `keys_variableKeys` does for `keyForVariable`.
  -/
  keys_propertyKeys : ∀ (k : PromotionKey) (r : ValueVersion) (q : List String),
    ks.keys[k]? = some (.loc r q) → ks.propertyKeys r q = some k

/--
`ks.Extends ks'` means that `ks'` was reached from `ks` by allocating zero or more keys: every key
allocated in `ks` is still allocated in `ks'`, and still stands for the same specification key.

Since `keys` is a list, this is equivalent to `ks.keys` being a prefix of `ks'.keys`.  It says
nothing about `variableKeys` or `propertyKeys`, which are recoverable from `keys` in a well-formed
store.
-/
@[expose]
public def Extends (ks ks' : PromotionKeyStore) : Prop :=
  ∀ (k : PromotionKey) (key : Key), ks.keys[k]? = some key → ks'.keys[k]? = some key

-- Theorems --

/-- The initial key store is well formed, since it holds nothing at all. -/
public theorem WellFormed.empty : (empty : PromotionKeyStore).WellFormed where
  variableKeys_keys _ _ h := by simp [PromotionKeyStore.empty] at h
  keys_variableKeys _ _ h := by simp [PromotionKeyStore.empty] at h
  propertyKeys_keys _ _ _ h := by simp [PromotionKeyStore.empty] at h
  keys_propertyKeys _ _ _ h := by simp [PromotionKeyStore.empty] at h

/--
Distinct promotion keys stand for distinct specification keys.

This is what the refinement relation consumes. It follows from the two completeness clauses of
`WellFormed`: both promotion keys are the memo table entry for the specification key they stand
for, in `variableKeys` for a variable and in `propertyKeys` for a property.
-/
public theorem WellFormed.keys_inj {ks : PromotionKeyStore} (hwf : ks.WellFormed) :
    ∀ (k₁ k₂ : PromotionKey) (key : Key),
      ks.keys[k₁]? = some key → ks.keys[k₂]? = some key → k₁ = k₂ := by
  intro k₁ k₂ key h₁ h₂
  cases key
  case var v =>
    have := hwf.keys_variableKeys k₁ v h₁
    rw [hwf.keys_variableKeys k₂ v h₂] at this
    exact (Option.some.inj this).symm
  case loc r q =>
    have := hwf.keys_propertyKeys k₁ r q h₁
    rw [hwf.keys_propertyKeys k₂ r q h₂] at this
    exact (Option.some.inj this).symm

@[refl]
public theorem Extends.refl (ks : PromotionKeyStore) : ks.Extends ks := fun _ _ h => h

public theorem Extends.trans {ks₁ ks₂ ks₃ : PromotionKeyStore} (h₁₂ : ks₁.Extends ks₂)
    (h₂₃ : ks₂.Extends ks₃) : ks₁.Extends ks₃ :=
  fun k key h => h₂₃ k key (h₁₂ k key h)

/-- Looking up an index in a list that has had one element appended. -/
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

/-- `makeNewKey` returns the next unused key. -/
@[simp]
public theorem makeNewKey_fst {ks : PromotionKeyStore} {key : Key} :
    (ks.makeNewKey key).1 = ks.keys.length := rfl

/-- `makeNewKey` records exactly `key`, and allocates exactly one key. -/
@[simp]
public theorem makeNewKey_keys {ks : PromotionKeyStore} {key : Key} :
    (ks.makeNewKey key).2.keys = ks.keys ++ [key] := rfl

/-- Allocation only ever grows the store. -/
public theorem makeNewKey_extends {ks : PromotionKeyStore} {key : Key} :
    ks.Extends (ks.makeNewKey key).2 := by
  intro k key' h
  simp [getElem?_append_singleton_eq_some, h]

/--
`keyForVariable` only ever grows the store: on a memo hit it returns the store unchanged, and on a
miss it allocates one key.
-/
public theorem keyForVariable_extends {ks ks' : PromotionKeyStore} {v : Variable}
    {k : PromotionKey} (h : ks.keyForVariable v = (k, ks')) : ks.Extends ks' := by
  obtain rfl : ks' = (ks.keyForVariable v).2 := by rw [h]
  unfold keyForVariable
  split
  · exact Extends.refl ks
  · exact makeNewKey_extends

/-- `keyForVariable` preserves well-formedness. -/
public theorem keyForVariable_wellFormed {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    {v : Variable} {k : PromotionKey} (h : ks.keyForVariable v = (k, ks')) : ks'.WellFormed := by
  obtain rfl : ks' = (ks.keyForVariable v).2 := by rw [h]
  unfold keyForVariable
  split
  case h_1 => exact hwf
  case h_2 hmiss =>
    -- No allocated key already stands for `.var v`, because otherwise `keys_variableKeys` would have
    -- put it in the memo table.  So the new key is the only one that stands for `.var v`, which is
    -- what lets `keys_variableKeys` record it as that variable's key.
    have hfresh : ∀ k : PromotionKey, ks.keys[k]? ≠ some (.var v) := fun k h => by
      simp [hwf.keys_variableKeys k v h] at hmiss
    constructor
    case variableKeys_keys =>
      intro v' k h
      simp only [makeNewKey, Std.HashMap.getElem?_insert, beq_iff_eq] at h ⊢
      rw [getElem?_append_singleton_eq_some]
      split at h
      case isTrue heq => cases h; subst heq; simp
      case isFalse => exact Or.inl (hwf.variableKeys_keys v' k h)
    case keys_variableKeys =>
      intro k v' h
      simp only [makeNewKey, Std.HashMap.getElem?_insert, beq_iff_eq] at h ⊢
      rw [getElem?_append_singleton_eq_some] at h
      rcases h with h | ⟨rfl, heq⟩
      · have hne : v ≠ v' := by rintro rfl; exact hfresh k h
        simp [hne, hwf.keys_variableKeys k v' h]
      · cases heq; simp
    -- `keyForVariable` doesn't touch the property memo table, and the key it allocates isn't a
    -- property key.
    case propertyKeys_keys =>
      intro r q k h
      simp only [makeNewKey] at h ⊢
      rw [getElem?_append_singleton_eq_some]
      exact Or.inl (hwf.propertyKeys_keys r q k h)
    case keys_propertyKeys =>
      intro k r q h
      simp only [makeNewKey] at h ⊢
      rw [getElem?_append_singleton_eq_some] at h
      rcases h with h | ⟨-, heq⟩
      · exact hwf.keys_propertyKeys k r q h
      · cases heq

/-- The key that `keyForVariable` returns stands for `v`. -/
public theorem keyForVariable_keys {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    {v : Variable} {k : PromotionKey} (h : ks.keyForVariable v = (k, ks')) :
    ks'.keys[k]? = some (.var v) := by
  obtain ⟨rfl, rfl⟩ : k = (ks.keyForVariable v).1 ∧ ks' = (ks.keyForVariable v).2 := by simp [h]
  unfold keyForVariable
  split
  case h_1 k hhit => exact hwf.variableKeys_keys v k hhit
  case h_2 => simp

/--
`keyForVariable` memoizes: asking a second time for the key of the same variable returns the same
key, and leaves the store unchanged.
-/
public theorem keyForVariable_idem {ks ks' : PromotionKeyStore} {v : Variable} {k : PromotionKey}
    (h : ks.keyForVariable v = (k, ks')) : ks'.keyForVariable v = (k, ks') := by
  obtain ⟨rfl, rfl⟩ : k = (ks.keyForVariable v).1 ∧ ks' = (ks.keyForVariable v).2 := by simp [h]
  rcases hlookup : ks.variableKeys[v]? with _ | k
  · -- A miss allocates a key and records it, so the second call is a hit on that key.
    simp [keyForVariable, hlookup, makeNewKey]
  · simp [keyForVariable, hlookup]

section
variable [DecidableEq ℓ]

/--
`getOrCreatePropertyVersion` only ever grows the store: on a memo hit it returns the store
unchanged, and on a miss it allocates one key.
-/
public theorem getOrCreatePropertyVersion_extends {ks ks' : PromotionKeyStore}
    {target : ValueVersionImpl} {name : String} {k : PromotionKey}
    (h : ks.getOrCreatePropertyVersion target name = (k, ks')) : ks.Extends ks' := by
  obtain rfl : ks' = (ks.getOrCreatePropertyVersion target name).2 := by rw [h]
  unfold getOrCreatePropertyVersion
  split
  · exact Extends.refl ks
  · exact makeNewKey_extends

/-- `getOrCreatePropertyVersion` preserves well-formedness. -/
public theorem getOrCreatePropertyVersion_wellFormed {ks ks' : PromotionKeyStore}
    (hwf : ks.WellFormed) {target : ValueVersionImpl} {name : String} {k : PromotionKey}
    (h : ks.getOrCreatePropertyVersion target name = (k, ks')) : ks'.WellFormed := by
  obtain rfl : ks' = (ks.getOrCreatePropertyVersion target name).2 := by rw [h]
  unfold getOrCreatePropertyVersion
  split
  case h_1 => exact hwf
  case h_2 hmiss =>
    -- No allocated key already stands for the property, because otherwise `keys_propertyKeys`
    -- would have put it in the memo table.  So the new key is the only one that stands for it,
    -- which is what lets `keys_propertyKeys` record it as that property's key.
    have hfresh : ∀ k : PromotionKey,
        ks.keys[k]? ≠ some (.loc target.roots (target.path ++ [name])) := fun k h => by
      simp [hwf.keys_propertyKeys k _ _ h] at hmiss
    constructor
    -- The variable memo table is untouched, and the key allocated isn't a variable key.
    case variableKeys_keys =>
      intro v k h
      simp only [makeTemporaryKey, makeNewKey] at h ⊢
      rw [getElem?_append_singleton_eq_some]
      exact Or.inl (hwf.variableKeys_keys v k h)
    case keys_variableKeys =>
      intro k v h
      simp only [makeTemporaryKey, makeNewKey] at h ⊢
      rw [getElem?_append_singleton_eq_some] at h
      rcases h with h | ⟨-, heq⟩
      · exact hwf.keys_variableKeys k v h
      · cases heq
    case propertyKeys_keys =>
      intro r q k h
      simp only [makeTemporaryKey, makeNewKey] at h ⊢
      rw [getElem?_append_singleton_eq_some]
      split at h
      case isTrue heq => obtain ⟨rfl, rfl⟩ := heq; cases h; simp
      case isFalse => exact Or.inl (hwf.propertyKeys_keys r q k h)
    case keys_propertyKeys =>
      intro k r q h
      simp only [makeTemporaryKey, makeNewKey] at h ⊢
      rw [getElem?_append_singleton_eq_some] at h
      rcases h with h | ⟨rfl, heq⟩
      · have hne : ¬(r = target.roots ∧ q = target.path ++ [name]) := by
          rintro ⟨rfl, rfl⟩; exact hfresh k h
        simp [hne, hwf.keys_propertyKeys k r q h]
      · cases heq; simp

/-- The key that `getOrCreatePropertyVersion` returns stands for the property. -/
public theorem getOrCreatePropertyVersion_keys {ks ks' : PromotionKeyStore} (hwf : ks.WellFormed)
    {target : ValueVersionImpl} {name : String} {k : PromotionKey}
    (h : ks.getOrCreatePropertyVersion target name = (k, ks')) :
    ks'.keys[k]? = some (.loc target.roots (target.path ++ [name])) := by
  obtain ⟨rfl, rfl⟩ : k = (ks.getOrCreatePropertyVersion target name).1 ∧
      ks' = (ks.getOrCreatePropertyVersion target name).2 := by simp [h]
  unfold getOrCreatePropertyVersion
  split
  case h_1 k hhit => exact hwf.propertyKeys_keys _ _ k hhit
  case h_2 => simp [makeTemporaryKey]

/--
`getOrCreatePropertyVersion` memoizes: asking a second time for the key of the same property of the
same value returns the same key, and leaves the store unchanged.
-/
public theorem getOrCreatePropertyVersion_idem {ks ks' : PromotionKeyStore}
    {target : ValueVersionImpl} {name : String} {k : PromotionKey}
    (h : ks.getOrCreatePropertyVersion target name = (k, ks')) :
    ks'.getOrCreatePropertyVersion target name = (k, ks') := by
  obtain ⟨rfl, rfl⟩ : k = (ks.getOrCreatePropertyVersion target name).1 ∧
      ks' = (ks.getOrCreatePropertyVersion target name).2 := by simp [h]
  rcases hlookup : ks.propertyKeys target.roots (target.path ++ [name]) with _ | k
  · -- A miss allocates a key and records it, so the second call is a hit on that key.
    simp [getOrCreatePropertyVersion, hlookup, makeTemporaryKey, makeNewKey]
  · simp [getOrCreatePropertyVersion, hlookup]

end

end «PromotionKeyStore»
end FlowAnalysis
