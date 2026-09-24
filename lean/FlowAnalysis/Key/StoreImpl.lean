module
public import Std.Data.HashMap
public import FlowAnalysis.Elements
public import FlowAnalysis.Key.Basic

/-
This module models the Dart implementation's `PromotionKeyStore`, which hands out the integer
`PromotionKey`s under which flow analysis records what it knows about each promotable part of the
program.

The store is *memoizing*: asking twice for the key of the same variable yields the same key.  That
property is what makes it sound for the implementation to key its flow models by integers rather
than by the things the integers stand for, and it is verified here as `keyForVariable_idem`, on
top of the well-formedness invariant `PromotionKeyStore.WellFormed`.
-/

namespace FlowAnalysis

variable {τ : Type} [DartTypeRepr τ] {ℓ : Type}

local notation "Key" => Key (τ := τ) (ℓ := ℓ)
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
  specification key, and this is the only place the implementation model mentions `Key` at all.
  -/
  keys : List Key
  /-- Mirrors `PromotionKeyStore._variableKeys`. -/
  variableKeys : Std.HashMap Variable PromotionKey

local notation "PromotionKeyStore" => PromotionKeyStore (τ := τ) (ℓ := ℓ)

namespace «PromotionKeyStore»

/-- The key store at the start of flow analysis, before any key has been allocated. -/
@[expose]
public def empty : PromotionKeyStore := ⟨[], ∅⟩

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
  /--
  Distinct promotion keys stand for distinct specification keys.

  At this stage every allocated key is a variable key, so this follows from the other two clauses.
  It is carried as a field anyway because it is what the refinement relation consumes, and because
  it will need re-establishing independently once property keys are allocated.
  -/
  keys_inj : ∀ (k₁ k₂ : PromotionKey) (key : Key),
    ks.keys[k₁]? = some key → ks.keys[k₂]? = some key → k₁ = k₂

/--
`ks.Extends ks'` means that `ks'` was reached from `ks` by allocating zero or more keys: every key
allocated in `ks` is still allocated in `ks'`, and still stands for the same specification key.

Since `keys` is a list, this is equivalent to `ks.keys` being a prefix of `ks'.keys`.  It says
nothing about `variableKeys`, which is recoverable from `keys` in a well-formed store.
-/
@[expose]
public def Extends (ks ks' : PromotionKeyStore) : Prop :=
  ∀ (k : PromotionKey) (key : Key), ks.keys[k]? = some key → ks'.keys[k]? = some key

-- Theorems --

/-- The initial key store is well formed, since it holds nothing at all. -/
public theorem WellFormed.empty : (empty : PromotionKeyStore).WellFormed where
  variableKeys_keys _ _ h := by simp [PromotionKeyStore.empty] at h
  keys_variableKeys _ _ h := by simp [PromotionKeyStore.empty] at h
  keys_inj _ _ _ h := by simp [PromotionKeyStore.empty] at h

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
    -- put it in the memo table.  This is what keeps the new key distinct from all the old ones.
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
    case keys_inj =>
      intro k₁ k₂ key h₁ h₂
      simp only [makeNewKey] at h₁ h₂
      rw [getElem?_append_singleton_eq_some] at h₁ h₂
      rcases h₁ with h₁ | ⟨rfl, rfl⟩ <;> rcases h₂ with h₂ | ⟨rfl, heq⟩
      · exact hwf.keys_inj k₁ k₂ key h₁ h₂
      · cases heq; exact absurd h₁ (hfresh k₁)
      · exact absurd h₂ (hfresh k₂)
      · rfl

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

end «PromotionKeyStore»
end FlowAnalysis
