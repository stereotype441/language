module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Option.NAry

namespace FlowAnalysis

/-
This module defines `ValueVersion`, the specification's model of the Dart implementation's
`ValueVersion` class (formerly `SsaNode`).

Flow analysis promotes *values*, not storage locations, so it needs a way to tell whether the value
held by some promotable location is "the same value" as the one that was held there earlier.  The
implementation answers that question with pointer identity: it allocates a fresh `ValueVersion`
object each time a new value comes into existence, and two locations hold the same value precisely
when they point to the same object.

The specification can't use pointer identity, so instead it names each value structurally:

  - Each point in the program at which a fresh value comes into existence (a variable declaration, a
    write, `this`, a temporary, ...) is identified by a *label* of type `ℓ`.  `ℓ` is deliberately
    left abstract here; nothing in this module may depend on how labels are formed.
  - The value of a property `n` of a value `v` is named by extending `v`'s name with `n`.
  - At a join point, the joined value is named by the *set* of values that flow into it.

Taking the set at join points (rather than minting a fresh name, as the implementation does) is what
makes join associative, commutative and idempotent on the nose, which in turn makes the
specification independent of the order in which branches happen to be joined.

Finally, we quotient by the law

  getProperty (join v₁ v₂) n = join (getProperty v₁ n) (getProperty v₂ n)

which is exactly what the implementation's `_joinProperties` computes.  Under that law every name
collapses to a root label followed by a path of property names, so a value version is just a
nonempty finite set of such paths.
-/

variable {ℓ : Type}

/--
A single element of a `ValueVersion`: a root label, paired with the path of property names leading
from that root to the value in question.  An empty path denotes the root value itself.
-/
public abbrev Atom := ℓ × List String

local notation "Atom" => Atom (ℓ := ℓ)

/-- `a.extend name` names the property `name` of the value named by the atom `a`. -/
@[expose]
public def Atom.extend (a : Atom) (name : String) : Atom := (a.1, a.2 ++ [name])

/-- Extending an atom's path with a property name is injective. -/
public theorem Atom.extend_injective (name : String) :
    Function.Injective (fun a : Atom => a.extend name) := by
  rintro ⟨l₁, p₁⟩ ⟨l₂, p₂⟩ h
  simp_all [Atom.extend]

/--
Identifies the value held by a promotable location at a particular point in a function's execution.

Two locations hold the same value iff their `ValueVersion`s are equal, so promotions established for
one are available to the other.

A `ValueVersion` is a nonempty finite set of `Atom`s: a value that has not passed through a join
point is a single atom, and a value produced by joining several control flow paths is the union of
the atoms of the values that flow into it.  Nonemptiness holds because every value ultimately
originates at some root.
-/
public abbrev ValueVersion := {atoms : Finset Atom // atoms.Nonempty}

local notation "ValueVersion" => ValueVersion (ℓ := ℓ)

namespace «ValueVersion»

/--
Simplification theorem: the atoms of a `ValueVersion` are trivially nonempty, since a `ValueVersion`
can only be created if a witness to nonemptiness is provided.
-/
@[simp]
public theorem prop (v : ValueVersion) : v.val.Nonempty := v.2

/-- Extensionality: value versions may be proven equal by proving their atom sets equal. -/
public theorem ext {v₁ v₂ : ValueVersion} : v₁.val = v₂.val → v₁ = v₂ := by
  intro h; apply Subtype.ext; assumption

/-- Injection: if value versions are equal then their atom sets are equal. -/
public theorem val_inj {v₁ v₂ : ValueVersion} : v₁ = v₂ → v₁.val = v₂.val := by
  intro rfl; rfl

/-- Equality of value versions may be rewritten to equality of atom sets and vice versa. -/
public theorem ext_iff {v₁ v₂ : ValueVersion} : v₁ = v₂ ↔ v₁.val = v₂.val := by
  constructor
  · apply val_inj
  · apply ext

/--
`root l` is the value that comes into existence at the program point labelled `l`.  It is distinct
from every other root, and from every property of every value (see `getProperty_ne_root`).
-/
@[expose]
public def root (l : ℓ) : ValueVersion := ⟨{(l, [])}, by simp⟩

@[simp]
public theorem val_root {l : ℓ} : (root l).val = {(l, [])} := rfl

/-- Distinct labels denote distinct values. -/
@[simp]
public theorem root_inj {l₁ l₂ : ℓ} : root l₁ = root l₂ ↔ l₁ = l₂ := by
  rw [ext_iff]; simp

/--
The version of a value whose creation site cannot yet be labelled.

TODO: every value that comes into existence should be labelled with the program point that created
it, but the syntax doesn't yet carry enough information to do that.  Until it does, all such values
share this single unspecified version.

Deliberately not exposed, so that proofs can't rely on how it is constructed.
-/
public def unspecified [Inhabited ℓ] : ValueVersion := root default

variable [DecidableEq ℓ]

-- Value versions are used as map keys, so decidable equality is required.  It is inherited from
-- `Finset` and `Subtype`; this `example` merely records that fact.
example : DecidableEq ValueVersion := inferInstance

/--
`join v₁ v₂` is the value observed at a join point whose incoming control flow paths hold `v₁` and
`v₂` respectively.
-/
@[expose]
public def join (v₁ v₂ : ValueVersion) : ValueVersion :=
  ⟨v₁.val ∪ v₂.val, by simp [Finset.union_nonempty]⟩

@[simp]
public theorem val_join {v₁ v₂ : ValueVersion} : (join v₁ v₂).val = v₁.val ∪ v₂.val := rfl

/-- The join operation is idempotent (`join v v = v`). -/
@[simp]
public theorem join_self (v : ValueVersion) : join v v = v := by
  apply ext; simp

public instance join.instIdempotentOp : Std.IdempotentOp (join (ℓ := ℓ)) where
  idempotent := join_self

/-- The join operation is commutative (`join v₁ v₂ = join v₂ v₁`). -/
public theorem join_comm (v₁ v₂ : ValueVersion) : join v₁ v₂ = join v₂ v₁ := by
  apply ext; simp [Finset.union_comm]

public instance join.instCommutative : Std.Commutative (join (ℓ := ℓ)) where
  comm := join_comm

/-- The join operation is associative (`join (join v₁ v₂) v₃ = join v₁ (join v₂ v₃)`). -/
public theorem join_assoc (v₁ v₂ v₃ : ValueVersion) :
    join (join v₁ v₂) v₃ = join v₁ (join v₂ v₃) := by
  apply ext; simp [Finset.union_assoc]

public instance join.instAssociative : Std.Associative (join (ℓ := ℓ)) where
  assoc := join_assoc

/--
`v.getProperty n` is the value held by the property `n` of the value `v`.

This is named `getProperty` rather than `property` to avoid colliding with `Subtype.property`, which
would otherwise shadow it in dot notation.  It also matches the name used by the implementation.
-/
@[expose]
public def getProperty (v : ValueVersion) (name : String) : ValueVersion :=
  ⟨v.val.image (fun a => a.extend name), by simp⟩

@[simp]
public theorem val_getProperty {v : ValueVersion} {name : String} :
    (v.getProperty name).val = v.val.image (fun a => a.extend name) := rfl

/--
Reading a property distributes over `join`.  Equivalently: the value of `v.n` at a join point
depends only on the values of `v.n` along the incoming paths, not on how those paths were joined.

This is what makes the flattened representation of value versions faithful to the implementation:
it is precisely what the implementation's `_joinProperties` computes.
-/
public theorem getProperty_join (v₁ v₂ : ValueVersion) (name : String) :
    (join v₁ v₂).getProperty name = join (v₁.getProperty name) (v₂.getProperty name) := by
  apply ext; simp [Finset.image_union]

/-- Distinct values have distinct properties. -/
@[simp]
public theorem getProperty_inj {v₁ v₂ : ValueVersion} {name : String} :
    v₁.getProperty name = v₂.getProperty name ↔ v₁ = v₂ := by
  constructor
  · intro h
    exact ext (Finset.image_injective (Atom.extend_injective name) (val_inj h))
  · intro h; rw [h]

/-- A property of a value is never a root value. -/
@[simp]
public theorem getProperty_ne_root {v : ValueVersion} {name : String} {l : ℓ} :
    v.getProperty name ≠ root l := by
  intro h
  have hmem : (l, ([] : List String)) ∈ (v.getProperty name).val := by rw [h]; simp
  simp only [val_getProperty, Finset.mem_image] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  simp [Atom.extend] at ha

/-- Properties with distinct names are distinct, regardless of the values they are read from. -/
public theorem getProperty_name_inj {v₁ v₂ : ValueVersion} {name₁ name₂ : String}
    (h : v₁.getProperty name₁ = v₂.getProperty name₂) : name₁ = name₂ := by
  obtain ⟨a, ha⟩ := v₁.prop
  have hmem : a.extend name₁ ∈ (v₂.getProperty name₂).val := by
    rw [← h]; simp only [val_getProperty, Finset.mem_image]; exact ⟨a, ha, rfl⟩
  simp only [val_getProperty, Finset.mem_image] at hmem
  obtain ⟨b, -, hb⟩ := hmem
  have hpath : a.2 ++ [name₁] = b.2 ++ [name₂] := congrArg Prod.snd hb.symm
  simpa using congrArg List.getLast? hpath

/--
`join?` lifts `join` to optional value versions, which is how the specification currently models
write capture: a write-captured location has no value version, because flow analysis has given up on
tracking which value it holds.

`none` is therefore *absorbing*: if either incoming path has given up, so does the join.  This
matches the implementation, where `PromotionModel.join` computes
`newWriteCaptured = first.writeCaptured || second.writeCaptured` and stores a null value version
whenever `newWriteCaptured` holds.

TODO: once `writeCaptured` becomes a separate field of `PromotionModel`, with the invariant that it
holds iff the value version is absent, this lifting should become unnecessary.
-/
@[expose]
public def join? (v₁? v₂? : Option ValueVersion) : Option ValueVersion := Option.map₂ join v₁? v₂?

/-- The lifted join operation is idempotent (`join? v? v? = v?`). -/
@[simp]
public theorem join?_self (v? : Option ValueVersion) : join? v? v? = v? := by
  cases v? <;> simp [join?]

public instance join?.instIdempotentOp : Std.IdempotentOp (join? (ℓ := ℓ)) where
  idempotent := join?_self

/-- The lifted join operation is commutative (`join? v₁? v₂? = join? v₂? v₁?`). -/
public theorem join?_comm (v₁? v₂? : Option ValueVersion) : join? v₁? v₂? = join? v₂? v₁? :=
  Option.map₂_comm join_comm

public instance join?.instCommutative : Std.Commutative (join? (ℓ := ℓ)) where
  comm := join?_comm

/--
The lifted join operation is associative
(`join? (join? v₁? v₂?) v₃? = join? v₁? (join? v₂? v₃?)`).
-/
public theorem join?_assoc (v₁? v₂? v₃? : Option ValueVersion) :
    join? (join? v₁? v₂?) v₃? = join? v₁? (join? v₂? v₃?) :=
  Option.map₂_assoc join_assoc

public instance join?.instAssociative : Std.Associative (join? (ℓ := ℓ)) where
  assoc := join?_assoc

end «ValueVersion»
end FlowAnalysis
