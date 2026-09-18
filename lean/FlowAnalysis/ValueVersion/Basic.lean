module
public import Mathlib.Data.Finset.Basic
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
  - At a join point, the joined value is named by the *set* of values that flow into it.

Taking the set at join points (rather than minting a fresh name, as the implementation does) is what
makes join associative, commutative and idempotent on the nose, which in turn makes the
specification independent of the order in which branches happen to be joined.

Note what is *absent*: a value version says nothing about *where* the value lives.  The
implementation's value versions do carry that information implicitly, since the version of a
property is reached by walking down from the version of its target; but it is not needed here,
because of the following invariant of the implementation:

  Every version stored under a given promotion key describes a value at that key's property path.

Consequently two versions that are joined always describe values at the same property path, so the
path is a property of the *key*, not of the version.  It lives in `Key` instead.
-/

variable {ℓ : Type}

/--
Identifies the value held by a promotable location at a particular point in a function's execution.

Two locations hold the same value iff their `ValueVersion`s are equal, so promotions established for
one are available to the other.

A `ValueVersion` is a nonempty finite set of labels: a value that has not passed through a join
point is a single label, and a value produced by joining several control flow paths is the union of
the labels of the values that flow into it.  Nonemptiness holds because every value ultimately
originates at some labelled program point.
-/
public abbrev ValueVersion := {labels : Finset ℓ // labels.Nonempty}

local notation "ValueVersion" => ValueVersion (ℓ := ℓ)

namespace «ValueVersion»

/--
Simplification theorem: the labels of a `ValueVersion` are trivially nonempty, since a
`ValueVersion` can only be created if a witness to nonemptiness is provided.
-/
@[simp]
public theorem prop (v : ValueVersion) : v.val.Nonempty := v.2

/-- Extensionality: value versions may be proven equal by proving their label sets equal. -/
public theorem ext {v₁ v₂ : ValueVersion} : v₁.val = v₂.val → v₁ = v₂ := by
  intro h; apply Subtype.ext; assumption

/-- Injection: if value versions are equal then their label sets are equal. -/
public theorem val_inj {v₁ v₂ : ValueVersion} : v₁ = v₂ → v₁.val = v₂.val := by
  intro rfl; rfl

/-- Equality of value versions may be rewritten to equality of label sets and vice versa. -/
public theorem ext_iff {v₁ v₂ : ValueVersion} : v₁ = v₂ ↔ v₁.val = v₂.val := by
  constructor
  · apply val_inj
  · apply ext

/--
`root l` is the value that comes into existence at the program point labelled `l`.  It is distinct
from every other root, and from every value produced by joining two values that are not both `l`.
-/
@[expose]
public def root (l : ℓ) : ValueVersion := ⟨{l}, by simp⟩

@[simp]
public theorem val_root {l : ℓ} : (root l).val = {l} := rfl

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

-- Value versions are used as part of map keys, so decidable equality is required.  It is inherited
-- from `Finset` and `Subtype`; this `example` merely records that fact.
example : DecidableEq ValueVersion := inferInstance

/--
`join v₁ v₂` is the value observed at a join point whose incoming control flow paths hold `v₁` and
`v₂` respectively.
-/
@[expose]
public def join (v₁ v₂ : ValueVersion) : ValueVersion :=
  ⟨v₁.val ∪ v₂.val, v₁.prop.mono Finset.subset_union_left⟩

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
`join?` lifts `join` to optional value versions, which is how the specification models write
capture: a write-captured location has no value version, because flow analysis has given up on
tracking which value it holds.

`none` is therefore *absorbing*: if either incoming path has given up, so does the join.  This
matches the implementation, where `PromotionModel.join` computes
`newWriteCaptured = first.writeCaptured || second.writeCaptured` and stores a null value version
whenever `newWriteCaptured` holds.
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
