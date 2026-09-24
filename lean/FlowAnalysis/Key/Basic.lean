module
public import FlowAnalysis.Elements
public import FlowAnalysis.ValueVersion.Basic

namespace FlowAnalysis

/-
This module defines `Key`, the specification's model of the Dart implementation's `PromotionKey`:
the name under which flow analysis records what it knows about one promotable part of the program.

The implementation allocates an integer promotion key for each such part, lazily, as the part is
first mentioned.  The specification names them structurally instead:

  - a local variable is named by itself;
  - a property is named by the value version of its target together with the path of property names
    leading to it.

Carrying the *path* here, rather than in `ValueVersion`, is deliberate.  The implementation's value
versions do implicitly encode a path, since a property's version is reached by walking down from its
target's version; but every version stored under a given promotion key describes a value at that
key's path, so the path is a property of the key.  Keeping it here is what lets `ValueVersion.join`
be plain set union, and hence unconditionally idempotent, commutative and associative.
-/

variable {τ : Type} {ℓ : Type}

local notation "Variable" => Variable (τ := τ)
local notation "ValueVersion" => ValueVersion (ℓ := ℓ)

/--
A part of the program being analyzed that is a candidate for type promotion, and the name under
which its promotion information is recorded.

TODO: `this` and `super`.
-/
public inductive Key where
  /-- A local variable. -/
  | var (v : Variable)
  /--
  The property reached by following `path` from a value whose version is `roots`.  `path` is never
  empty: a `Key` with an empty path would denote the target value itself, which is named by
  whichever key holds it.
  -/
  | loc (roots : ValueVersion) (path : List String)
  deriving DecidableEq

local notation "Key" => Key (τ := τ) (ℓ := ℓ)

namespace «Key»

/--
The path of property names leading from the value named by whichever key holds it, to the value
named by `k`.

TODO(stage 7): this is not always `[]` for a variable.  An anonymous method parameter is bound to
the value of the method's target, so it sits at the target's path; the implementation relies on this
when it makes field promotions of the target visible through the parameter.  Nothing modelled before
stage 7 can construct such a variable, so `[]` is correct for now.
-/
@[expose]
public def path : Key → List String
  | .var _ => []
  | .loc _ p => p

@[simp]
public theorem path_var {v : Variable} : (Key.var (ℓ := ℓ) v).path = [] := rfl

@[simp]
public theorem path_loc {r : ValueVersion} {p : List String} :
    (Key.loc (τ := τ) r p).path = p := rfl

/--
`k.property version name` is the key naming the property `name` of the value held at `k`, given that
the value held at `k` has version `version`.

Both arguments are needed: the version supplies the identity of the value whose property is being
read, and `k` supplies the path at which that value sits.  This is the one place where the
specification's shape differs from the implementation's, which reads the path off the version
itself; the two agree precisely because of the invariant described at the top of this module.
-/
@[expose]
public def property (k : Key) (version : ValueVersion) (name : String) : Key :=
  .loc version (k.path ++ [name])

@[simp]
public theorem path_property {k : Key} {version : ValueVersion} {name : String} :
    (k.property version name).path = k.path ++ [name] := rfl

/-- A property is never a variable. -/
@[simp]
public theorem property_ne_var {k : Key} {version : ValueVersion} {name : String}
    {v : Variable} : k.property version name ≠ .var v := by
  simp [property]

/--
Two property keys are equal exactly when they name the same property of the same value.

TODO(stage 5): the join of two flow models must *re-key* property entries, mapping `loc r₁ p` and
`loc r₂ p` to `loc (ValueVersion.join r₁ r₂) p`.  This is what the implementation's
`_joinProperties` computes, and it is the reason a property read distributes over a join.  A naive
pointwise join over a fixed set of keys would instead drop every property promotion, because the
keys on the two incoming paths differ.  Until Stage 5 adds the re-keying join, the model is sound
but less precise than Dart: after `if (b) { declare x; x._f! } else { declare x; x._f! }`, Dart
considers `x._f` promoted, but the model doesn't.
-/
@[simp]
public theorem property_inj {k₁ k₂ : Key} {version₁ version₂ : ValueVersion}
    {name₁ name₂ : String} :
    k₁.property version₁ name₁ = k₂.property version₂ name₂ ↔
      version₁ = version₂ ∧ k₁.path ++ [name₁] = k₂.path ++ [name₂] := by
  simp [property]

/-- Properties with distinct names are distinct, regardless of the values they are read from. -/
public theorem property_name_inj {k₁ k₂ : Key} {version₁ version₂ : ValueVersion}
    {name₁ name₂ : String} (h : k₁.property version₁ name₁ = k₂.property version₂ name₂) :
    name₁ = name₂ := by
  have hpath : k₁.path ++ [name₁] = k₂.path ++ [name₂] := (property_inj.mp h).2
  simpa using congrArg List.getLast? hpath

/-- Properties reached by distinct paths are distinct, regardless of their names. -/
public theorem property_path_inj {k₁ k₂ : Key} {version₁ version₂ : ValueVersion}
    {name₁ name₂ : String} (h : k₁.property version₁ name₁ = k₂.property version₂ name₂) :
    k₁.path = k₂.path := by
  have hpath : k₁.path ++ [name₁] = k₂.path ++ [name₂] := (property_inj.mp h).2
  rw [property_name_inj h] at hpath
  exact List.append_cancel_right hpath

end «Key»

local notation "Property" => Property (τ := τ)

/--
Mirrors Dart's `_Reference`: what flow analysis knows about the location that an expression read,
so that the location can be promoted when the expression's value is.
-/
public structure Reference where
  /-- The key of the location that was read. -/
  key : Key
  /--
  The version of the value that was read, which is the version held at `key` at the time.

  `none` only for a write-captured variable. Dart gives each read of such a variable a fresh
  `ValueVersion` (`_variableReference`). Among the constructs modelled so far, nothing can reach a
  fresh version again, so recording `none` instead is observationally equivalent. TODO(stage 7):
  revisit when write capture is modelled, since some constructs do reach the fresh version again.
  Cascades are one example (see `Reference.property?`); pattern matching and anonymous methods are
  others.
  -/
  version? : Option ValueVersion

local notation "Reference" => Reference (τ := τ) (ℓ := ℓ)

namespace «Reference»

/--
`r.property? p` is the reference to property `p` of the value that `r` read, or `none` if flow
analysis doesn't track that property. Mirrors the choice of key in Dart's `_handleProperty`.

It is `none` if `p` isn't promotable, or if the target's value isn't tracked (a write-captured
variable). Otherwise the property's key is determined by the target's key and version (see
`Key.property`), and its `version?` records the version of the target, since in the specification a
version doesn't carry a path (see `FlowAnalysis.ValueVersion`).

TODO(stage 7): revisit the write-captured case once constructs that reach a fresh version again are
modelled (see `Reference.version?`). Cascades are one example: within a cascade, the
properties of a write-captured variable *can* be promoted. For example, even if `x` is write
captured, `x.._p!.f().._p.g()` is allowed: cascade semantics make it behave like
`let tmp = x; tmp._p!.f(); tmp._p.g();`, so the second `_p` needs no null check. Dart achieves this
because `cascadeExpression_afterTarget` holds the fresh version that `_variableReference` gives the
read of `x` in a temporary reference, through which every section of the cascade reaches it again.
So a `version?` of `none`, which can't be reached again, will no longer do (see
`Reference.version?`).
-/
@[expose]
public def property? (r : Reference) (p : Property) : Option Reference :=
  if p.isPromotable then r.version?.map fun v => ⟨r.key.property v p.name, some v⟩ else none

/--
A reference to a property records the version named by its key.

This is the specification's counterpart of Dart's assertion in `_handleProperty` that the promotion
model found for a property holds the version the property was read from, and it is what makes
`FlowModel.infoFor` preserve `FlowModel.WellFormed`.
-/
@[expose]
public def WellFormed (r : Reference) : Prop :=
  ∀ v q, r.key = .loc v q → r.version? = some v

/-- A reference produced by `property?` is well formed. -/
public theorem WellFormed.property? {r r' : Reference} {p : Property}
    (h : r.property? p = some r') : r'.WellFormed := by
  intro v q hkey
  simp only [Reference.property?] at h
  split at h
  case isTrue =>
    obtain ⟨v', -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [Key.property, Key.loc.injEq] at hkey
    rw [hkey.1]
  case isFalse => simp at h

end «Reference»
end FlowAnalysis
