module
public import DartLang.Elements

/-!
# Promotion keys and references

This module defines `Key`, the specification's model of the Dart implementation's `PromotionKey`:
the name under which flow analysis records what it knows about one promotable part of the program.
It follows the promotion targets of the "Promotion targets" section of `flow-analysis.md`.

The implementation allocates an integer promotion key for each such part, lazily, as the part is
first mentioned.  The specification names them structurally instead:

  - a local variable is named by the label of its declaration (with `ℓ := AstPath`, the declaring
    statement's AST path; see `Scope`);
  - a property target is named by its *root*, the variable whose value it is reached from, together
    with the path of property names leading to it.

Naming a property target by its root variable, rather than by the value the variable holds, is what
`flow-analysis.md` does: `x._f` names whatever value is reached by reading `_f` from whatever `x`
holds.  So when `x` is assigned (or declared again), every property target rooted at `x` must be
forgotten (`FlowModel.eraseRooted`), because it now names a property of a different value.  The
implementation instead names a property by the identity of the value it was read from (its value
version), so that assigning `x` makes the old properties unreachable without erasing them; the
algorithmic model mirrors that, and `FlowAnalysis.AlgorithmTheorems` proves the two equivalent.

It also defines `Reference`, the model of the Dart implementation's `_Reference`: what flow analysis
knows about the location that an expression read, so that the location can be promoted when the
expression's value is.
-/

namespace FlowAnalysis
open DartLang

variable {τ : Type} {ℓ : Type}

/--
A part of the program being analyzed that is a candidate for type promotion, and the name under
which its promotion information is recorded.

TODO: property targets rooted at `this` and `super`, which `flow-analysis.md` already covers, once
the syntax has a `this` expression.
-/
public inductive Key where
  /--
  The local variable declared at `decl`. Naming a variable by its declaration, rather than by its
  name and type, mirrors Dart's `PromotionKeyStore`, which keys variables by the identity of their
  elements: an inner declaration that shadows an outer one is a distinct variable.
  -/
  | var (decl : ℓ)
  /--
  The property target reached by following `path` from the value of the variable declared at
  `root` (the property target is *rooted at* `root`).  `path` is never empty: a `Key` with an empty
  path would denote the variable itself, which is named by `Key.var root`.
  -/
  | property (root : ℓ) (path : List String)
  deriving DecidableEq

local notation "Key" => Key (ℓ := ℓ)

local notation "Property" => Property (τ := τ)

/--
Mirrors Dart's `_Reference`: what flow analysis knows about the location that an expression read,
so that the location can be promoted when the expression's value is.

There is one constructor for each kind of location. Dart's `_Reference` records a promotion key and
a value version for every kind of location; here a reference records the data of its key, and, for
a variable, whether flow analysis is tracking the value it read.
-/
public inductive Reference where
  /--
  A read of the variable declared at `decl`. `tracked` says whether flow analysis is tracking the
  value read: it is `false` only for a write-captured variable.

  Dart gives each read of a write-captured variable a fresh `ValueVersion` (`_variableReference`).
  Among the constructs modelled so far, nothing can reach a fresh version again, so recording that
  the value isn't tracked instead is observationally equivalent.
  TODO: revisit when write capture is modelled, since some constructs do reach the fresh
  version again. Cascades are one example (see `Reference.property?`); pattern matching and
  anonymous methods are others.
  -/
  | var (decl : ℓ) (tracked : Bool)
  /--
  A read of the property target reached by following `path` from the value of the variable declared
  at `root`. As for `Key.property`, `path` is never empty.
  -/
  | property (root : ℓ) (path : List String)

local notation "Reference" => Reference (ℓ := ℓ)

namespace «Reference»

/-- The key of the location that `r` read. -/
@[expose]
public def key : Reference → Key
  | .var decl _ => .var decl
  | .property root path => .property root path

/-- The key of a reference to a variable is the variable's key. -/
@[simp]
public theorem key_var {decl : ℓ} {tracked : Bool} :
    (Reference.var decl tracked).key = .var decl := rfl

/-- The key of a reference to a property target is `Key.property root path`. -/
@[simp]
public theorem key_property {root : ℓ} {path : List String} :
    (Reference.property root path).key = .property root path := rfl

/--
Whether flow analysis is tracking the value that `r` read: always for a property target, and for a
variable unless it's write captured (see `Reference.var`).
-/
@[expose]
public def tracked : Reference → Bool
  | .var _ tracked => tracked
  | .property _ _ => true

/-- A reference to a variable is tracked if it says so. -/
@[simp]
public theorem tracked_var {decl : ℓ} {tracked : Bool} :
    (Reference.var decl tracked).tracked = tracked := rfl

/-- A reference to a property target is always tracked. -/
@[simp]
public theorem tracked_property {root : ℓ} {path : List String} :
    (Reference.property root path).tracked = true := rfl

/--
The variable at the root of the location that `r` read: the variable itself, or the root of the
property target.
-/
@[expose]
public def root : Reference → ℓ
  | .var decl _ => decl
  | .property root _ => root

/-- The root of a reference to a variable is the variable. -/
@[simp]
public theorem root_var {decl : ℓ} {tracked : Bool} :
    (Reference.var decl tracked).root = decl := rfl

/-- The root of a reference to a property target is its root. -/
@[simp]
public theorem root_property {root : ℓ} {path : List String} :
    (Reference.property root path).root = root := rfl

/--
`r.property? p` is the reference to property `p` of the value that `r` read, or `none` if flow
analysis doesn't track that property. Mirrors the specification's **Property get** rule, and the
choice of key in Dart's `_handleProperty`.

It is `none` if `p` isn't promotable, or if the target's value isn't tracked (a write-captured
variable). Otherwise the property target has the same root as the target, and a path one name
longer.

TODO: revisit the write-captured case once constructs that reach a fresh version again are
modelled (see `Reference.var`). Cascades are one example: within a cascade, the
properties of a write-captured variable *can* be promoted. For example, even if `x` is write
captured, `x.._p!.f().._p.g()` is allowed: cascade semantics make it behave like
`let tmp = x; tmp._p!.f(); tmp._p.g();`, so the second `_p` needs no null check. Dart achieves this
because `cascadeExpression_afterTarget` holds the fresh version that `_variableReference` gives the
read of `x` in a temporary reference, through which every section of the cascade reaches it again.
Under root-variable keying, such a temporary would become the root of the property targets.
-/
@[expose]
public def property? (r : Reference) (p : Property) : Option Reference :=
  if p.isPromotable then
    match r with
    | .var decl tracked => if tracked then some (.property decl [p.name]) else none
    | .property root path => some (.property root (path ++ [p.name]))
  else none

end «Reference»
end FlowAnalysis
