module
public import FlowAnalysis.ValueVersion.Basic

namespace FlowAnalysis

/-
This module defines `ValueVersionImpl`, the implementation's model of a Dart `ValueVersion` object.

Dart's `ValueVersion` objects are identified by pointer identity. Each one has a map,
`_promotableProperties`, from property names to the `_PropertyValueVersion`s of the promotable
properties of the value it describes, so these maps form a trie of version objects. The root of
each trie is a version that wasn't produced by a property access (a declaration, a write, or a
join), and each property access walks one edge.

Flattening the trie identifies every Dart version by its root together with the path of property
names leading from the root to it. The root is identified by the specification's `ValueVersion`
(the implementation mints roots exactly where the specification does), and the flattened
`_promotableProperties` maps are `PromotionKeyStore.propertyKeys`.
-/

variable {ℓ : Type}

/--
Mirrors a Dart `ValueVersion` object. `roots` identifies the root of the `_promotableProperties`
trie it belongs to, and `path` is the list of property names leading from that root to it. So a
`_PropertyValueVersion` has a nonempty path, and any other version has an empty one.
-/
public structure ValueVersionImpl where
  roots : ValueVersion (ℓ := ℓ)
  path : List String

end FlowAnalysis
