module

/-!
# The algorithm's value versions

This module defines `ValueVersionImpl`, the algorithmic model's representation of a Dart
`ValueVersion` object.

Flow analysis promotes *values*, not storage locations. The Dart implementation tells whether the
value held by a variable is "the same value" as the one it held earlier by object identity: it
allocates a fresh `ValueVersion` object each time a new value comes into existence (a declaration,
a write, or a join of two different values), and two reads saw the same value precisely when they
found the same object. The algorithm models that object identity by numbering versions in order of
allocation, so a version is just a natural number, and a fresh one is the next unused number (see
`PromotionKeyStore.newVersion`).

Each Dart `ValueVersion` also has a map, `_promotableProperties`, from property names to the
`_PropertyValueVersion`s of the promotable properties of the value it describes, so these maps form
a forest of version objects: each property access walks one edge. The algorithm keeps these maps in
the promotion key store (`PromotionKeyStore.promotableProperties`), indexed by version.

The specification has no value versions at all: it names a property by its root *variable*
instead (see `Key.property`).
-/

namespace FlowAnalysis

/--
Mirrors a Dart `ValueVersion` object, identified by the order in which it was allocated: versions
are numbered `0`, `1`, `2`, … (see `PromotionKeyStore.newVersion`).

An abbreviation rather than a structure, like `PromotionKey`, so that versions can be compared and
hashed without ceremony.
-/
public abbrev ValueVersionImpl := Nat

end FlowAnalysis
