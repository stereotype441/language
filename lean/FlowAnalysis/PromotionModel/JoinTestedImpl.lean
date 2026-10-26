module
public import Batteries.Data.List.Basic
public import Batteries.Data.List.Lemmas
public import DartLang.Types

/-!
# Joining lists of tested types

This module defines `joinTestedImpl`, the algorithm's join of the tested types of two promotion
models. It's a placeholder: it's plain list union, whereas Dart's `PromotionModel.joinTested`
computes the union in a particular order (starting from the longer list), and reuses an input list
when it can, rather than allocating a new one.
-/

namespace FlowAnalysis.PromotionModel
open DartLang

variable {τ : Type} [DartTypeRepr τ]

/--
The join of two lists of tested types: every type that's in either list (`ts₁ ∪ ts₂`). Agrees with
the specification's union of tested types up to order and duplicates, which is all that refinement
(`PromotionModelImpl.refines.tested`) compares.

TODO: mirror Dart's `PromotionModel.joinTested`.
-/
@[expose]
public def joinTestedImpl (ts₁ ts₂ : List τ) : List τ := ts₁ ∪ ts₂

end FlowAnalysis.PromotionModel
