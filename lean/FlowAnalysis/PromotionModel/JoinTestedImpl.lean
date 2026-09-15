module
public import Batteries.Data.List.Basic
public import Batteries.Data.List.Lemmas
public import FlowAnalysis.Types

namespace FlowAnalysis.PromotionModel

variable {τ : Type} [DartTypeRepr τ]

-- TODO: placeholder
@[expose]
public def joinTestedImpl (ts₁ ts₂ : List τ) : List τ := ts₁ ∪ ts₂

end FlowAnalysis.PromotionModel
