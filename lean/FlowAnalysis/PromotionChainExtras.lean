module
import all FlowAnalysis.PromotionChain

namespace FlowAnalysis

variable {DartType : Type} [DartTypeRepr DartType]

/--
Alternative definition of `isValidPromotionChain` by index: `ts` is a valid promotion chain iff
`ts[i] < ts[j]` is equivalent to `j < i`.
-/
theorem isValidPromotionChain.by_index {ts : List DartType} :
    isValidPromotionChain ts ↔
    (∀ i j (hi : i < ts.length) (hj : j < ts.length), ts[i] < ts[j] ↔ j < i) := by
  cases hts : ts
  case nil => simp
  case cons T ts' =>
    constructor
    case mp =>
      intro hvalid_ts i j hi hj
      have hbound := isValidPromotionChain.head_bounds hvalid_ts
      have hvalid_ts' := isValidPromotionChain.tail_valid hvalid_ts
      cases i <;> cases j
      case zero.zero => simp; exact Std.lt_irrefl
      case zero.succ j' =>
        simp at hj ⊢
        specialize hbound ts'[j'] (by simp)
        exact Std.not_gt_of_lt hbound
      case succ.zero i' =>
        simp at hi ⊢
        specialize hbound ts'[i'] (by simp)
        assumption
      case succ.succ i' j' =>
        simp at hi hj ⊢
        rw [isValidPromotionChain.by_index] at hvalid_ts'
        specialize hvalid_ts' i' j' (by assumption) (by assumption)
        assumption
    case mpr =>
      simp
      intro hvalid_ts
      cases ts'
      case nil => simp
      case cons U ts'' =>
        have hU_lt_T : U < T := by
          specialize hvalid_ts 1 0 (by simp) (by simp); simp at hvalid_ts; assumption
        have hvalid_ts' : isValidPromotionChain (U::ts'') := by
          rw [isValidPromotionChain.by_index]
          intro i j hi hj
          specialize hvalid_ts (i + 1) (j + 1) (by lia) (by lia)
          simp at hvalid_ts
          assumption
        exact isValidPromotionChain.cons hU_lt_T hvalid_ts'

/--
Second alternative definition of `isPromotionChain` by index: `ts` is a valid promotion chain iff,
for all `i < j`, `ts[j] < ts[i]`.
-/
theorem isValidPromotionChain.by_index' {ts : List DartType} :
    isValidPromotionChain ts ↔
    (∀ i j (hij : i < j) (hj : j < ts.length), ts[j] < ts[i]) := by
  simp [isValidPromotionChain]
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hij hj; apply h; assumption
  · intro h i j hi hj hij; apply h; assumption
