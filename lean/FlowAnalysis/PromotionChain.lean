module
import Aesop
import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
public meta import FlowAnalysis.SimpleTypes
public import FlowAnalysis.Types
import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Order
import Mathlib.Tactic.WLOG

namespace FlowAnalysis

-- Allows the use of `<+` notation for `List.Sublist`.
open scoped List

variable {τ : Type} [DartTypeRepr τ]

/-- A list of types `c` is a promotion chain iff, for all `i < c.length - 1`, `c[i + 1] < c[i]`. -/
public def isPromotionChain (c : List τ) : Prop :=
    ∀ i (h : i < c.length - 1), c[i + 1] < c[i]

namespace isPromotionChain

/--
Equivalent formulation of `isPromotionChain` in terms of Lean's built-in notation of a chain (which
is defined recursively, so it's a bit more convenient to use in proofs).
-/
theorem iff_isChain (c : List τ) :
    isPromotionChain c ↔ c.IsChain (fun T U => U < T) := by
  rw [isPromotionChain, List.isChain_iff_getElem]
  constructor
  · intro h i hi; apply h; omega
  · intro h i hi; apply h

lemma iff_pairwise (c : List τ) :
    isPromotionChain c ↔ c.Pairwise (fun T U => U < T) := by
  rw [iff_isChain, List.isChain_iff_pairwise]

/-- Equivalently, `c` is a promotion chain iff, for all `0 ≤ i < j < c.length`, `c[j] < c[i]`. -/
theorem iff_pairwise_getElem (c : List τ) :
    isPromotionChain c ↔ ∀ i j (hij : i < j) (hj : j < c.length), c[j] < c[i] := by
  rw [iff_pairwise, List.pairwise_iff_getElem]
  constructor
  · intro h i j hij hj; apply h; assumption
  · intro h i j hi hj hij; apply h; assumption

/-- The empty list is a promotion chain. -/
@[simp]
theorem empty : isPromotionChain ([] : List τ) := by
  simp [isPromotionChain]

/-- A list with just one element is a promotion chain. -/
@[simp]
theorem single : ∀ T : τ, isPromotionChain [T] := by
  simp [isPromotionChain]

/-- The tail of a promotion chain is also a promotion chain. -/
public theorem tail_valid {T : τ} {ts : List τ} (hvalid : isPromotionChain (T::ts)) :
    isPromotionChain ts := by
  simp [iff_isChain] at hvalid ⊢
  exact List.IsChain.of_cons hvalid

/-- The head of a valid promotion chain is a strict supertype of every type in the tail. -/
public theorem head_bounds {T : τ} {ts : List τ} (hvalid : isPromotionChain (T::ts)) :
    ∀ T' ∈ ts, T' < T := by
  simp [iff_pairwise] at hvalid
  aesop

/-- The head of a valid promotion chain is not in the tail. -/
lemma head_notIn_tail {T : τ} {ts : List τ} (hvalid : isPromotionChain (T::ts)) : T ∉ ts := by
  have := hvalid.head_bounds T
  grind

public theorem cons {T : τ} {ts : List τ} (hbounds : ∀ T' ∈ ts, T' < T)
    (hvalid : isPromotionChain ts) :
    isPromotionChain (T::ts) := by
  simp [iff_pairwise] at hvalid ⊢; grind

/--
Any sublist of a promotion chain is also a promotion chain.

In the spec we use the term `subsequence` since `sublist` in programming usually implies contiguity.
We use the term `sublist` here to match Lean's terminology.
-/
public theorem sublist {ts₁ ts₂ : List τ} (hsublist : ts₁ <+ ts₂) (hvalid₂ : isPromotionChain ts₂) :
    isPromotionChain ts₁ := by
  simp [iff_pairwise] at hvalid₂ ⊢
  apply List.Pairwise.sublist hsublist
  assumption

end isPromotionChain

/--
For convenience, define `PromotionChain` as a subtype of `List τ`.
-/
public abbrev PromotionChain := {ts : List τ // isPromotionChain ts}

local notation "PromotionChain" => PromotionChain (τ := τ)

namespace «PromotionChain»

@[simp]
public theorem isValid (c : PromotionChain) : isPromotionChain c.val := c.property

/-- Extensionality: promotion chains may be proven equal by proving their lists equal. -/
public theorem ext {c₁ c₂ : PromotionChain} : c₁.val = c₂.val → c₁ = c₂ := by
  intro h; apply Subtype.ext; assumption

/-- Injection: if promotion chains are equal then their values are equal. -/
public theorem inj {c₁ c₂ : PromotionChain} : c₁ = c₂ → c₁.val = c₂.val := by
  intro rfl; rfl

/-- Equality of promotion chains may be rewritten to equality of values and vice versa. -/
public theorem eq_iff_values_eq {c₁ c₂ : PromotionChain} : c₁ = c₂ ↔ c₁.val = c₂.val := by
  constructor
  · apply inj
  · apply ext

/-- The empty promotion chain. -/
public def empty : PromotionChain := ⟨[], by simp⟩

public def take (n : Nat) (c : PromotionChain) : PromotionChain := .mk (c.val.take n) $ by
  suffices h : c.val.take n <+ c.val by apply isPromotionChain.sublist h c.property
  exact List.take_sublist n c.val

@[simp]
public theorem take.val {n : Nat} {c : PromotionChain} : (c.take n).val = c.val.take n := by rfl

public def drop (n : Nat) (c : PromotionChain) :
    PromotionChain := .mk (c.val.drop n) $ by
  suffices h : c.val.drop n <+ c.val by apply isPromotionChain.sublist h c.property
  exact List.drop_sublist n c.val

@[simp]
public theorem drop.zero (c : PromotionChain) : drop 0 c = c := by rfl

@[simp]
public theorem drop.val {n : Nat} {c : PromotionChain} : (c.drop n).val = c.val.drop n := by rfl

@[simp]
public theorem drop.of_val {n : Nat} {c : PromotionChain} {hvalid : isPromotionChain (c.val.drop n)} :
    ⟨c.val.drop n, hvalid⟩ = c.drop n := by rfl

public instance instEmptyCollection : EmptyCollection (PromotionChain) where
  emptyCollection := empty

@[simp]
public theorem eq_empty {h : isPromotionChain []} : (⟨[], h⟩ : PromotionChain) = ∅ :=
  by rfl

@[simp]
public theorem empty_types : (∅ : PromotionChain).val = [] := by rfl

public theorem empty_if_empty_types {c : PromotionChain} :
    c.val = [] → c = ∅ := by
  intro h; apply ext; simp_all

/-- A promotion chain containing a single type. -/
public def single (T : τ) : PromotionChain := ⟨[T], by simp⟩

@[simp]
public theorem single_types {T : τ} : (single T).val = [T] := by rfl

/-- A promotion chain `c` is strictly bounded by `T` iff `T::c` is a promotion chain. -/
public def strictlyBoundedBy (c : PromotionChain) (T : τ) : Prop := isPromotionChain (T::c)

def filter (p : τ → Bool) (c : PromotionChain) : PromotionChain := .mk (c.val.filter p) $ by
  rcases c with ⟨ts, hvalid⟩
  rw [isPromotionChain.iff_pairwise]
  apply List.Pairwise.filter
  rw [←isPromotionChain.iff_pairwise]
  simp [hvalid]

lemma eq_if_typeSets_eq : ∀ (c₁ c₂ : PromotionChain),
    c₁.val.toFinset = c₂.val.toFinset → c₁ = c₂ := by
  rintro ⟨ts₁, hvalid₁⟩ ⟨ts₂, hvalid₂⟩; simp
  cases ts₁
  case nil => simp; intro h; rw [←List.toFinset_eq_empty_iff]; aesop
  case cons T₁ ts₁' =>
    cases ts₂
    case nil => simp
    case cons T₂ ts₂' =>
      simp
      by_cases T₁ = T₂
      case pos heq =>
        subst heq
        intro hinsert
        suffices h : ts₁'.toFinset = ts₂'.toFinset by
          have := eq_if_typeSets_eq ⟨ts₁', hvalid₁.tail_valid⟩ ⟨ts₂', hvalid₂.tail_valid⟩
          simp_all
        simp [Finset.ext_iff] at hinsert ⊢
        intro T; specialize hinsert T
        by_cases T = T₁
        case neg hne => simp [hne] at hinsert; assumption
        case pos heq => grind [hvalid₁.head_notIn_tail, hvalid₂.head_notIn_tail]
      case neg hne =>
        simp [hne]; intro hcontra; simp [Finset.ext_iff] at hcontra
        have hT₁_lt_T₂ : T₁ < T₂ := by grind [isPromotionChain.head_bounds hvalid₂]
        have hT₂_lt_T₁ : T₂ < T₁ := by grind [isPromotionChain.head_bounds hvalid₁]
        grind

/-- Two promotion chains are equal iff they contain the same set of types. -/
public theorem eq_iff_typeSets_eq (c₁ c₂ : PromotionChain) :
    c₁ = c₂ ↔ c₁.val.toFinset = c₂.val.toFinset := by
  constructor
  · intro rfl; rfl
  · apply eq_if_typeSets_eq

public theorem eq_iff_membership (c₁ c₂ : PromotionChain) :
    c₁ = c₂ ↔ ∀ T, T ∈ c₁.val ↔ T ∈ c₂.val := by
  rw [eq_iff_typeSets_eq, Finset.ext_iff]; simp

/--
The sublist relation holds between two promotion chains iff membership in the former implies
membership in the latter.
-/
public theorem sublist_iff_membership (c₁ c₂ : PromotionChain) :
    c₁.val <+ c₂.val ↔ ∀ T, T ∈ c₁.val → T ∈ c₂.val := by
  constructor
  · intro hsublist T hT_in_c₁
    apply hsublist.mem; assumption
  · intro hsubset
    suffices c₁ = c₂.filter (· ∈ c₁.val) by rw [this]; simp [filter]
    simp_all [eq_iff_membership, filter]

public abbrev isCommonSublist (c c₁ c₂ : PromotionChain) : Prop := c.val <+ c₁.val ∧ c.val <+ c₂.val

public abbrev isGreatestCommonSublist (c c₁ c₂ : PromotionChain) : Prop :=
  c.isCommonSublist c₁ c₂ ∧ ∀ c' : PromotionChain, c'.isCommonSublist c₁ c₂ → c'.val <+ c.val

-- TODO: needed?
/-- If a type is in both c₁ and c₂, it's in a greatest common sublist. -/
lemma isGreatestCommonSublist.mem {c c₁ c₂ : PromotionChain} :
    c.isGreatestCommonSublist c₁ c₂ → ∀ T, T ∈ c₁.val → T ∈ c₂.val → T ∈ c.val := by
  rintro ⟨hc_is_commonSublist, hc_is_greatest⟩ T hT_in_c₁ hT_in_c₂
  suffices (single T).isCommonSublist c₁ c₂ by specialize hc_is_greatest (.single T) this; simp_all
  simp_all [isCommonSublist]

-- TODO: needed?
/-- If a type is in a greatest common sublist of c₁ and c₂, then it's in c₁. -/
lemma isGreatestCommonSublist.mem_left {c c₁ c₂ : PromotionChain} {T : τ} :
    c.isGreatestCommonSublist c₁ c₂ → T ∈ c.val → T ∈ c₁.val := by grind

-- TODO: needed?
/-- If a type is in a greatest common sublist of c₁ and c₂, then it's in c₂. -/
lemma isGreatestCommonSublist.mem_right {c c₁ c₂ : PromotionChain} {T : τ} :
    c.isGreatestCommonSublist c₁ c₂ → T ∈ c.val → T ∈ c₂.val := by grind

/-- The unique greatest common sublist of two promotion chains is called their `join`. -/
public def join (c₁ c₂ : PromotionChain) := c₁.filter (· ∈ c₂.val)

theorem join.spec (c₁ c₂ : PromotionChain) : (c₁.join c₂).isGreatestCommonSublist c₁ c₂ := by
  simp [join]
  constructor
  · constructor
    · simp [filter]
    · rw [sublist_iff_membership]; simp [filter]
  · rintro c' ⟨hc'_sublist_c₁, hc'_sublist_c₂⟩
    rw [sublist_iff_membership] at hc'_sublist_c₁ hc'_sublist_c₂ ⊢
    intro T hT_in_c'
    simp [filter, hc'_sublist_c₁ T hT_in_c', hc'_sublist_c₂ T hT_in_c']

/--
The computable definition of `join` above proves that a greatest common sublist always exists.
-/
lemma greatestCommonSublist_exists (c₁ c₂ : PromotionChain) :
    ∃ c : PromotionChain, c.isGreatestCommonSublist c₁ c₂ := by
  exists c₁.filter (· ∈ c₂.val)
  apply join.spec

/-- The join is the unique greatest common sublist. -/
public theorem greatestCommonSublist_unique (c₁ c₂ : PromotionChain) :
    ∀ c : PromotionChain, c.isGreatestCommonSublist c₁ c₂ → c = c₁.join c₂ := by
  intro c hc
  let c' := c₁.join c₂
  have hc' := join.spec c₁ c₂
  rw [eq_iff_membership]; grind

@[simp]
public theorem join.membership (c₁ c₂ : PromotionChain) (T : τ) :
    T ∈ (c₁.join c₂).val ↔ T ∈ c₁.val ∧ T ∈ c₂.val := by
  obtain ⟨⟨hjoin_sublist_c₁, hjoin_sublist_c₂⟩, hgreatest⟩ := join.spec c₁ c₂
  rw [PromotionChain.sublist_iff_membership] at hjoin_sublist_c₁ hjoin_sublist_c₂
  constructor
  · grind
  · simp; intro hT_in_c₁ hT_in_c₂
    specialize hgreatest (.single T) (by simp_all [isCommonSublist])
    rw [PromotionChain.sublist_iff_membership] at hgreatest; simp at hgreatest; assumption

public theorem join.eq_iff (c c₁ c₂ : PromotionChain) :
    c₁.join c₂ = c ↔ ∀ T, T ∈ c₁.val ∧ T ∈ c₂.val ↔ T ∈ c.val := by
  constructor
  · intro rfl T; simp
  · rw [eq_iff_membership]; simp

@[simp]
public theorem join.sublist_left (c₁ c₂ : PromotionChain) :
    c₁.val <+ c₂.val → c₁.join c₂ = c₁ := by
  intro h; rw [eq_iff]; intro T; grind

@[simp]
public theorem join.sublist_right (c₁ c₂ : PromotionChain) :
    c₂.val <+ c₁.val → c₁.join c₂ = c₂ := by
  intro h; rw [eq_iff]; intro T; grind

/-- The join operation is idempotent (`join c c = c`). -/
@[simp]
public theorem join.idempotent (c : PromotionChain) : c.join c = c := by
  rw [eq_iff]; grind

public instance join.instIdempotentOp :
    Std.IdempotentOp (join (τ := τ)) where
  idempotent := idempotent

/-- The join operation is commutative (`c₁.join c₂ = c₂.join c₁`). -/
public theorem join.commutative (c₁ c₂ : PromotionChain) : c₁.join c₂ = c₂.join c₁ := by
  rw [eq_iff_membership]; simp; aesop

public instance join.instCommutative : Std.Commutative (join (τ := τ)) where
  comm := commutative

/-- The join operation is associative (`(c₁.join c₂).join c₃ = c₁.join (c₂.join c₃)`) -/
public theorem join.associative (c₁ c₂ c₃ : PromotionChain) :
    (c₁.join c₂).join c₃ = c₁.join (c₂.join c₃) := by
  rw [eq_iff_membership]; simp; aesop

public instance join.instAssociative : Std.Associative (join (τ := τ)) where
  assoc := associative

@[simp]
public theorem join.left_empty :
    ∀ c : PromotionChain, (∅ : PromotionChain).join c = ∅ := by
  intro c; rw [eq_iff]; simp

@[simp]
public theorem join.right_empty : ∀ c : PromotionChain, c.join ∅ = ∅ := by
  intro c; rw [eq_iff]; simp

-- TODO: needed?
lemma filter_refineGuard_notIn {α} {P : α → Bool} {l : List α} {y : α} [DecidableEq α] : y ∉ l →
    List.filter (fun x => decide (x = y) || P x) l =
    List.filter (fun x => P x) l := by
  intro h; apply List.filter_congr; simp; intro x hx_in_l rfl; contradiction

@[simp]
lemma join.heads_eq_valid {T : τ} {ts₁' ts₂' : List τ}
    {hvalid₁ : isPromotionChain (T::ts₁')} {hvalid₂ : isPromotionChain (T::ts₂')} :
    isPromotionChain (T :: join ⟨ts₁', hvalid₁.tail_valid⟩ ⟨ts₂', hvalid₂.tail_valid⟩) := by
  apply isPromotionChain.cons <;> simp
  intro T' hT'_in_ts₁' hT'_in_ts₂'
  apply hvalid₁.head_bounds; assumption

@[simp]
public theorem join.heads_eq {T : τ} {ts₁' ts₂' : List τ}
    {hvalid₁ : isPromotionChain (T::ts₁')} {hvalid₂ : isPromotionChain (T::ts₂')} :
    join ⟨T::ts₁', hvalid₁⟩ ⟨T::ts₂', hvalid₂⟩ =
    ⟨T :: join ⟨ts₁', hvalid₁.tail_valid⟩ ⟨ts₂', hvalid₂.tail_valid⟩, by simp_all⟩ := by
  rw [eq_iff_membership]; intro T'
  constructor <;> simp <;> grind

@[simp]
public theorem join.heads_ne_le {T₁ T₂ : τ} {ts₁' ts₂' : List τ}
    {hvalid₁ : isPromotionChain (T₁::ts₁')} {hvalid₂ : isPromotionChain (T₂::ts₂')}
    (hne : ¬T₁ = T₂) (hle : T₁ ≤ T₂) :
    join ⟨T₁::ts₁', hvalid₁⟩ ⟨T₂::ts₂', hvalid₂⟩ =
    join ⟨T₁::ts₁', hvalid₁⟩ ⟨ts₂', hvalid₂.tail_valid⟩ := by
  rw [eq_iff_membership]; intro T; simp
  intro h rfl; simp [show T = T₁ ↔ False by grind] at h
  have := hvalid₁.head_bounds T h
  grind

@[simp]
public theorem join.heads_ne_notLe {T₁ T₂ : τ} {ts₁' ts₂' : List τ}
    {hvalid₁ : isPromotionChain (T₁::ts₁')} {hvalid₂ : isPromotionChain (T₂::ts₂')}
    (hne : ¬T₁ = T₂) (hnotLe : ¬T₁ ≤ T₂) :
    join ⟨T₁::ts₁', hvalid₁⟩ ⟨T₂::ts₂', hvalid₂⟩ =
    join ⟨ts₁', hvalid₁.tail_valid⟩ ⟨T₂::ts₂', hvalid₂⟩ := by
  rw [eq_iff_membership]; intro T; simp
  intro h rfl; simp [show T = T₂ ↔ False by grind] at h
  have := hvalid₂.head_bounds T h
  grind

@[grind =>]
public theorem val_notEmpty_if_notEmpty {c : PromotionChain} : ¬c = ∅ → ¬c.val = [] := by
  contrapose; rcases c; simp; intro rfl; simp

@[simp]
public theorem join.left_empty' {c₁ c₂ : PromotionChain} : c₁.val = [] → c₁.join c₂ = ∅ := by
  intro h; simp [show c₁ = ∅ by grind]

@[simp]
public theorem join.right_empty' {c₁ c₂ : PromotionChain} : c₂.val = [] → c₁.join c₂ = ∅ := by
  intro h; simp [show c₂ = ∅ by grind]

end «PromotionChain»
