/-
Proofs of soundness and completeness of the algorithmic implementation in `FlowAnalysis.algorithm`.
-/

module
import Aesop
public import Lean
import Mathlib.Logic.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.SplitIfs
import Std.Data.HashMap
import FlowAnalysis.Algorithm
import FlowAnalysis.Elaboration
import FlowAnalysis.PromotionChain.JoinImpl
import Mathlib.Tactic.Order

section
open Lean Elab Tactic Meta

/--
`by_cases_iff h` splits a hypothesis `h : P ↔ Q` into two subgoals:
- `pos`: assuming both `P` and `Q` are true.
- `neg`: assuming both `¬P` and `¬Q` are true.
-/
elab "by_cases_iff" t:term : tactic => withMainContext do
  -- 1. Split the equivalence: creates a temporary `Or` hypothesis and case-splits it
  evalTactic (← `(tactic| have h_or := iff_iff_and_or_not_and_not.mp $t))
  evalTactic (← `(tactic| cases h_or <;> rename_i h_or <;> cases h_or))

  -- 2. Grab the two resulting subgoals and assign the `pos` and `neg` tags
  let goals ← getGoals
  match goals with
  | g1 :: g2 :: rest =>
    g1.setTag `pos
    g2.setTag `neg
    setGoals (g1 :: g2 :: rest)
  | _ =>
    -- Fail silently or log nothing if the goal was solved during splitting
    pure ()
end

namespace FlowAnalysis

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]
variable {cfg : Config}

local notation "AlgM" => AlgM (τ := τ)
local notation "Expr" => Expr (τ := τ)
local notation "ExprModel" => ExprModel (τ := τ)
local notation "ExprModelImpl" => ExprModelImpl (τ := τ)
local notation "FlowModel" => FlowModel (τ := τ)
local notation "FlowModelImpl" => FlowModelImpl (τ := τ)
local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "Stmt" => Stmt (τ := τ)
local notation "PromotionModel" => PromotionModel (τ := τ)
local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ)

@[simp]
theorem AlgM_get_eq {fm} :
  (get : AlgM _) cfg fm = Except.ok (fm, fm) := rfl

@[simp]
theorem AlgM_pure_eq {α fm} {a : α} :
  (pure a : AlgM _) cfg fm = Except.ok (a, fm) := rfl

@[simp]
theorem AlgM_bind_eq {α β : Type} {x : AlgM α} {fm : FlowModelImpl}
    {f : α → AlgM β} :
  (x >>= f) cfg fm = match x cfg fm with
                 | Except.ok (a, hm') => f a cfg hm'
                 | Except.error e => Except.error e := by
  simp [bind, ReaderT.bind, StateT.bind]
  cases x cfg fm <;> rfl

@[simp]
theorem AlgM_map_eq {α β : Type} {fm : FlowModelImpl} {f : α → β} {x : AlgM α} :
  (f <$> x) cfg fm = match x cfg fm with
                 | Except.ok (a, hm') => Except.ok (f a, hm')
                 | Except.error e => Except.error e := by
  dsimp [Functor.map, StateT.instMonad, StateT.map, StateT.bind, StateT.pure, ExceptT.bind, ExceptT.pure, bind, pure]
  cases x cfg fm <;> trivial

@[simp]
theorem AlgM_modify_eq {f fm} :
    (modify : _ → AlgM _) f cfg fm = Except.ok ((), f fm) := rfl

@[simp]
theorem AlgM_set_eq {fm fm'} :
    (set : _ → AlgM _) fm' cfg fm = Except.ok ((), fm') := rfl

@[simp]
theorem AlgM_throw_eq_ok_contra {α e fmI₀ x fmI} :
    (throw e : AlgM α) cfg fmI₀ = Except.ok (x, fmI) ↔ False := by
  constructor
  case mp => intro h; contradiction
  case mpr => intro h; exfalso; assumption

/--
`fmI.PromotionInfoRefinesAt fm v` says that the `promotionInfo` fields of the algorithm's flow model `fmI` and the
specification's flow model `fm` agree about the variable `v`: either neither flow model has an entry
for `v`, or both do, and the algorithm's variable model refines the specification's.
-/
inductive FlowModelImpl.PromotionInfoRefinesAt (fmI : FlowModelImpl)
    (fm : FlowModel) (v : Variable) : Prop where
  /-- `v` is absent from both flow models. -/
  | absent (hlookupI : fmI.promotionInfo[v]? = none) (hlookup : fm.promotionInfo v = none)
  /-- `v` is present in both flow models, and their variable models are related by `refines`. -/
  | present
        {pmI : PromotionModelImpl} {pm : PromotionModel} (hlookupI : fmI.promotionInfo[v]? = some pmI)
        (hlookup : fm.promotionInfo v = some pm) (hrefines_vm : pmI.refines pm)

/--
`fmI.refines fm` says that the algorithm's flow model `fmI` faithfully represents the
specification's flow model `fm`.
-/
structure FlowModelImpl.refines (fmI : FlowModelImpl)
    (fm : FlowModel) : Prop where
  /-- The two flow models' `promotionInfo` fields agree about every variable. -/
  promotionInfos (v : Variable) : fmI.PromotionInfoRefinesAt fm v

/-- The algorithm's initial flow model refines the specification's initial flow model. -/
theorem FlowModelImpl.refines.empty :
    (.empty : FlowModelImpl).refines FlowModel.empty := by
  constructor; intro v
  exact .absent (by simp [FlowModelImpl.empty]) (by simp [FlowModel.empty])

/--
A flow model refined by `fmI` maps every variable to `none` precisely when `fmI`'s `promotionInfo` is empty.
-/
theorem FlowModelImpl.refines.isEmpty {fmI : FlowModelImpl} {fm : FlowModel}
    (hrefines : fmI.refines fm) :
    fmI.promotionInfo.isEmpty ↔ ∀ v, fm.promotionInfo v = none := by
  constructor
  case mp =>
    intro hemptyI v
    have : fmI.promotionInfo[v]? = none := by exact Std.HashMap.getElem?_of_isEmpty hemptyI
    cases hrefines.promotionInfos v <;> simp_all
  case mpr =>
    intro hempty
    rw [Std.HashMap.isEmpty_iff_forall_not_mem]
    intro v
    cases hrefines.promotionInfos v <;> simp_all

/--
An algorithmic flow model whose `promotionInfo` is empty refines the specification's empty flow model.

The conclusion is spelled out as `⟨fun _ => none⟩` rather than `FlowModel.empty` because `simp`
matches conclusions syntactically; stating it in terms of `FlowModel.empty` would stop this lemma
from firing on the goals that arise in `FlowModelImpl.refines.join`.
-/
@[simp]
theorem FlowModelImpl.refines.empty_of_isEmpty {fmI : FlowModelImpl}
    (hempty : fmI.promotionInfo.isEmpty) : fmI.refines ⟨fun _ => none⟩ := by
  constructor; intro v
  exact .absent (Std.HashMap.getElem?_of_isEmpty hempty) (by simp)

/--
A single algorithmic flow model can't refine two different specification flow models, since it
determines each variable's variable model up to `PromotionModelImpl.refines`, which is itself unique.
-/
theorem FlowModelImpl.refines.unique {fmI : FlowModelImpl} {fm₁ fm₂ : FlowModel}
    (hrefines₁ : fmI.refines fm₁) (hrefines₂ : fmI.refines fm₂) : fm₁ = fm₂ := by
  apply FlowModel.extensionality; intro v
  cases hrefines₁.promotionInfos v
  case absent hlookupI₁ hlookup₁ => cases hrefines₂.promotionInfos v <;> simp_all
  case present pmI₁ pm₁ hlookupI₁ hlookup₁ hrefines_vm₁ =>
    cases hrefines₂.promotionInfos v
    case absent hlookupI₂ hlookup₂ => simp_all
    case present pmI₂ pm₂ hlookupI₂ hlookup₂ hrefines_vm₂ =>
      -- `fmI` has a single entry for `v`, so `pm₁` and `pm₂` refine the same `PromotionModelImpl`,
      -- and `PromotionModelImpl.refines` determines the variable model it refines uniquely.
      have hvmIs : pmI₁ = pmI₂ := by simp_all
      subst hvmIs
      rw [hlookup₁, hlookup₂, hrefines_vm₁.unique hrefines_vm₂]

/--
Refinement is preserved by adding a variable to both flow models, provided the variable models
being added are themselves related by `refines`.
-/
@[simp]
theorem FlowModelImpl.refines.insert {fmI : FlowModelImpl} {fm : FlowModel}
    {pmI : PromotionModelImpl} {pm : PromotionModel} (v : Variable)
    (hrefines_fm : fmI.refines fm) (hrefines_vm : pmI.refines pm) :
    (FlowModelImpl.mk (fmI.promotionInfo.insert v pmI)).refines (fm.set v pm) := by
  constructor; intro v'
  by_cases heq : v = v' <;> subst_eqs
  case pos =>
    exact .present (by simp) (by simp) hrefines_vm
  case neg =>
    cases hrefines_fm.promotionInfos v'
    case absent hlookupI hlookup =>
      exact .absent (by simp_all) (by simp_all)
    case present pmI' pm' hlookupI hlookup hrefines_vm' =>
      exact .present (by simp_all [Std.HashMap.getElem?_insert]) (by simp_all) hrefines_vm'

/--
Running the algorithm's `tryPromoteImpl` on a flow model that refines `fm` succeeds, and produces a
flow model that refines the result of the specification's `FlowModel.tryPromote`.
-/
theorem FlowModelImpl.refines.tryPromote
    {fmI : FlowModelImpl} {fm : FlowModel} (hrefines : fmI.refines fm) ref? T :
    ∃ fmI', tryPromoteImpl ref? T cfg fmI = Except.ok ((), fmI') ∧
    fmI'.refines (fm.tryPromote ref? T) := by
  simp [tryPromoteImpl, FlowModel.tryPromote]
  cases ref? <;> simp_all
  case none => exists fmI
  case some ref =>
    cases ref; simp_all
    case var v =>
      cases hrefines.promotionInfos v <;> simp_all
      case absent => exists fmI
      case present pmI pm hlookupI hlookup hrefines_vm =>
        rw [hrefines_vm.currentTypes]
        by_cases hT_lt_current : T < pm.currentType v.type <;> simp_all
        case neg => exists fmI
        case pos =>
          -- Unlike `FlowModel.tryPromote`, which promotes using `PromotionChain.tryPromote`, the
          -- algorithm checks explicitly whether appending `T` produces a valid promotion chain, and
          -- leaves `promotionInfo` untouched if it doesn't. So we need to consider the two cases separately.
          by_cases hchain : isPromotionChain (pmI.promotedTypes ++ [T]) <;> simp_all
          case pos =>
            -- `T` was appended to `v`'s promotion chain, in both the algorithm and the spec.
            exists ⟨fmI.promotionInfo.insert v {pmI with promotedTypes := pmI.promotedTypes ++ [T]}⟩
            refine ⟨rfl, ?_⟩
            exact hrefines.insert v (hrefines_vm.promote hchain)
          case neg =>
            -- Neither the algorithm nor the spec promoted `v`, so neither one changed its state;
            -- for the spec, this is because `PromotionChain.tryPromote` was a no-op, so the `set`
            -- assigned `v` the variable model it already had.
            exists fmI
            refine ⟨rfl, ?_⟩
            rw [hrefines_vm.tryPromote_eq_self hchain, FlowModel.set_self hlookup]
            exact hrefines

section
variable {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {f : β → β → β} {m₁ m₂ : Std.HashMap α β}

/-- A key that's absent from the first map being merged is absent from the merged map. -/
theorem mergeMaps_none₁ {k : α} : k ∉ m₁ → k ∉ mergeMaps f m₁ m₂ := by
  simp_all [mergeMaps, Std.HashMap.mem_filterMap]

/-- A key that's absent from the second map being merged is absent from the merged map. -/
theorem mergeMaps_none₂ {k : α} : k ∉ m₂ → k ∉ mergeMaps f m₁ m₂ := by
  simp_all [mergeMaps, Std.HashMap.mem_filterMap]

/-- A key that's present in both maps being merged is mapped to the combination of its values. -/
theorem mergeMaps_some {k : α} {v₁ v₂ : β} :
    m₁[k]? = some v₁ → m₂[k]? = some v₂ → (mergeMaps f m₁ m₂)[k]? = f v₁ v₂ := by
  simp_all [mergeMaps]

end

/-- Refinement is preserved by joining the two flow models pointwise. -/
theorem FlowModelImpl.refines.join {fmI₁ fmI₂ : FlowModelImpl}
    {fm₁ fm₂ : FlowModel} (hrefines₁ : fmI₁.refines fm₁) (hrefines₂ : fmI₂.refines fm₂) :
    (fmI₁.join fmI₂).refines (fm₁.join fm₂) := by
  simp [FlowModelImpl.join, FlowModel.join]
  by_cases_iff hrefines₁.isEmpty <;> simp_all
  case neg hnonEmpty₁ hnonEmptyI₁ =>
    by_cases_iff hrefines₂.isEmpty <;> simp_all
    case pos => (conv => enter [2, 1, v]; tactic => split); simp_all
    case neg hnonEmpty₂ hnonEmptyI₂ =>
      constructor; intro v
      cases hrefines₁.promotionInfos v
      case absent hlookupI₁ hlookup₁ =>
        exact .absent (by simp_all [mergeMaps_none₁]) (by simp_all)
      case present pmI₁ pm₁ hlookupI₁ hlookup₁ hrefines_vm₁ =>
        cases hrefines₂.promotionInfos v
        case absent hlookupI₂ hlookup₂ =>
          exact .absent (by simp_all [mergeMaps_none₂]) (by simp_all)
        case present pmI₂ pm₂ hlookupI₂ hlookup₂ hrefines_vm₂ =>
          exact .present
            (by simp_all [mergeMaps_some])
            (by simp_all)
            (hrefines_vm₁.join hrefines_vm₂)

/--
`emI.refines fmI em` says that the algorithm's expression model `emI`, interpreted in the
algorithmic flow model `fmI` that the algorithm reached after analyzing the expression, faithfully
represents the specification's expression model `em`.

`fmI` is needed because the algorithm only records flow models for an expression when they differ
between the `true` and `false` cases, whereas the specification always records both.
-/
structure ExprModelImpl.refines (emI : ExprModelImpl)
    (fmI : FlowModelImpl) (em : ExprModel) :
    Prop where
  /-- The algorithm and the specification infer the same static type for the expression. -/
  types : emI.type = em.type
  /-- The algorithm and the specification identify the same promotion target, if any. -/
  ref?s : emI.ref? = em.ref?
  /-- The flow models that apply when the expression evaluates to `true` are related. -/
  fm_trues : (emI.boolInfo.getD (fmI, fmI)).fst.refines em.fm_true
  /-- The flow models that apply when the expression evaluates to `false` are related. -/
  fm_falses : (emI.boolInfo.getD (fmI, fmI)).snd.refines em.fm_false

/--
An algorithmic expression model that records no boolean information refines a specification
expression model whose `true` and `false` flow models are both the flow model the algorithm reached.
-/
theorem ExprModelImpl.refines.noBoolInfo {fmI fm} (hrefines : fmI.refines fm) T ref? :
    (⟨T, ref?, none⟩ : ExprModelImpl).refines fmI ⟨T, ref?, fm, fm⟩ := by
  constructor <;> simp_all

structure elabExprImpl.Correctness (e : Expr) : Prop where
  complete : ∀ {fm₀ m em} {fmI₀ : FlowModelImpl}, fmI₀.refines fm₀ →
    ElabExpr fm₀ e m em → ∃ fmI emI,
      elabExprImpl e cfg fmI₀ = Except.ok ((m, emI), fmI) ∧
      fmI.refines em.fm_after ∧ emI.refines fmI em
  sound : ∀ {fm₀ m emI fmI} {fmI₀ : FlowModelImpl}, fmI₀.refines fm₀ →
      elabExprImpl e cfg fmI₀ = Except.ok ((m, emI), fmI) → ∃ em,
      ElabExpr fm₀ e m em ∧ fmI.refines em.fm_after ∧ emI.refines fmI em

theorem elabExprImpl.correct.var (v : Variable) :
    elabExprImpl.Correctness (cfg := cfg) (.var v : Expr) := by
  constructor
  case complete =>
    intro fm₀ m em fmI₀ hrefines_fm₀ helab; simp [elabExprImpl]
    cases helab; case var pm T hlookup hcurrentType =>
      cases hrefines_fm₀.promotionInfos v <;> simp_all; subst_eqs
      case present pmI hlookupI hlookup hrefines_vm =>
        simp [hrefines_vm.currentTypes]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩; rotate_left 2
        · congr; rfl; rfl
        · assumption
        · constructor <;> simp <;> assumption
  case sound =>
    intro fm₀ m emI fmI fmI₀ hrefines_fm₀ hok; simp [elabExprImpl] at hok
    cases hrefines_fm₀.promotionInfos v <;> simp_all
    case present pmI pm hlookupI hlookup hrefines_vm =>
      simp_all [hrefines_vm.currentTypes]
      rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
      exists ⟨pm.currentType v.type, some (.var v), fm₀, fm₀⟩; simp_all
      constructor
      · exact ElabExpr.var hlookup rfl
      · exact ExprModelImpl.refines.noBoolInfo
          hrefines_fm₀ (pm.currentType v.type) (some (Reference.var v))

theorem elabExprImpl.correct.nullCheck (e₁ : Expr) (hcorrect₁ :
    elabExprImpl.Correctness (cfg := cfg) e₁) :
    elabExprImpl.Correctness (cfg := cfg) e₁.nullCheck := by
  constructor
  case complete =>
    intro fm₀ m em fmI₀ hrefines_fm₀ helab; simp [elabExprImpl]
    cases helab; case nullCheck m₁ em₁ fm htryPromote helab₁ =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩; simp_all
      obtain ⟨fmI₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain ⟨fmI, hok_tryPromote, hrefines_fmI⟩ :=
        hrefines_fm₁.tryPromote (cfg := cfg) ref?₁' (NonNull T₁'); simp_all
      refine ⟨?_, ?_, ?_, ?_, ?_⟩; rotate_left 2
      · congr; rfl; rfl
      · assumption
      · constructor <;> simp <;> assumption
  case sound =>
    intro fm₀ m emI fmI fmI₀ hrefines_fm₀ hok; simp [elabExprImpl] at hok
    cases hok₁ : elabExprImpl e₁ cfg fmI₀ <;> simp_all
    case ok result₁ =>
      rcases result₁ with ⟨⟨m₁, ⟨T₁, ref?₁, boolInfo₁⟩⟩, fmI₁⟩; simp_all
      rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨em₁, helab₁, hrefines_fm₁, hrefines_em₁⟩
      generalize hfm₁ : em₁.fm_after = fm₁; simp_all
      rcases em₁ with ⟨T₁', ref?₁', fm_true₁, fm_false₁⟩
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain ⟨fmI', hok_tryPromote, hrefines_fmI'⟩ :=
        hrefines_fm₁.tryPromote (cfg := cfg) ref?₁ (NonNull T₁); simp_all
      generalize hfm : (FlowModel.tryPromote ref?₁ (NonNull T₁) fm₁) = fm; simp_all
      generalize hem : (⟨NonNull T₁, none, fm, fm⟩ : ExprModel) = em
      injections; subst fmI m emI
      have hrefines_em := ExprModelImpl.refines.noBoolInfo hrefines_fmI' (NonNull T₁) none;
        rw [hem] at hrefines_em
      exists em
      refine ⟨?_, ?_, ?_⟩
      · subst hem; apply ElabExpr.nullCheck helab₁ (by simp_all)
      · subst hem; simp [ExprModel.fm_after]; assumption
      · assumption

theorem elabExprImpl.correct.asExpr (e₁ : Expr) T
    (hcorrect₁ : elabExprImpl.Correctness (cfg := cfg) e₁) :
    elabExprImpl.Correctness (cfg := cfg) (e₁.as T) := by
  constructor
  case complete =>
    intro fmI₀ fm₀ m em hrefines_fm₀ helab; simp [elabExprImpl]
    cases helab; case asExpr m₁ em₁ fm helab₁ htryPromote =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩; simp_all
      obtain ⟨fmI₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain ⟨fmI, hok_tryPromote, hrefines_fmI⟩ :=
        hrefines_fm₁.tryPromote (cfg := cfg) ref?₁' T; simp_all
      refine ⟨?_, ?_, ?_, ?_, ?_⟩; rotate_left 2
      · congr; rfl; rfl
      · assumption
      · constructor <;> simp <;> assumption
  case sound =>
    intro fm₀ m emI fmI fmI₀ hrefines_fm₀ hok; simp [elabExprImpl] at hok
    cases hok₁ : elabExprImpl e₁ cfg fmI₀ <;> simp_all
    case ok result₁ =>
      rcases result₁ with ⟨⟨m₁, ⟨T₁, ref?₁, boolInfo₁⟩⟩, fmI₁⟩; simp_all
      rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨em₁, helab₁, hrefines_fm₁, hrefines_em₁⟩
      generalize hfm₁ : em₁.fm_after = fm₁; simp_all
      rcases em₁ with ⟨T₁', ref?₁', fm_true₁, fm_false₁⟩
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain ⟨fmI', hok_tryPromote, hrefines_fmI'⟩ :=
        hrefines_fm₁.tryPromote (cfg := cfg) ref?₁ T; simp_all
      generalize hfm : (FlowModel.tryPromote ref?₁ T fm₁) = fm; simp_all
      generalize hem : (⟨T, none, fm, fm⟩ : ExprModel) = em
      injections; subst fmI' m emI
      have hrefines_em := ExprModelImpl.refines.noBoolInfo hrefines_fmI' T none;
        rw [hem] at hrefines_em
      exists em
      refine ⟨?_, ?_, ?_⟩
      · subst hem; apply ElabExpr.asExpr helab₁ (by simp_all)
      · subst hem; simp [ExprModel.fm_after]; assumption
      · assumption

theorem elabExprImpl.correct.nullLiteral :
    elabExprImpl.Correctness (cfg := cfg) (.null : Expr) := by
  constructor
  case complete =>
    intro fmI₀ fm₀ m em hrefines_fm₀ helab; simp [elabExprImpl]
    cases helab; simp; case nullLiteral =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩; rotate_left 2
      · congr; rfl; rfl
      · assumption
      · constructor <;> simp <;> assumption
  case sound =>
    intro fm₀ m emI fmI fmI₀ hrefines_fm₀ hok; simp [elabExprImpl] at hok
    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
    exists ⟨Γ.Null, none, fm₀, fm₀⟩; simp_all
    constructor
    · apply ElabExpr.nullLiteral
    · exact ExprModelImpl.refines.noBoolInfo hrefines_fm₀ Γ.Null none

theorem elabExprImpl.correct (e : Expr) :
    elabExprImpl.Correctness (cfg := cfg) e := by
  constructor
  case complete =>
    intro fmI₀ fm₀ m em hrefines_fm₀ helab
    cases h : e <;> rw [h] at helab
    case var v => apply (elabExprImpl.correct.var v).complete hrefines_fm₀ helab
    case nullCheck e₁ =>
      apply (elabExprImpl.correct.nullCheck e₁ (elabExprImpl.correct e₁)).complete hrefines_fm₀ helab
    case as e₁ T =>
      apply (elabExprImpl.correct.asExpr e₁ T (elabExprImpl.correct e₁)).complete hrefines_fm₀ helab
    case null => apply elabExprImpl.correct.nullLiteral.complete hrefines_fm₀ helab
  case sound =>
    intro fm₀ m emI fmI fmI₀ hrefines_fm₀ hok
    cases h : e <;> rw [h] at hok
    case var v => apply (elabExprImpl.correct.var v).sound hrefines_fm₀ hok
    case nullCheck e₁ =>
      apply (elabExprImpl.correct.nullCheck e₁ (elabExprImpl.correct e₁)).sound hrefines_fm₀ hok
    case as e₁ T =>
      apply (elabExprImpl.correct.asExpr e₁ T (elabExprImpl.correct e₁)).sound hrefines_fm₀ hok
    case null => apply elabExprImpl.correct.nullLiteral.sound hrefines_fm₀ hok

structure elabStmtImpl.Correctness (s : Stmt) : Prop where
  complete :
    ∀ {fm₀ m fm} {fmI₀ : FlowModelImpl}, fmI₀.refines fm₀ →
      ElabStmt fm₀ s m fm →
      ∃ fmI, elabStmtImpl s cfg fmI₀ = Except.ok (m, fmI) ∧ fmI.refines fm
  sound :
    ∀ {fm₀ m fmI} {fmI₀ : FlowModelImpl},
      fmI₀.refines fm₀ → elabStmtImpl s cfg fmI₀ = Except.ok (m, fmI) →
      ∃ fm, ElabStmt fm₀ s m fm ∧ fmI.refines fm

structure elabStmtsImpl.Correctness (ss : List Stmt) : Prop where
  complete :
    ∀ {fm₀ m fm} {fmI₀ : FlowModelImpl}, fmI₀.refines fm₀ →
      ElabStmts fm₀ ss m fm →
      ∃ fmI, elabStmtsImpl ss cfg fmI₀ = Except.ok (m, fmI) ∧ fmI.refines fm
  sound :
    ∀ {fm₀ m fmI} {fmI₀ : FlowModelImpl},
      fmI₀.refines fm₀ → elabStmtsImpl ss cfg fmI₀ = Except.ok (m, fmI) →
      ∃ fm, ElabStmts fm₀ ss m fm ∧ fmI.refines fm

theorem elabStmtImpl.correct.declare (n : String) (T : τ) :
    elabStmtImpl.Correctness (cfg := cfg) (.declare n T) := by
  constructor
  case complete =>
    intro fm₀ m fm fmI₀ hrefines_fm₀ helab; simp [elabStmtImpl]
    cases helab; case declare =>
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · apply hrefines_fm₀.insert ⟨n, T⟩ PromotionModelImpl.refines.declared
  case sound =>
    intro fm₀ m fmI fmI₀ hrefines_fm₀ hok; simp [elabStmtImpl] at hok
    rcases hok with ⟨rfl, rfl⟩
    exists fm₀.set ⟨n, T⟩ ⟨∅, ∅, true, false, some ⟨⟩⟩
    constructor
    · apply ElabStmt.declare fm₀ n T
    · apply hrefines_fm₀.insert ⟨n, T⟩ PromotionModelImpl.refines.declared

theorem elabStmtImpl.correct.exprStmt
    (e₁ : Expr) (hcorrect₁ : elabExprImpl.Correctness (cfg := cfg) e₁) :
    elabStmtImpl.Correctness (cfg := cfg) (.exprStmt e₁) := by
  constructor
  case complete =>
    intro fm₀ m fm fmI₀ hrefines_fm₀ helab; simp [elabStmtImpl]
    cases helab; case exprStmt em₁ helab₁ =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩
      obtain ⟨fmI₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · assumption
  case sound =>
    intro fm₀ m fmI fmI₀ hrefines_fm₀ hok; simp [elabStmtImpl] at hok
    cases hok₁ : elabExprImpl e₁ cfg fmI₀ <;> simp_all; case ok result₁ =>
    injections; subst m fmI
    rcases result₁ with ⟨⟨m₁, emI₁⟩, fmI₁⟩; simp_all
    rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨em₁, helab₁, hrefines_fm₁, hrefines_em₁⟩
    exists em₁.fm_after; simp_all
    exact ElabStmt.exprStmt helab₁

theorem elabStmtImpl.correct.ifStmt
    (e₁ : Expr) (s₂ s₃ : Stmt)
    (hcorrect₁ : elabExprImpl.Correctness (cfg := cfg) e₁)
    (hcorrect₂ : elabStmtImpl.Correctness (cfg := cfg) s₂)
    (hcorrect₃ : elabStmtImpl.Correctness (cfg := cfg) s₃) :
    elabStmtImpl.Correctness (cfg := cfg) (.ifStmt e₁ s₂ s₃) := by
  constructor
  case complete =>
    intro fm₀ m em fmI₀ hrefines_fm₀ helab; simp [elabStmtImpl]
    cases helab; case ifStmt m₁ em₁ m₂ fm₂ m₃ fm₃ his_bool helab₁ helab₂ helab₃ =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩; simp_all
      obtain ⟨fmI₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain hrefines_fm₁_true := hrefines_em₁.fm_trues; simp_all
      obtain ⟨fmI₂, hok₂, hrefines_fm₂⟩ := hcorrect₂.complete hrefines_fm₁_true helab₂;
        simp_all
      obtain hrefines_fm₁_false := hrefines_em₁.fm_falses; simp_all
      obtain ⟨fmI₃, hok₃, hrefines_fm₃⟩ := hcorrect₃.complete hrefines_fm₁_false helab₃; simp_all
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · exact FlowModelImpl.refines.join hrefines_fm₂ hrefines_fm₃
  case sound =>
    intro fm₀ m fmI fmI₀ hrefines_fm₀ hok; simp [elabStmtImpl] at hok
    cases hok₁ : elabExprImpl e₁ cfg fmI₀ <;> simp_all; case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emI₁⟩, fmI₁⟩; simp_all
    rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨em₁, helab₁, hrefines_fm₁, hrefines_em₁⟩
    rcases emI₁ with ⟨T₁, ref?₁, boolInfo₁⟩
    rcases hrefines_em₁.types with rfl; simp_all
    by_cases his_bool : em₁.type = Γ.bool <;>
      simp_all;
      case pos =>
    cases hok₂ : elabStmtImpl s₂ cfg (boolInfo₁.getD (fmI₁, fmI₁)).fst <;> simp_all;
      case ok result₂ =>
    rcases result₂ with ⟨m₂, fmI₂⟩; simp_all
    rcases hcorrect₂.sound hrefines_em₁.fm_trues hok₂ with ⟨fm₂, helab₂, hrefines_fm₂⟩
    cases hok₃ : elabStmtImpl s₃ cfg (boolInfo₁.getD (fmI₁, fmI₁)).snd <;> simp_all; case ok result₃ =>
    rcases result₃ with ⟨m₃, fmI₃⟩; simp_all
    rcases hcorrect₃.sound hrefines_em₁.fm_falses hok₃ with ⟨fm₃, helab₃, hrefines_fm₃⟩
    rcases hok with ⟨rfl, rfl⟩
    exists fm₂.join fm₃
    constructor
    · apply ElabStmt.ifStmt helab₁ his_bool helab₂ helab₃
    · exact FlowModelImpl.refines.join hrefines_fm₂ hrefines_fm₃

theorem elabStmtImpl.correct.block
    (ss₁ : List Stmt) (hcorrect₁ : elabStmtsImpl.Correctness (cfg := cfg) ss₁) :
    elabStmtImpl.Correctness (cfg := cfg) (.block ss₁) := by
  constructor
  case complete =>
    intro fm₀ m fm fmI₀ hrefines_fm₀ helab; simp [elabStmtImpl]
    cases helab; case block ms₁ helab₁ =>
    obtain ⟨fmI₁, hok₁, hrefines_fm₁⟩ := hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
    refine ⟨?_, ?_, ?_⟩; rotate_left
    · congr; rfl
    · assumption
  case sound =>
    intro fm₀ m fmI fmI₀ hrefines_fm₀ hok; simp [elabStmtImpl] at hok
    cases hok₁ : elabStmtsImpl ss₁ cfg fmI₀ <;> simp_all; case ok result₁ =>
    rcases result₁ with ⟨m₁, fmI₂⟩; simp_all
    rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨fm₁, helab₁, hrefines_fm₁⟩
    rcases hok with ⟨rfl, rfl⟩
    exists fm₁; simp_all
    exact ElabStmt.block helab₁

theorem elabStmtsImpl.correct.nil : elabStmtsImpl.Correctness (cfg := cfg) ([] : List Stmt) := by
  constructor
  case complete =>
    intro fm₀ m fm fmI₀ hrefines_fm₀ helab; simp [elabStmtsImpl]
    cases helab; case nil =>
      exists fmI₀
  case sound =>
    intro fm₀ m fmI fmI₀ hrefines_fm₀ hok; simp [elabStmtsImpl] at hok
    rcases hok with ⟨rfl, rfl⟩
    exists fm₀; simp_all
    exact ElabStmts.nil

theorem elabStmtsImpl.correct.cons
    (s₁ : Stmt) (ss₂ : List Stmt)
    (hcorrect₁ : elabStmtImpl.Correctness (cfg := cfg) s₁)
    (hcorrect₂ : elabStmtsImpl.Correctness (cfg := cfg) ss₂) :
    elabStmtsImpl.Correctness (cfg := cfg) (s₁ :: ss₂) := by
  constructor
  case complete =>
    intro fm₀ m fm fmI₀ hrefines_fm₀ helab; simp [elabStmtsImpl]
    cases helab; case cons fm₁ m₁ ms₂ helab₁ helab₂ =>
      obtain ⟨fmI₁, hok₁, hrefines_fm₁⟩ := hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      obtain ⟨fmI₂, hok₂, hrefines_fm₂⟩ := hcorrect₂.complete hrefines_fm₁ helab₂; simp_all
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · assumption
  case sound =>
    intro fm₀ m fmI fmI₀ hrefines_fm₀ hok; simp [elabStmtsImpl] at hok
    cases hok₁ : elabStmtImpl s₁ cfg fmI₀ <;> simp_all; case ok result₁ =>
    rcases result₁ with ⟨m₁, fmI₁⟩; simp_all
    rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨fm₁, helab₁, hrefines_fm₁⟩
    cases hok₂ : elabStmtsImpl ss₂ cfg fmI₁ <;> simp_all; case ok result₂ =>
    rcases result₂ with ⟨m₂, fmI₂⟩; simp_all
    rcases hcorrect₂.sound hrefines_fm₁ hok₂ with ⟨fm₂, helab₂, hrefines_fm₂⟩
    rcases hok with ⟨rfl, rfl⟩
    exists fm₂; simp_all
    apply ElabStmts.cons helab₁ helab₂

mutual
theorem elabStmtImpl.correct (s : Stmt) :
    elabStmtImpl.Correctness (cfg := cfg) s := by
  constructor
  case complete =>
    intro fm₀ m fm fmI₀ hrefines_fm₀ helab
    cases h : s <;> rw [h] at helab
    case declare n T => apply (elabStmtImpl.correct.declare n T).complete hrefines_fm₀ helab
    case exprStmt e₁ =>
      apply (elabStmtImpl.correct.exprStmt e₁ (elabExprImpl.correct e₁)).complete hrefines_fm₀ helab
    case ifStmt e₁ s₂ s₃ =>
      apply
        (elabStmtImpl.correct.ifStmt
            e₁ s₂ s₃ (elabExprImpl.correct e₁) (elabStmtImpl.correct s₂) (elabStmtImpl.correct s₃)).complete
          hrefines_fm₀ helab
    case block ss =>
      apply (elabStmtImpl.correct.block ss (elabStmtsImpl.correct ss)).complete hrefines_fm₀ helab
  case sound =>
    intro fm₀ m fmI fmI₀ hrefines_fm₀ hok
    cases h : s <;> rw [h] at hok
    case declare n T => apply (elabStmtImpl.correct.declare n T).sound hrefines_fm₀ hok
    case exprStmt e₁ =>
      apply (elabStmtImpl.correct.exprStmt e₁ (elabExprImpl.correct e₁)).sound hrefines_fm₀ hok
    case ifStmt e₁ s₂ s₃ =>
      apply
        (elabStmtImpl.correct.ifStmt
            e₁ s₂ s₃ (elabExprImpl.correct e₁) (elabStmtImpl.correct s₂) (elabStmtImpl.correct s₃)).sound
          hrefines_fm₀ hok
    case block ss =>
      apply (elabStmtImpl.correct.block ss (elabStmtsImpl.correct ss)).sound hrefines_fm₀ hok

theorem elabStmtsImpl.correct (ss : List Stmt) :
    elabStmtsImpl.Correctness (cfg := cfg) ss := by
  constructor
  case complete =>
    intro fm₀ m fm fmI₀ hrefines_fm₀ helab
    cases h : ss <;> rw [h] at helab
    case nil => apply elabStmtsImpl.correct.nil.complete hrefines_fm₀ helab
    case cons s ss =>
      apply (elabStmtsImpl.correct.cons s ss (elabStmtImpl.correct s) (elabStmtsImpl.correct ss)).complete
        hrefines_fm₀ helab
  case sound =>
    intro fm₀ m fmI fmI₀ hrefines_fm₀ hok
    cases h : ss <;> rw [h] at hok
    case nil => apply elabStmtsImpl.correct.nil.sound hrefines_fm₀ hok
    case cons s ss =>
      apply (elabStmtsImpl.correct.cons s ss (elabStmtImpl.correct s) (elabStmtsImpl.correct ss)).sound
        hrefines_fm₀ hok
end

end FlowAnalysis
