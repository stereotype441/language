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
local notation "ExprModelA" => ExprModelA (τ := τ)
local notation "FlowModel" => FlowModel (τ := τ)
local notation "FlowModelA" => FlowModelA (τ := τ)
local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "Stmt" => Stmt (τ := τ)
local notation "VariableModel" => VariableModel (τ := τ)
local notation "VariableModelImpl" => VariableModelImpl (τ := τ)

@[simp]
theorem AlgM_get_eq {fm} :
  (get : AlgM _) cfg fm = Except.ok (fm, fm) := rfl

@[simp]
theorem AlgM_pure_eq {α fm} {a : α} :
  (pure a : AlgM _) cfg fm = Except.ok (a, fm) := rfl

@[simp]
theorem AlgM_bind_eq {α β : Type} {x : AlgM α} {fm : FlowModelA}
    {f : α → AlgM β} :
  (x >>= f) cfg fm = match x cfg fm with
                 | Except.ok (a, hm') => f a cfg hm'
                 | Except.error e => Except.error e := by
  simp [bind, ReaderT.bind, StateT.bind]
  cases x cfg fm <;> rfl

@[simp]
theorem AlgM_map_eq {α β : Type} {fm : FlowModelA} {f : α → β} {x : AlgM α} :
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
theorem AlgM_throw_eq_ok_contra {α e fmA₀ x fmA} :
    (throw e : AlgM α) cfg fmA₀ = Except.ok (x, fmA) ↔ False := by
  constructor
  case mp => intro h; contradiction
  case mpr => intro h; exfalso; assumption

/--
`fmA.EnvRefinesAt fm v` says that the `env` fields of the algorithm's flow model `fmA` and the
specification's flow model `fm` agree about the variable `v`: either neither flow model has an entry
for `v`, or both do, and the algorithm's variable model refines the specification's.
-/
inductive FlowModelA.EnvRefinesAt (fmA : FlowModelA)
    (fm : FlowModel) (v : Variable) : Prop where
  /-- `v` is absent from both flow models. -/
  | absent (hlookupA : fmA.env[v]? = none) (hlookup : fm.env v = none)
  /-- `v` is present in both flow models, and their variable models are related by `refines`. -/
  | present
        {vmI : VariableModelImpl} {vm : VariableModel} (hlookupA : fmA.env[v]? = some vmI)
        (hlookup : fm.env v = some vm) (hrefines_vm : vmI.refines vm)

/--
`fmA.refines fm` says that the algorithm's flow model `fmA` faithfully represents the
specification's flow model `fm`.
-/
structure FlowModelA.refines (fmA : FlowModelA)
    (fm : FlowModel) : Prop where
  /-- The two flow models' `env` fields agree about every variable. -/
  envs (v : Variable) : fmA.EnvRefinesAt fm v

/-- The algorithm's initial flow model refines the specification's initial flow model. -/
theorem FlowModelA.refines.empty :
    (.empty : FlowModelA).refines FlowModel.empty := by
  constructor; intro v
  exact .absent (by simp [FlowModelA.empty]) (by simp [FlowModel.empty])

/--
A flow model refined by `fmA` maps every variable to `none` precisely when `fmA`'s `env` is empty.
-/
theorem FlowModelA.refines.isEmpty {fmA : FlowModelA} {fm : FlowModel}
    (hrefines : fmA.refines fm) :
    fmA.env.isEmpty ↔ ∀ v, fm.env v = none := by
  constructor
  case mp =>
    intro hemptyA v
    have : fmA.env[v]? = none := by exact Std.HashMap.getElem?_of_isEmpty hemptyA
    cases hrefines.envs v <;> simp_all
  case mpr =>
    intro hempty
    rw [Std.HashMap.isEmpty_iff_forall_not_mem]
    intro v
    cases hrefines.envs v <;> simp_all

/--
An algorithmic flow model whose `env` is empty refines the specification's empty flow model.

The conclusion is spelled out as `⟨fun _ => none⟩` rather than `FlowModel.empty` because `simp`
matches conclusions syntactically; stating it in terms of `FlowModel.empty` would stop this lemma
from firing on the goals that arise in `FlowModelA.refines.join`.
-/
@[simp]
theorem FlowModelA.refines.empty_of_isEmpty {fmA : FlowModelA}
    (hempty : fmA.env.isEmpty) : fmA.refines ⟨fun _ => none⟩ := by
  constructor; intro v
  exact .absent (Std.HashMap.getElem?_of_isEmpty hempty) (by simp)

/--
A single algorithmic flow model can't refine two different specification flow models, since it
determines each variable's variable model up to `VariableModelImpl.refines`, which is itself unique.
-/
theorem FlowModelA.refines.unique {fmA : FlowModelA} {fm₁ fm₂ : FlowModel}
    (hrefines₁ : fmA.refines fm₁) (hrefines₂ : fmA.refines fm₂) : fm₁ = fm₂ := by
  apply FlowModel.extensionality; intro v
  cases hrefines₁.envs v
  case absent hlookupA₁ hlookup₁ => cases hrefines₂.envs v <;> simp_all
  case present vmI₁ vm₁ hlookupA₁ hlookup₁ hrefines_vm₁ =>
    cases hrefines₂.envs v
    case absent hlookupA₂ hlookup₂ => simp_all
    case present vmI₂ vm₂ hlookupA₂ hlookup₂ hrefines_vm₂ =>
      -- `fmA` has a single entry for `v`, so `vm₁` and `vm₂` refine the same `VariableModelImpl`,
      -- and `VariableModelImpl.refines` determines the variable model it refines uniquely.
      have hvmIs : vmI₁ = vmI₂ := by simp_all
      subst hvmIs
      rw [hlookup₁, hlookup₂, hrefines_vm₁.unique hrefines_vm₂]

/--
Refinement is preserved by adding a variable to both flow models, provided the variable models
being added are themselves related by `refines`.
-/
@[simp]
theorem FlowModelA.refines.insert {fmA : FlowModelA} {fm : FlowModel}
    {vmI : VariableModelImpl} {vm : VariableModel} (v : Variable)
    (hrefines_fm : fmA.refines fm) (hrefines_vm : vmI.refines vm) :
    (FlowModelA.mk (fmA.env.insert v vmI)).refines (fm.set v vm) := by
  constructor; intro v'
  by_cases heq : v = v' <;> subst_eqs
  case pos =>
    exact .present (by simp) (by simp) hrefines_vm
  case neg =>
    cases hrefines_fm.envs v'
    case absent hlookupA hlookup =>
      exact .absent (by simp_all) (by simp_all)
    case present vmI' vm' hlookupA hlookup hrefines_vm' =>
      exact .present (by simp_all [Std.HashMap.getElem?_insert]) (by simp_all) hrefines_vm'

/--
Running the algorithm's `tryPromoteA` on a flow model that refines `fm` succeeds, and produces a
flow model that refines the result of the specification's `FlowModel.tryPromote`.
-/
theorem FlowModelA.refines.tryPromote
    {fmA : FlowModelA} {fm : FlowModel} (hrefines : fmA.refines fm) ref? T :
    ∃ fmA', tryPromoteA ref? T cfg fmA = Except.ok ((), fmA') ∧
    fmA'.refines (fm.tryPromote ref? T) := by
  simp [tryPromoteA, FlowModel.tryPromote]
  cases ref? <;> simp_all
  case none => exists fmA
  case some ref =>
    cases ref; simp_all
    case var v =>
      cases hrefines.envs v <;> simp_all
      case absent => exists fmA
      case present vmI vm hlookupA hlookup hrefines_vm =>
        rw [hrefines_vm.currentTypes]
        by_cases hT_lt_current : T < vm.currentType v.type <;> simp_all
        case neg => exists fmA
        case pos =>
          -- Unlike `FlowModel.tryPromote`, which promotes using `PromotionChain.tryPromote`, the
          -- algorithm checks explicitly whether appending `T` produces a valid promotion chain, and
          -- leaves `env` untouched if it doesn't. So we need to consider the two cases separately.
          by_cases hchain : isPromotionChain (vmI.promotedTypes ++ [T]) <;> simp_all
          case pos =>
            -- `T` was appended to `v`'s promotion chain, in both the algorithm and the spec.
            exists ⟨fmA.env.insert v {vmI with promotedTypes := vmI.promotedTypes ++ [T]}⟩
            refine ⟨rfl, ?_⟩
            exact hrefines.insert v (hrefines_vm.promote hchain)
          case neg =>
            -- Neither the algorithm nor the spec promoted `v`, so neither one changed its state;
            -- for the spec, this is because `PromotionChain.tryPromote` was a no-op, so the `set`
            -- assigned `v` the variable model it already had.
            exists fmA
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
theorem FlowModelA.refines.join {fmA₁ fmA₂ : FlowModelA}
    {fm₁ fm₂ : FlowModel} (hrefines₁ : fmA₁.refines fm₁) (hrefines₂ : fmA₂.refines fm₂) :
    (fmA₁.join fmA₂).refines (fm₁.join fm₂) := by
  simp [FlowModelA.join, FlowModel.join]
  by_cases_iff hrefines₁.isEmpty <;> simp_all
  case neg hnonEmpty₁ hnonEmptyA₁ =>
    by_cases_iff hrefines₂.isEmpty <;> simp_all
    case pos => (conv => enter [2, 1, v]; tactic => split); simp_all
    case neg hnonEmpty₂ hnonEmptyA₂ =>
      constructor; intro v
      cases hrefines₁.envs v
      case absent hlookupA₁ hlookup₁ =>
        exact .absent (by simp_all [mergeMaps_none₁]) (by simp_all)
      case present vmI₁ vm₁ hlookupA₁ hlookup₁ hrefines_vm₁ =>
        cases hrefines₂.envs v
        case absent hlookupA₂ hlookup₂ =>
          exact .absent (by simp_all [mergeMaps_none₂]) (by simp_all)
        case present vmI₂ vm₂ hlookupA₂ hlookup₂ hrefines_vm₂ =>
          exact .present
            (by simp_all [mergeMaps_some])
            (by simp_all)
            (hrefines_vm₁.join hrefines_vm₂)

/--
`emA.refines fmA em` says that the algorithm's expression model `emA`, interpreted in the
algorithmic flow model `fmA` that the algorithm reached after analyzing the expression, faithfully
represents the specification's expression model `em`.

`fmA` is needed because the algorithm only records flow models for an expression when they differ
between the `true` and `false` cases, whereas the specification always records both.
-/
structure ExprModelA.refines (emA : ExprModelA)
    (fmA : FlowModelA) (em : ExprModel) :
    Prop where
  /-- The algorithm and the specification infer the same static type for the expression. -/
  types : emA.type = em.type
  /-- The algorithm and the specification identify the same promotion target, if any. -/
  ref?s : emA.ref? = em.ref?
  /-- The flow models that apply when the expression evaluates to `true` are related. -/
  fm_trues : (emA.boolInfo.getD (fmA, fmA)).fst.refines em.fm_true
  /-- The flow models that apply when the expression evaluates to `false` are related. -/
  fm_falses : (emA.boolInfo.getD (fmA, fmA)).snd.refines em.fm_false

/--
An algorithmic expression model that records no boolean information refines a specification
expression model whose `true` and `false` flow models are both the flow model the algorithm reached.
-/
theorem ExprModelA.refines.noBoolInfo {fmA fm} (hrefines : fmA.refines fm) T ref? :
    (⟨T, ref?, none⟩ : ExprModelA).refines fmA ⟨T, ref?, fm, fm⟩ := by
  constructor <;> simp_all

structure elabExprA.Correctness (e : Expr) : Prop where
  complete : ∀ {fm₀ m em} {fmA₀ : FlowModelA}, fmA₀.refines fm₀ →
    ElabExpr fm₀ e m em → ∃ fmA emA,
      elabExprA e cfg fmA₀ = Except.ok ((m, emA), fmA) ∧
      fmA.refines em.fm_after ∧ emA.refines fmA em
  sound : ∀ {fm₀ m emA fmA} {fmA₀ : FlowModelA}, fmA₀.refines fm₀ →
      elabExprA e cfg fmA₀ = Except.ok ((m, emA), fmA) → ∃ em,
      ElabExpr fm₀ e m em ∧ fmA.refines em.fm_after ∧ emA.refines fmA em

theorem elabExprA.correct.var (v : Variable) :
    elabExprA.Correctness (cfg := cfg) (.var v : Expr) := by
  constructor
  case complete =>
    intro fm₀ m em fmA₀ hrefines_fm₀ helab; simp [elabExprA]
    cases helab; case var vm T hlookup hcurrentType =>
      cases hrefines_fm₀.envs v <;> simp_all; subst_eqs
      case present vmI hlookupA hlookup hrefines_vm =>
        simp [hrefines_vm.currentTypes]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩; rotate_left 2
        · congr; rfl; rfl
        · assumption
        · constructor <;> simp <;> assumption
  case sound =>
    intro fm₀ m emA fmA fmA₀ hrefines_fm₀ hok; simp [elabExprA] at hok
    cases hrefines_fm₀.envs v <;> simp_all
    case present vmI vm hlookupA hlookup hrefines_vm =>
      simp_all [hrefines_vm.currentTypes]
      rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
      exists ⟨vm.currentType v.type, some (.var v), fm₀, fm₀⟩; simp_all
      constructor
      · exact ElabExpr.var hlookup rfl
      · exact ExprModelA.refines.noBoolInfo
          hrefines_fm₀ (vm.currentType v.type) (some (Reference.var v))

theorem elabExprA.correct.nullCheck (e₁ : Expr) (hcorrect₁ :
    elabExprA.Correctness (cfg := cfg) e₁) :
    elabExprA.Correctness (cfg := cfg) e₁.nullCheck := by
  constructor
  case complete =>
    intro fm₀ m em fmA₀ hrefines_fm₀ helab; simp [elabExprA]
    cases helab; case nullCheck m₁ em₁ fm htryPromote helab₁ =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩; simp_all
      obtain ⟨fmA₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain ⟨fmA, hok_tryPromote, hrefines_fmA⟩ :=
        hrefines_fm₁.tryPromote (cfg := cfg) ref?₁' (NonNull T₁'); simp_all
      refine ⟨?_, ?_, ?_, ?_, ?_⟩; rotate_left 2
      · congr; rfl; rfl
      · assumption
      · constructor <;> simp <;> assumption
  case sound =>
    intro fm₀ m emA fmA fmA₀ hrefines_fm₀ hok; simp [elabExprA] at hok
    cases hok₁ : elabExprA e₁ cfg fmA₀ <;> simp_all
    case ok result₁ =>
      rcases result₁ with ⟨⟨m₁, ⟨T₁, ref?₁, boolInfo₁⟩⟩, fmA₁⟩; simp_all
      rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨em₁, helab₁, hrefines_fm₁, hrefines_em₁⟩
      generalize hfm₁ : em₁.fm_after = fm₁; simp_all
      rcases em₁ with ⟨T₁', ref?₁', fm_true₁, fm_false₁⟩
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain ⟨fmA', hok_tryPromote, hrefines_fmA'⟩ :=
        hrefines_fm₁.tryPromote (cfg := cfg) ref?₁ (NonNull T₁); simp_all
      generalize hfm : (FlowModel.tryPromote ref?₁ (NonNull T₁) fm₁) = fm; simp_all
      generalize hem : (⟨NonNull T₁, none, fm, fm⟩ : ExprModel) = em
      injections; subst fmA m emA
      have hrefines_em := ExprModelA.refines.noBoolInfo hrefines_fmA' (NonNull T₁) none;
        rw [hem] at hrefines_em
      exists em
      refine ⟨?_, ?_, ?_⟩
      · subst hem; apply ElabExpr.nullCheck helab₁ (by simp_all)
      · subst hem; simp [ExprModel.fm_after]; assumption
      · assumption

theorem elabExprA.correct.asExpr (e₁ : Expr) T
    (hcorrect₁ : elabExprA.Correctness (cfg := cfg) e₁) :
    elabExprA.Correctness (cfg := cfg) (e₁.as T) := by
  constructor
  case complete =>
    intro fmA₀ fm₀ m em hrefines_fm₀ helab; simp [elabExprA]
    cases helab; case asExpr m₁ em₁ fm helab₁ htryPromote =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩; simp_all
      obtain ⟨fmA₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain ⟨fmA, hok_tryPromote, hrefines_fmA⟩ :=
        hrefines_fm₁.tryPromote (cfg := cfg) ref?₁' T; simp_all
      refine ⟨?_, ?_, ?_, ?_, ?_⟩; rotate_left 2
      · congr; rfl; rfl
      · assumption
      · constructor <;> simp <;> assumption
  case sound =>
    intro fm₀ m emA fmA fmA₀ hrefines_fm₀ hok; simp [elabExprA] at hok
    cases hok₁ : elabExprA e₁ cfg fmA₀ <;> simp_all
    case ok result₁ =>
      rcases result₁ with ⟨⟨m₁, ⟨T₁, ref?₁, boolInfo₁⟩⟩, fmA₁⟩; simp_all
      rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨em₁, helab₁, hrefines_fm₁, hrefines_em₁⟩
      generalize hfm₁ : em₁.fm_after = fm₁; simp_all
      rcases em₁ with ⟨T₁', ref?₁', fm_true₁, fm_false₁⟩
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain ⟨fmA', hok_tryPromote, hrefines_fmA'⟩ :=
        hrefines_fm₁.tryPromote (cfg := cfg) ref?₁ T; simp_all
      generalize hfm : (FlowModel.tryPromote ref?₁ T fm₁) = fm; simp_all
      generalize hem : (⟨T, none, fm, fm⟩ : ExprModel) = em
      injections; subst fmA' m emA
      have hrefines_em := ExprModelA.refines.noBoolInfo hrefines_fmA' T none;
        rw [hem] at hrefines_em
      exists em
      refine ⟨?_, ?_, ?_⟩
      · subst hem; apply ElabExpr.asExpr helab₁ (by simp_all)
      · subst hem; simp [ExprModel.fm_after]; assumption
      · assumption

theorem elabExprA.correct.nullLiteral :
    elabExprA.Correctness (cfg := cfg) (.null : Expr) := by
  constructor
  case complete =>
    intro fmA₀ fm₀ m em hrefines_fm₀ helab; simp [elabExprA]
    cases helab; simp; case nullLiteral =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩; rotate_left 2
      · congr; rfl; rfl
      · assumption
      · constructor <;> simp <;> assumption
  case sound =>
    intro fm₀ m emA fmA fmA₀ hrefines_fm₀ hok; simp [elabExprA] at hok
    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
    exists ⟨Γ.Null, none, fm₀, fm₀⟩; simp_all
    constructor
    · apply ElabExpr.nullLiteral
    · exact ExprModelA.refines.noBoolInfo hrefines_fm₀ Γ.Null none

theorem elabExprA.correct (e : Expr) :
    elabExprA.Correctness (cfg := cfg) e := by
  constructor
  case complete =>
    intro fmA₀ fm₀ m em hrefines_fm₀ helab
    cases h : e <;> rw [h] at helab
    case var v => apply (elabExprA.correct.var v).complete hrefines_fm₀ helab
    case nullCheck e₁ =>
      apply (elabExprA.correct.nullCheck e₁ (elabExprA.correct e₁)).complete hrefines_fm₀ helab
    case as e₁ T =>
      apply (elabExprA.correct.asExpr e₁ T (elabExprA.correct e₁)).complete hrefines_fm₀ helab
    case null => apply elabExprA.correct.nullLiteral.complete hrefines_fm₀ helab
  case sound =>
    intro fm₀ m emA fmA fmA₀ hrefines_fm₀ hok
    cases h : e <;> rw [h] at hok
    case var v => apply (elabExprA.correct.var v).sound hrefines_fm₀ hok
    case nullCheck e₁ =>
      apply (elabExprA.correct.nullCheck e₁ (elabExprA.correct e₁)).sound hrefines_fm₀ hok
    case as e₁ T =>
      apply (elabExprA.correct.asExpr e₁ T (elabExprA.correct e₁)).sound hrefines_fm₀ hok
    case null => apply elabExprA.correct.nullLiteral.sound hrefines_fm₀ hok

structure elabStmtA.Correctness (s : Stmt) : Prop where
  complete :
    ∀ {fm₀ m fm} {fmA₀ : FlowModelA}, fmA₀.refines fm₀ →
      ElabStmt fm₀ s m fm →
      ∃ fmA, elabStmtA s cfg fmA₀ = Except.ok (m, fmA) ∧ fmA.refines fm
  sound :
    ∀ {fm₀ m fmA} {fmA₀ : FlowModelA},
      fmA₀.refines fm₀ → elabStmtA s cfg fmA₀ = Except.ok (m, fmA) →
      ∃ fm, ElabStmt fm₀ s m fm ∧ fmA.refines fm

structure elabStmtsA.Correctness (ss : List Stmt) : Prop where
  complete :
    ∀ {fm₀ m fm} {fmA₀ : FlowModelA}, fmA₀.refines fm₀ →
      ElabStmts fm₀ ss m fm →
      ∃ fmA, elabStmtsA ss cfg fmA₀ = Except.ok (m, fmA) ∧ fmA.refines fm
  sound :
    ∀ {fm₀ m fmA} {fmA₀ : FlowModelA},
      fmA₀.refines fm₀ → elabStmtsA ss cfg fmA₀ = Except.ok (m, fmA) →
      ∃ fm, ElabStmts fm₀ ss m fm ∧ fmA.refines fm

theorem elabStmtA.correct.declare (n : String) (T : τ) :
    elabStmtA.Correctness (cfg := cfg) (.declare n T) := by
  constructor
  case complete =>
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab; simp [elabStmtA]
    cases helab; case declare =>
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · apply hrefines_fm₀.insert ⟨n, T⟩ VariableModelImpl.refines.declared
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtA] at hok
    rcases hok with ⟨rfl, rfl⟩
    exists fm₀.set ⟨n, T⟩ ⟨∅, ∅, true, false, some ⟨⟩⟩
    constructor
    · apply ElabStmt.declare fm₀ n T
    · apply hrefines_fm₀.insert ⟨n, T⟩ VariableModelImpl.refines.declared

theorem elabStmtA.correct.exprStmt
    (e₁ : Expr) (hcorrect₁ : elabExprA.Correctness (cfg := cfg) e₁) :
    elabStmtA.Correctness (cfg := cfg) (.exprStmt e₁) := by
  constructor
  case complete =>
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab; simp [elabStmtA]
    cases helab; case exprStmt em₁ helab₁ =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩
      obtain ⟨fmA₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · assumption
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtA] at hok
    cases hok₁ : elabExprA e₁ cfg fmA₀ <;> simp_all; case ok result₁ =>
    injections; subst m fmA
    rcases result₁ with ⟨⟨m₁, emA₁⟩, fmA₁⟩; simp_all
    rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨em₁, helab₁, hrefines_fm₁, hrefines_em₁⟩
    exists em₁.fm_after; simp_all
    exact ElabStmt.exprStmt helab₁

theorem elabStmtA.correct.ifStmt
    (e₁ : Expr) (s₂ s₃ : Stmt)
    (hcorrect₁ : elabExprA.Correctness (cfg := cfg) e₁)
    (hcorrect₂ : elabStmtA.Correctness (cfg := cfg) s₂)
    (hcorrect₃ : elabStmtA.Correctness (cfg := cfg) s₃) :
    elabStmtA.Correctness (cfg := cfg) (.ifStmt e₁ s₂ s₃) := by
  constructor
  case complete =>
    intro fm₀ m em fmA₀ hrefines_fm₀ helab; simp [elabStmtA]
    cases helab; case ifStmt m₁ em₁ m₂ fm₂ m₃ fm₃ his_bool helab₁ helab₂ helab₃ =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩; simp_all
      obtain ⟨fmA₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁
      rcases hrefines_em₁.types with rfl; simp_all
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain hrefines_fm₁_true := hrefines_em₁.fm_trues; simp_all
      obtain ⟨fmA₂, hok₂, hrefines_fm₂⟩ := hcorrect₂.complete hrefines_fm₁_true helab₂;
        simp_all
      obtain hrefines_fm₁_false := hrefines_em₁.fm_falses; simp_all
      obtain ⟨fmA₃, hok₃, hrefines_fm₃⟩ := hcorrect₃.complete hrefines_fm₁_false helab₃; simp_all
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · exact FlowModelA.refines.join hrefines_fm₂ hrefines_fm₃
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtA] at hok
    cases hok₁ : elabExprA e₁ cfg fmA₀ <;> simp_all; case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emA₁⟩, fmA₁⟩; simp_all
    rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨em₁, helab₁, hrefines_fm₁, hrefines_em₁⟩
    rcases emA₁ with ⟨T₁, ref?₁, boolInfo₁⟩
    rcases hrefines_em₁.types with rfl; simp_all
    by_cases his_bool : em₁.type = Γ.bool <;>
      simp_all;
      case pos =>
    cases hok₂ : elabStmtA s₂ cfg (boolInfo₁.getD (fmA₁, fmA₁)).fst <;> simp_all;
      case ok result₂ =>
    rcases result₂ with ⟨m₂, fmA₂⟩; simp_all
    rcases hcorrect₂.sound hrefines_em₁.fm_trues hok₂ with ⟨fm₂, helab₂, hrefines_fm₂⟩
    cases hok₃ : elabStmtA s₃ cfg (boolInfo₁.getD (fmA₁, fmA₁)).snd <;> simp_all; case ok result₃ =>
    rcases result₃ with ⟨m₃, fmA₃⟩; simp_all
    rcases hcorrect₃.sound hrefines_em₁.fm_falses hok₃ with ⟨fm₃, helab₃, hrefines_fm₃⟩
    rcases hok with ⟨rfl, rfl⟩
    exists fm₂.join fm₃
    constructor
    · apply ElabStmt.ifStmt helab₁ his_bool helab₂ helab₃
    · exact FlowModelA.refines.join hrefines_fm₂ hrefines_fm₃

theorem elabStmtA.correct.block
    (ss₁ : List Stmt) (hcorrect₁ : elabStmtsA.Correctness (cfg := cfg) ss₁) :
    elabStmtA.Correctness (cfg := cfg) (.block ss₁) := by
  constructor
  case complete =>
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab; simp [elabStmtA]
    cases helab; case block ms₁ helab₁ =>
    obtain ⟨fmA₁, hok₁, hrefines_fm₁⟩ := hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
    refine ⟨?_, ?_, ?_⟩; rotate_left
    · congr; rfl
    · assumption
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtA] at hok
    cases hok₁ : elabStmtsA ss₁ cfg fmA₀ <;> simp_all; case ok result₁ =>
    rcases result₁ with ⟨m₁, fmA₂⟩; simp_all
    rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨fm₁, helab₁, hrefines_fm₁⟩
    rcases hok with ⟨rfl, rfl⟩
    exists fm₁; simp_all
    exact ElabStmt.block helab₁

theorem elabStmtsA.correct.nil : elabStmtsA.Correctness (cfg := cfg) ([] : List Stmt) := by
  constructor
  case complete =>
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab; simp [elabStmtsA]
    cases helab; case nil =>
      exists fmA₀
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtsA] at hok
    rcases hok with ⟨rfl, rfl⟩
    exists fm₀; simp_all
    exact ElabStmts.nil

theorem elabStmtsA.correct.cons
    (s₁ : Stmt) (ss₂ : List Stmt)
    (hcorrect₁ : elabStmtA.Correctness (cfg := cfg) s₁)
    (hcorrect₂ : elabStmtsA.Correctness (cfg := cfg) ss₂) :
    elabStmtsA.Correctness (cfg := cfg) (s₁ :: ss₂) := by
  constructor
  case complete =>
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab; simp [elabStmtsA]
    cases helab; case cons fm₁ m₁ ms₂ helab₁ helab₂ =>
      obtain ⟨fmA₁, hok₁, hrefines_fm₁⟩ := hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      obtain ⟨fmA₂, hok₂, hrefines_fm₂⟩ := hcorrect₂.complete hrefines_fm₁ helab₂; simp_all
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · assumption
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtsA] at hok
    cases hok₁ : elabStmtA s₁ cfg fmA₀ <;> simp_all; case ok result₁ =>
    rcases result₁ with ⟨m₁, fmA₁⟩; simp_all
    rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨fm₁, helab₁, hrefines_fm₁⟩
    cases hok₂ : elabStmtsA ss₂ cfg fmA₁ <;> simp_all; case ok result₂ =>
    rcases result₂ with ⟨m₂, fmA₂⟩; simp_all
    rcases hcorrect₂.sound hrefines_fm₁ hok₂ with ⟨fm₂, helab₂, hrefines_fm₂⟩
    rcases hok with ⟨rfl, rfl⟩
    exists fm₂; simp_all
    apply ElabStmts.cons helab₁ helab₂

mutual
theorem elabStmtA.correct (s : Stmt) :
    elabStmtA.Correctness (cfg := cfg) s := by
  constructor
  case complete =>
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab
    cases h : s <;> rw [h] at helab
    case declare n T => apply (elabStmtA.correct.declare n T).complete hrefines_fm₀ helab
    case exprStmt e₁ =>
      apply (elabStmtA.correct.exprStmt e₁ (elabExprA.correct e₁)).complete hrefines_fm₀ helab
    case ifStmt e₁ s₂ s₃ =>
      apply
        (elabStmtA.correct.ifStmt
            e₁ s₂ s₃ (elabExprA.correct e₁) (elabStmtA.correct s₂) (elabStmtA.correct s₃)).complete
          hrefines_fm₀ helab
    case block ss =>
      apply (elabStmtA.correct.block ss (elabStmtsA.correct ss)).complete hrefines_fm₀ helab
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok
    cases h : s <;> rw [h] at hok
    case declare n T => apply (elabStmtA.correct.declare n T).sound hrefines_fm₀ hok
    case exprStmt e₁ =>
      apply (elabStmtA.correct.exprStmt e₁ (elabExprA.correct e₁)).sound hrefines_fm₀ hok
    case ifStmt e₁ s₂ s₃ =>
      apply
        (elabStmtA.correct.ifStmt
            e₁ s₂ s₃ (elabExprA.correct e₁) (elabStmtA.correct s₂) (elabStmtA.correct s₃)).sound
          hrefines_fm₀ hok
    case block ss =>
      apply (elabStmtA.correct.block ss (elabStmtsA.correct ss)).sound hrefines_fm₀ hok

theorem elabStmtsA.correct (ss : List Stmt) :
    elabStmtsA.Correctness (cfg := cfg) ss := by
  constructor
  case complete =>
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab
    cases h : ss <;> rw [h] at helab
    case nil => apply elabStmtsA.correct.nil.complete hrefines_fm₀ helab
    case cons s ss =>
      apply (elabStmtsA.correct.cons s ss (elabStmtA.correct s) (elabStmtsA.correct ss)).complete
        hrefines_fm₀ helab
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok
    cases h : ss <;> rw [h] at hok
    case nil => apply elabStmtsA.correct.nil.sound hrefines_fm₀ hok
    case cons s ss =>
      apply (elabStmtsA.correct.cons s ss (elabStmtA.correct s) (elabStmtsA.correct ss)).sound
        hrefines_fm₀ hok
end

end FlowAnalysis
