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
import Std.Tactic.Do
import FlowAnalysis.Algorithm
import FlowAnalysis.Elaboration
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

-- Allows the use of `<+` notation for `List.Sublist`.
-- TODO: needed?
open scoped List

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
local notation "ValueModel" => ValueModel (τ := τ)
local notation "ValueModelA" => ValueModelA (τ := τ)

theorem AlgM_get_eq {fm} :
  (get : AlgM _) cfg fm = Except.ok (fm, fm) := rfl

theorem AlgM_pure_eq {α fm} {a : α} :
  (pure a : AlgM _) cfg fm = Except.ok (a, fm) := rfl

theorem AlgM_bind_eq {α β : Type} {x : AlgM α} {fm : FlowModelA}
    {f : α → AlgM β} :
  (x >>= f) cfg fm = match x cfg fm with
                 | Except.ok (a, hm') => f a cfg hm'
                 | Except.error e => Except.error e := by
  simp [bind, ReaderT.bind, StateT.bind]
  cases x cfg fm <;> rfl

theorem AlgM_map_eq {α β : Type} {fm : FlowModelA} {f : α → β} {x : AlgM α} :
  (f <$> x) cfg fm = match x cfg fm with
                 | Except.ok (a, hm') => Except.ok (f a, hm')
                 | Except.error e => Except.error e := by
  dsimp [Functor.map, StateT.instMonad, StateT.map, StateT.bind, StateT.pure, ExceptT.bind, ExceptT.pure, bind, pure]
  cases x cfg fm <;> trivial

theorem AlgM_modify_eq {f fm} :
    (modify : _ → AlgM _) f cfg fm = Except.ok ((), f fm) := rfl

theorem AlgM_set_eq {fm fm'} :
    (set : _ → AlgM _) fm' cfg fm = Except.ok ((), fm') := rfl

theorem AlgM_throw_eq_ok_contra {α e fmA₀ x fmA} :
    (throw e : AlgM α) cfg fmA₀ = Except.ok (x, fmA) ↔ False := by
  constructor
  case mp => intro h; contradiction
  case mpr => intro h; exfalso; assumption

structure ValueModelA.refines (vmA : ValueModelA) (vm : ValueModel) :
    Prop where
  types : vmA.promotedTypes = vm.promotedTypes.val

theorem ValueModelA.refines.unique {vmA : ValueModelA}
    {vm₁ vm₂ : ValueModel} :
    vmA.refines vm₁ → vmA.refines vm₂ → vm₁ = vm₂ := by
  intro h₁ h₂
  ext
  rw [←h₁.types, ←h₂.types]

@[simp]
theorem ValueModelA.refines.empty :
    (⟨[]⟩ : ValueModelA).refines ⟨∅⟩ := by
  constructor
  · simp

-- TODO: remove when no longer needed
@[simp]
theorem ValueModelA.refines.single {T : τ} :
    (⟨[T]⟩ : ValueModelA).refines ⟨.single T⟩ := by
  constructor
  · simp

theorem ValueModelA.refines.currentTypes {vmA : ValueModelA} {vm : ValueModel} {baseType : τ} :
    vmA.refines vm → vmA.currentType baseType = vm.currentType baseType := by
  intro hrefines
  simp [ValueModelA.currentType, ValueModelA.promotedType?, ValueModel.currentType]
  rw [hrefines.types]
  rfl

section
open FlowAnalysis.ValueModelA
open FlowAnalysis.PromotionChain
open Std.Do

-- TODO: remove?
lemma split_chain_at_index {i : Nat} {c : PromotionChain} (h : i < c.val.length) :
    ∃ (c' : PromotionChain) (x : τ) (c'' : PromotionChain) (hbounds : ∀ T' ∈ c''.val, T' < x),
      c.val[i] = x ∧
      c.val.take i = c'.val ∧
      c.val.take (i + 1) = c'.val ++ [x] ∧
      c.drop i = ⟨x::c''.val, isPromotionChain.cons hbounds c''.property⟩ ∧
      c.drop (i + 1) = c'' := by
  exists c.take i, c.val[i], c.drop (i + 1)
  exists by
    apply isPromotionChain.head_bounds
    suffices c.val[i] :: (c.drop (i + 1)).val = (c.drop i).val by
      rw [this]; apply (c.drop i).property
    simp
  simp

def stateIs {σs} (s : SVal.StateTuple σs) : SPred σs := SVal.curry (fun s' => ⟨s' = s⟩)

-- TODO: needed?
def currentIs (fmA : FlowModelA) :
    SPred [Config, FlowModelA] :=
  (SVal.getThe FlowModelA).evalsTo fmA

@[simp]
theorem curry_evalsTo_pure :
    (((SVal.curry fun _ => ULift.up v)).evalsTo (ULift.up v') : SPred σs) = ⌜v = v'⌝ := by
  apply SPred.bientails.to_eq
  induction σs
  case nil => grind
  case cons σ σs' ih => intro s; simp; assumption

-- TODO: rename and move to PromotionChain.lean if needed
lemma foo {c : PromotionChain} {ts : List τ} : c.val = ts → ∃ hvalid, c = ⟨ts, hvalid⟩ := by
  intro rfl; exists c.property

-- TODO: move to PromotionChain.lean if needed
lemma PromotionChain.membership_if_value_eq {c : PromotionChain} {ts : List τ} :
    c.val = ts → ∀ T, T ∈ c.val ↔ T ∈ ts := by
  intro rfl T; simp

-- TODO: maybe just go back to doing a normal split since I'm not trying to avoid simp anymore.
lemma WP_ite [Monad m] [WP m ps] {t e : m α} [Decidable c] (hifTrue : c → P ⊢ₛ wp⟦t⟧ Q)
    (hifFalse : ¬c → P ⊢ₛ wp⟦e⟧ Q) : P ⊢ₛ wp⟦if c then t else e⟧ Q := by
  mintro hP
  split
  case isTrue h => apply hifTrue h
  case isFalse h => apply hifFalse h

-- TODO: not sure I like this.
--theorem assert_spec {m ps α} {v : Option α} {s₀ a} [Monad m] [MonadExcept String m] [WPMonad m ps] :
--    ⦃stateIs s₀ ∧ ⌜v = some a⌝⦄ (Option.assert v : m _) ⦃⇓ r => stateIs s₀ ∧ ⌜r = a⌝⦄ := by
--  mintro h; mcases h with ⟨hstate, hv⟩; subst hv
--  unfold Option.assert; simp
--  mconstructor; massumption; mpure_intro; trivial

@[simp]
theorem assert_rw [Monad m] [MonadExcept String m] :
    (Option.assert (some x) : m _) = pure x := by rfl

lemma bar {i T} {c : PromotionChain} (hrange : i < c.val.length) (hT : T = c.val[i]) : ∃ hvalid,
    c.drop i = ⟨T :: c.drop (i+1), hvalid⟩ := by
  rcases c with ⟨ts, hvalid⟩; simp_all

lemma baz {m α} {i : Nat} {ts : List α} [Monad m] [MonadExcept String m] (hrange: i < ts.length) :
  ts[i]?.assert = (pure ts[i] : m _) := by simp_all [Option.assert]

theorem joinPromotedTypesA'_correct [Monad m] [MonadExcept String m] [Lean.Order.MonadTail m]
    [WPMonad m ps] (c₁ c₂ : PromotionChain) :
    0 < c₁.val.length → c₁.val.length ≤ c₂.val.length → ⦃stateIs s₀⦄ (joinPromotedTypesA' c₁.val c₂.val : m _)
    ⦃⇓ r => stateIs s₀ ∧ ⌜r = (c₁.join c₂).val⌝⦄ := by
  intro hc₁_nonEmpty hc₁_smaller
  mintro hstate
  unfold joinPromotedTypesA'
  rw [baz hc₁_nonEmpty, baz (by order)]
  simp
  mspec Spec.forIn_loop
  case measure => exact fun vars => SVal.curry fun _ => ⟨match vars with
    | ⟨_, i₁, i₂, _⟩ => c₁.val.length + c₂.val.length - i₁ - i₂
  ⟩
  case inv => exact (⇓ cursor => (match cursor with
    | .inl (retval, i₁, i₂, T₁, T₂, result) =>
      spred(stateIs s₀ ∧ ⌜retval = none ∧ (∃ hrange₁ : i₁ < c₁.val.length, T₁ = c₁.val[i₁]) ∧
        (∃ hrange₂ : i₂ < c₂.val.length, T₂ = c₂.val[i₂]) ∧
        (c₁.join c₂).val =
          retval.getD (result.getD (c₁.val.take i₁) ++ (c₁.drop i₁).join (c₂.drop i₂))⌝)
    | .inr (retval, i₁, i₂, T₁, T₂, result) =>
      spred(stateIs s₀ ∧ ⌜retval = some (c₁.join c₂).val⌝)
    ))
  case step =>
    simp; intro retval i₁ i₂ T₁ T₂ result mb
    mintro h; mcases h with ⟨hmb, hstate, h⟩; rcases h with
      ⟨rfl, ⟨hrange₁, hT₁⟩, ⟨hrange₂, hT₂⟩, hjoin⟩; simp at hjoin
    split
    case isTrue heq =>
      subst heq
      -- T₁ belongs in the output, so we can rewrite hjoin.
      have hT₁_belongs : (c₁.drop i₁).join (c₂.drop i₂) =
          T₁ :: (c₁.drop (i₁+1)).join (c₂.drop (i₂+1)) := by
        obtain ⟨hvalid_drop₁, hdrop₁⟩ := bar hrange₁ hT₁; rw [hdrop₁]
        obtain ⟨hvalid_drop₂, hdrop₂⟩ := bar hrange₂ hT₂; rw [hdrop₂]
        simp
      rw [hT₁_belongs] at hjoin; clear hT₁_belongs
      split
      case isTrue hdone₁ =>
        rw [hdone₁] at hjoin; simp at hjoin; split
        case isTrue hresult =>
          subst hresult; simp [hT₁] at hjoin ⊢; rw [hdone₁] at hjoin; simp at hjoin
          mconstructor; massumption; mpure_intro; aesop
        case isFalse hresult =>
          rcases result; contradiction; rename_i result; clear hresult; simp at hjoin
          simp; mconstructor; massumption; mpure_intro; aesop
      case isFalse hrange₁ =>
        replace hrange₁ : i₁ + 1 < c₁.val.length := by grind
        rw [baz hrange₁]; simp
        split
        case isTrue hdone₂ =>
          rw [hdone₂] at hjoin; simp at hjoin; split
          case isTrue hresult =>
            subst hresult; simp [hT₂] at hjoin ⊢
            mconstructor; massumption; mpure_intro
            rw [show c₁.val.take (i₁+1) = c₁.val.take i₁ ++ [T₁] by simp_all, hT₂]; aesop
          case isFalse hresult =>
            rcases result; contradiction; rename_i result _; clear hresult; simp at hjoin ⊢
            mconstructor; massumption; mpure_intro; aesop
        case isFalse hrange₂ =>
          replace hrange₂ : i₂ + 1 < c₂.val.length := by grind
          simp; rw [baz hrange₂]; simp
          mexists c₁.val.length + c₂.val.length - (i₁ + 1) - (i₂ + 1); simp
          mconstructor; · mpure_intro; trivial
          mconstructor; · mpure_intro; grind
          mconstructor; massumption; mpure_intro
          constructor; · assumption
          constructor; assumption
          cases result
          case none =>
            simp at hjoin ⊢
            rw [show c₁.val.take (i₁+1) = c₁.val.take i₁ ++ [T₁] by simp_all]; simp; assumption
          case some result => simp at hjoin ⊢; assumption
    case isFalse hne =>
      split
      case isTrue hle =>
        -- T₂ does not belong in the output, so we can rewrite hjoin.
        have hT₂_notBelongs : (c₁.drop i₁).join (c₂.drop i₂) =
            (c₁.drop i₁).join (c₂.drop (i₂+1)) := by
          obtain ⟨hvalid_drop₁, hdrop₁⟩ := bar hrange₁ hT₁; rw [hdrop₁]
          obtain ⟨hvalid_drop₂, hdrop₂⟩ := bar hrange₂ hT₂; rw [hdrop₂]
          simp [hne, hle]
        rw [hT₂_notBelongs] at hjoin; clear hT₂_notBelongs
        split
        case isTrue hdone₂ =>
          rw [hdone₂] at hjoin; simp at hjoin; split
          case isTrue hresult =>
            subst hresult; simp [hT₁] at hjoin ⊢
            split
            case isTrue hrange₁ => simp; mconstructor; massumption; mpure_intro; simp_all
            case isFalse hrange₁ => simp; mconstructor; massumption; mpure_intro; aesop
          case isFalse hresult =>
            rcases result; contradiction; rename_i result; clear hresult; simp at hjoin
            simp; mconstructor; massumption; mpure_intro; aesop
        case isFalse hrange₂ =>
          replace hrange₂ : i₂ + 1 < c₂.val.length := by grind
          simp; rw [baz hrange₂]; simp
          mexists c₁.val.length + c₂.val.length - i₁ - (i₂ + 1)
          mconstructor; · mpure_intro; trivial
          mconstructor; · mpure_intro; grind
          mconstructor; massumption; mpure_intro
          constructor; · exists hrange₁
          constructor; · assumption
          cases result
          case none => simp at hjoin ⊢; assumption
          case some result => simp at hjoin ⊢; assumption
      case isFalse hnotLe =>
        -- T₁ does not belong in the output, so we can rewrite hjoin.
        have hT₁_notBelongs : (c₁.drop i₁).join (c₂.drop i₂) =
            (c₁.drop (i₁+1)).join (c₂.drop i₂) := by
          obtain ⟨hvalid_drop₁, hdrop₁⟩ := bar hrange₁ hT₁; rw [hdrop₁]
          obtain ⟨hvalid_drop₂, hdrop₂⟩ := bar hrange₂ hT₂; rw [hdrop₂]
          simp [hne, hnotLe]
        rw [hT₁_notBelongs] at hjoin; clear hT₁_notBelongs
        split
        case isTrue hdone₁ =>
          rw [hdone₁] at hjoin; simp at hjoin ⊢
          mconstructor; massumption; mpure_intro; aesop
        case isFalse hrange₁ =>
          replace hrange₁ : i₁ + 1 < c₁.val.length := by grind
          simp; rw [baz hrange₁]; simp
          mexists c₁.val.length + c₂.val.length - (i₁ + 1) - i₂
          mconstructor; · mpure_intro; trivial
          mconstructor; · mpure_intro; grind
          mconstructor; massumption; mpure_intro
          constructor; · assumption
          constructor; · exists hrange₂
          cases result
          case none => simp at hjoin ⊢; assumption
          case some result => simp at hjoin ⊢; assumption
  case pre => simp; mconstructor; massumption; mpure_intro; grind
  case post.success r =>
    simp; mrename_i h; mcases h with ⟨hstate, hresult⟩; rw [hresult]; simp
    mconstructor; massumption; mpure_intro; trivial
  case post.except => simp

theorem joinPromotedTypesA_correct [Monad m] [MonadExcept String m] [Lean.Order.MonadTail m]
    [WPMonad m ps] (c₁ c₂ : PromotionChain) :
    ⦃stateIs s₀⦄ (joinPromotedTypesA c₁.val c₂.val : m _)
    ⦃⇓ r => stateIs s₀ ∧ ⌜r = (c₁.join c₂).val⌝⦄ := by
  unfold joinPromotedTypesA
  apply WP_ite
  case hifTrue =>
    intro hempty₁; simp [hempty₁]; mintro hstate; mconstructor; massumption; mpure_intro; trivial
  case hifFalse =>
  intro hnotEmpty₁; apply WP_ite
  case hifTrue =>
    intro hempty₂; simp [hempty₂]; mintro hstate; mconstructor; massumption; mpure_intro; trivial
  case hifFalse =>
  intro hnotEmpty₂
  apply WP_ite
  case hifTrue =>
    intro hc₁_longer; mintro hstate; simp; mspec joinPromotedTypesA'_correct
    · grind
    · order
    · rename_i r; mrename_i h; mcases h with ⟨hstate, hresult⟩
      mconstructor; massumption; mpure_intro
      rw [join.commutative]; assumption
  case hifFalse =>
    intro hc₁_shorter; mintro hstate; simp; mspec joinPromotedTypesA'_correct
    · grind
    · order

theorem AlgM.of_wp_run_eq
    {α : Type}
    {x : α} {prog : AlgM α} {fmA₀ fmA : FlowModelA}
    (h : prog.run cfg fmA₀ = .ok (x, fmA)) (P : α → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓? a => ⌜P a⌝)) → P x := by
  intro hwp
  apply ReaderT.of_wp_run (m := StateT FlowModelA (ExceptT String Id)) (ρ := Config) (prog := prog)
    (r := cfg) P
  case hcan =>
    simp [MonadAttach.CanReturn, Id.run, StateT.run]
    exists fmA₀, fmA
  case hwp =>
    have := hwp cfg
    simp at this ⊢
    assumption

lemma wp_expand_readerT {prog : ReaderT ρ m α} [WP m ps] :
    (wp⟦prog⟧ Q) r = wp⟦prog r⟧ (fun a => Q.fst a r, Q.snd) := by rfl

lemma wp_expand_stateT {prog : StateT σ m α} [WP m ps] :
    (wp⟦prog⟧ Q) s = wp⟦prog s⟧ (fun x => Q.fst x.fst x.snd, Q.snd) := by rfl

lemma wp_expand_exceptT {prog : ExceptT ε m α} [WP m ps] :
    wp⟦prog⟧ Q = wp⟦prog.run⟧ (fun x =>
      match x with
      | Except.ok a => Q.fst a
      | Except.error e => Q.snd.fst e,
      Q.snd.snd) := by
  rewrite [WP.wp, ExceptT.instWP]
  simp

-- TODO: bad name?
lemma wp_expand_id {α Q} {prog : Id α} :
    wp⟦prog⟧ Q = wp⟦prog⟧ (PostCond.noThrow fun a => ⟨(Q.fst a).down⟩) := by rfl

/--
Given a WP characterization of an (AlgM α) program that is known not to raise errors, an input
state, and a proof that the preconditions are satisfied, this theorem can be used to obtain:
- The output of the program
- The final state of the program
- A proof that the postcondition holds for the given output and final state
- A proof that the program, when run, actually produces the given output and final state.
-/
theorem AlgM.output_of_wp_run {P : Config → FlowModelA → ULift Prop}
    {Q : α → Config → FlowModelA → ULift Prop} {prog : AlgM α}
    (hwp : P ⊢ₛ wp⟦prog⟧ (.noThrow Q)) cfg fmA₀ :
    (P cfg fmA₀).down → ∃ a fmA, (Q a cfg fmA).down ∧ prog cfg fmA₀ = .ok (a, fmA) := by
  intro hpre
  specialize hwp cfg fmA₀ hpre
  simp [WP.wp, ReaderT.run, StateT.run, ExceptT.run, Id.run] at hwp
  cases hok : prog cfg fmA₀ <;> simp [hok] at hwp
  case ok r => exists r.fst, r.snd
  case error e => simp [ExceptConds.false, ExceptConds.const] at hwp

/--
Given a WP characterization of an (AlgM α) program that might raise errors, an input state, a proof
that the preconditions are satisfied, and a known output of the program, this theorem can be used to
obtain a proof that the known output actually satisfies the postcondition.

TODO: needed?
-/
theorem AlgM.post_of_wp_run {P : Config → FlowModelA → ULift Prop}
    {Q : α → Config → FlowModelA → ULift Prop} {prog : AlgM α}
    (hwp : P ⊢ₛ wp⟦prog⟧ (.mayThrow Q)) cfg fmA₀ :
    (P cfg fmA₀).down → ∀ a fmA, prog cfg fmA₀ = .ok (a, fmA) → (Q a cfg fmA).down := by
  intro hpre
  specialize hwp cfg fmA₀ hpre
  simp [WP.wp, ReaderT.run, StateT.run, ExceptT.run, Id.run] at hwp
  cases hok : prog cfg fmA₀ <;> simp [hok] at hwp
  case ok r =>
    intro a' fmA' hok'
    injection hok' with hok'; subst hok'
    simp at hwp; assumption
  case error e => intro a' fmA' hok'; contradiction

theorem joinPromotedTypes_correct (c₁ c₂ : PromotionChain) :
    (joinPromotedTypesA c₁.val c₂.val : ExceptT String Id _).run = .ok (c₁.join c₂).val := by
  symm; apply ExceptT.of_wp_run (prog := (joinPromotedTypesA c₁.val c₂.val : ExceptT String Id _))
  · simp [MonadAttach.CanReturn, Id.run]
  · mspec joinPromotedTypesA_correct
    rename_i r
    mrename_i h
    mcases h with ⟨hstate, hr⟩
    mpure_intro
    simp [hr]
end

theorem ValueModelA.refines.join {vmA₁ vmA₂ : ValueModelA}
    {vm₁ vm₂ : ValueModel} :
    vmA₁.refines vm₁ → vmA₂.refines vm₂ → (vmA₁.join vmA₂).refines (vm₁.join vm₂) := by
  rintro hrefines₁ hrefines₂
  simp [ValueModelA.join, ValueModel.join]
  simp [hrefines₁.types, hrefines₂.types]
  rw [joinPromotedTypes_correct vm₁.promotedTypes vm₂.promotedTypes]
  constructor; simp

inductive FlowModelA_refines_cases (fmA : FlowModelA)
    (fm : FlowModel) (v : Variable) : Prop where
  -- TODO: rename to "absent"?
  | nones (hlookupA : fmA.env[v]? = none) (hlookup : fm.env v = none) :
      FlowModelA_refines_cases fmA fm v
  -- TODO: rename to "present"?
  | somes
        {vmA : ValueModelA} {vm : ValueModel} (hlookupA : fmA.env[v]? = some vmA)
        (hlookup : fm.env v = some vm) (hrefines_vm : vmA.refines vm) :
      FlowModelA_refines_cases fmA fm v

structure FlowModelA.refines (fmA : FlowModelA)
    (fm : FlowModel) : Prop where
  lookup (v : Variable) : FlowModelA_refines_cases fmA fm v
  -- TODO: needed?
  --nones (v : Variable) : fmA.env[v]? = none ↔ fm.env v = none
  --somes
  --  {v : Variable} {vmA : ValueModelA} {vm : ValueModel}
  --  (hsomeA : fmA.env[v]? = some vmA) (hsome : fm.env v = some vm) :
  --  vmA.refines vm

-- TODO: needed?
--theorem FlowModelA.refines.mems
--    {fmA : FlowModelA} {fm : FlowModel} (hrefines : fmA.refines fm) (v : Variable) :
--    v ∈ fmA.env ↔ (fm.env v).isSome := by sorry

-- TODO: needed?
--theorem FlowModelA.refines.notMems
--    {fmA : FlowModelA} {fm : FlowModel} (hrefines : fmA.refines fm) (v : Variable) :
--    ¬v ∈ fmA.env ↔ fm.env v = none := by rw [←hrefines.nones v]; simp

-- TODO: needed?
--theorem FlowModelA.refines.eq_some_iff
--    {fmA : FlowModelA} {fm : FlowModel} {vm : ValueModel} {v : Variable}
--    (hrefines : fmA.refines fm) :
--    fm.env v = some vm ↔ ∃ vmA : ValueModelA, fmA.env[v]? = some vmA ∧ vmA.refines vm := by
--  constructor
--  case mp =>
--    intro hlookup
--    cases hlookupA : fmA.env[v]? <;> simp
--    case none => rw [hrefines.nones] at hlookupA; simp_all
--    case some vmA => exact hrefines.somes hlookupA hlookup
--  case mpr =>
--    rintro ⟨vmA, hlookupA, hrefines_vm⟩
--    cases hlookup : fm.env v <;> simp
--    case none => rw [←hrefines.nones] at hlookup; simp_all
--    case some vm' =>
--      have hrefines_vm' : vmA.refines vm' := hrefines.somes hlookupA hlookup
--      apply ValueModelA.refines.unique hrefines_vm' hrefines_vm

theorem FlowModelA.refines.empty :
    (.empty : FlowModelA).refines FlowModel.empty := by
  constructor; intro v
  apply FlowModelA_refines_cases.nones (by simp [FlowModelA.empty]) (by simp [FlowModel.empty])

theorem FlowModelA.refines.isEmpty {fmA : FlowModelA} {fm : FlowModel}
    (hrefines : fmA.refines fm) :
    fmA.env.isEmpty ↔ ∀ v, fm.env v = none := by
  constructor
  case mp =>
    intro hemptyA v
    have : fmA.env[v]? = none := by exact Std.HashMap.getElem?_of_isEmpty hemptyA
    cases hrefines.lookup v <;> simp_all
  case mpr =>
    intro hempty
    rw [Std.HashMap.isEmpty_iff_forall_not_mem]
    intro v
    cases hrefines.lookup v <;> simp_all

@[simp]
theorem FlowModelA.refines.isEmpty_simp {fmA : FlowModelA} :
    fmA.env.isEmpty → fmA.refines ⟨fun _ => none⟩ := by
  intro hempty
  constructor; intro v
  apply FlowModelA_refines_cases.nones (Std.HashMap.getElem?_of_isEmpty hempty) (by simp)

lemma FlowModelA.refines.some_if_some {fmA : FlowModelA}
    {fm₁ fm₂ : FlowModel} {v vm} :
    fmA.refines fm₁ → fmA.refines fm₂ → fm₁.env v = some vm → fm₂.env v = some vm := by
  intro hrefines₁ hrefines₂ hlookup₁
  cases hrefines₁.lookup v <;> simp_all; subst_eqs
  case somes vmA₁ hlookupA₁ hlookup₁' hrefines_vm₁ =>
    cases hrefines₂.lookup v <;> simp_all; subst_eqs
    case somes vm₂ hlookupA₂ hlookup₂ hrefines_vm₂ =>
      exact ValueModelA.refines.unique hrefines_vm₂ hrefines_vm₁

-- TODO: needed?
theorem FlowModelA.refines.unique {fmA : FlowModelA} {fm₁ fm₂ : FlowModel} :
    fmA.refines fm₁ → fmA.refines fm₂ → fm₁ = fm₂ := by
  intro hrefines₁ hrefines₂
  ext; rename_i v vm
  constructor <;> apply some_if_some (by assumption) (by assumption)

@[simp]
theorem FlowModelA.refines.insert {fmA : FlowModelA} {fm : FlowModel}
    {vmA : ValueModelA} {vm : ValueModel} (v : Variable) :
    fmA.refines fm → vmA.refines vm →
    (FlowModelA.mk (fmA.env.insert v vmA)).refines (fm.set v vm) := by
  intro hrefines_fm hrefines_vm; constructor; intro v'
  by_cases heq : v = v' <;> subst_eqs
  case pos =>
    apply FlowModelA_refines_cases.somes (by simp; rfl) (by simp; rfl) (by assumption)
  case neg =>
    cases hrefines_fm.lookup v'
    case nones hlookupA hlookup =>
      apply FlowModelA_refines_cases.nones (by simp_all) (by simp_all)
    case somes vmA' vm' hlookupA hlookup hrefines_vm' =>
      apply FlowModelA_refines_cases.somes
        (by simp_all [Std.HashMap.getElem?_insert]; rfl) (by simp_all; rfl) (by assumption)

theorem FlowModelA.refines.tryPromote
    {fmA : FlowModelA} {fm : FlowModel} (hrefines : fmA.refines fm) ref? T :
    ∃ fmA', tryPromoteA ref? T cfg fmA = Except.ok ((), fmA') ∧
    fmA'.refines (fm.tryPromote ref? T) := by
  simp [tryPromoteA, FlowModel.tryPromote]
  cases ref? <;> simp_all [AlgM_pure_eq, AlgM_bind_eq]
  case none => exists fmA
  case some ref =>
    cases ref; simp_all
    case var v =>
      cases hrefines.lookup v <;> simp_all [AlgM_get_eq, AlgM_pure_eq]
      case nones => exists fmA
      case somes vmA vm hlookupA hlookup hrefines_vm =>
        rw [hrefines_vm.currentTypes]
        by_cases hT_lt_current : T < vm.currentType v.type <;>
          simp_all [AlgM_pure_eq, AlgM_modify_eq]
        case neg => exists fmA
        case pos =>
          exists ⟨fmA.env.insert v ⟨[T]⟩⟩
          simp
          apply FlowModelA.refines.insert v hrefines
          simp

-- TODO: needed?
section
variable {α β : Type} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {f : β → β → β} {m₁ m₂ : Std.HashMap α β}

theorem mergeMaps_none₁ {k : α} : k ∉ m₁ → k ∉ mergeMaps f m₁ m₂ := by
  simp_all [mergeMaps, Std.HashMap.mem_filterMap]

theorem mergeMaps_none₂ {k : α} : k ∉ m₂ → k ∉ mergeMaps f m₁ m₂ := by
  simp_all [mergeMaps, Std.HashMap.mem_filterMap]

theorem mergeMaps_some {k : α} {v₁ v₂ : β} :
    m₁[k]? = some v₁ → m₂[k]? = some v₂ → (mergeMaps f m₁ m₂)[k]? = f v₁ v₂ := by
  simp_all [mergeMaps]

end

theorem FlowModelA.refines.join {fmA₁ fmA₂ : FlowModelA}
    {fm₁ fm₂ : FlowModel} :
    fmA₁.refines fm₁ → fmA₂.refines fm₂ → (fmA₁.join fmA₂).refines (fm₁.join fm₂) := by
  intro hrefines₁ hrefines₂
  simp [FlowModelA.join, FlowModel.join]
  by_cases_iff hrefines₁.isEmpty <;> simp_all
  case neg hnonEmpty₁ hnonEmptyA₁ =>
    by_cases_iff hrefines₂.isEmpty <;> simp_all
    case pos => (conv => enter [2, 1, v]; tactic => split); simp_all
    case neg hnonEmpty₂ hnonEmptyA₂ =>
      constructor; intro v
      cases hrefines₁.lookup v
      case nones hlookupA₁ hlookup₁ =>
        apply FlowModelA_refines_cases.nones (by simp_all [mergeMaps_none₁]) (by simp_all)
      case somes vmA₁ vm₁ hlookupA₁ hlookup₁ hrefines_vm₁ =>
        cases hrefines₂.lookup v
        case nones hlookupA₂ hlookup₂ =>
          apply FlowModelA_refines_cases.nones (by simp_all [mergeMaps_none₂]) (by simp_all)
        case somes vmA₂ vm₂ hlookupA₂ hlookup₂ hrefines_vm₂ =>
          apply FlowModelA_refines_cases.somes
            (by simp_all [mergeMaps_some]; rfl)
            (by simp_all; rfl)
            (by simp_all [hrefines_vm₁.join hrefines_vm₂])

structure ExprModelA.refines (emA : ExprModelA)
    (fmA : FlowModelA) (em : ExprModel) :
    Prop where
  types : emA.type = em.type
  ref?s : emA.ref? = em.ref?
  fm_trues : (emA.boolInfo.getD (fmA, fmA)).fst.refines em.fm_true
  fm_falses : (emA.boolInfo.getD (fmA, fmA)).snd.refines em.fm_false

theorem ExprModelA.refines.noBoolInfo {fmA fm} (hrefines : fmA.refines fm) T ref? :
    (⟨T, ref?, none⟩ : ExprModelA).refines fmA ⟨T, ref?, fm, fm⟩ := by
  constructor <;> simp_all

-- TODO: needed?
--theorem exprModelA_boolInfo_getD_sound {emA fmA fmA_true fmA_false} :
--    (emA : ExprModelA).boolInfo.getD (fmA, fmA) = (fmA_true, fmA_false) →
--    emA.interp fmA = ⟨emA.type, emA.ref?, fmA_true.interp, fmA_false.interp⟩ := by
--  intro h
--  simp [ExprModelA.interp]
--  simp [Option.getD] at h
--  cases hboolInfo : emA.boolInfo <;> simp [hboolInfo] at h <;> clear hboolInfo
--  case none =>
--    rcases h with ⟨rfl, rfl⟩ ; simp
--  case some boolInfo =>
--    subst h; simp

-- TODO: needed?
@[simp]
theorem ExprModelA.refines.fm_eq_afters_if_noBoolInfo {emA : ExprModelA} {fmA}
    {em : ExprModel} (hboolInfo : emA.boolInfo = none) :
    emA.refines fmA em → em.fm_after = em.fm_true ∧ em.fm_true = em.fm_false := by
  intro hrefines_em
  have hrefines_fm_true := hrefines_em.fm_trues; simp [hboolInfo] at hrefines_fm_true
  have hrefines_fm_false := hrefines_em.fm_falses; simp [hboolInfo] at hrefines_fm_false
  have hfm_true_eq_false := hrefines_fm_true.unique hrefines_fm_false
  simp [ExprModel.fm_after, hfm_true_eq_false]

-- TODO: needed?
--@[simp]
--theorem ExprModelA.refines.refines_fm_true_eq_false_eq_after_if_noBoolInfo
--    {emA : ExprModelA} {fmA em} (hboolInfo : emA.boolInfo = none) :
--    emA.refines fmA em →
--    em.fm_true = em.fm_false ∧ em.fm_false = em.fm_after := by sorry

-- TODO: trying to fold this into elabExprA_correct
--theorem elabExprA.consistent_emA_fmA {e fmA₀ m emA fmA em} :
--    elabExprA e fmA₀ = Except.ok ((m, emA), fmA) → emA.refines fmA em →
--    fmA.refines em.fm_after := by
--  intro hok hrefines_em
--  cases e <;> simp [elabExprA] at hok
--  case var v =>
--    cases hlookup : fmA₀.env[v]? <;> simp [hlookup] at hok
--    case some vmA =>
--      rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
--      exact hrefines_em.refines_fm_after_if_noBoolInfo rfl
--  case nullCheck e₁ =>
--    cases hok₁ : elabExprA e₁ fmA₀ <;> simp [hok₁] at hok
--    rename_i this; rcases this with ⟨⟨m₁, emA₁⟩, fmA₁⟩; simp at hok
--    cases htryPromote : tryPromoteA emA₁.ref? emA₁.type.nonNull fmA₁ <;> simp [htryPromote] at hok
--    rename_i this; rcases this with ⟨_, fmA'⟩; simp at hok
--    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
--    exact hrefines_em.refines_fm_after_if_noBoolInfo rfl
--  case as e₁ T =>
--    cases hok₁ : elabExprA e₁ fmA₀ <;> simp [hok₁] at hok
--    rename_i this; rcases this with ⟨⟨m₁, emA₁⟩, fmA₁⟩; simp at hok
--    cases htryPromote : tryPromoteA emA₁.ref? T fmA₁ <;> simp [htryPromote] at hok
--    rename_i this; rcases this with ⟨_, fmA'⟩; simp at hok
--    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
--    exact hrefines_em.refines_fm_after_if_noBoolInfo rfl
--  case null =>
--    rcases hok with ⟨⟨rfl, rfl⟩, rfl⟩
--    exact hrefines_em.refines_fm_after_if_noBoolInfo rfl

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
    intro fm₀ m em fmA₀ hrefines_fm₀ helab; simp [elabExprA, AlgM_get_eq, AlgM_bind_eq]
    cases helab; case var vm T hlookup hcurrentType =>
      cases hrefines_fm₀.lookup v <;> simp_all [AlgM_pure_eq]; subst_eqs
      case somes vmA hlookupA hlookup hrefines_vm =>
        simp [hrefines_vm.currentTypes]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩; rotate_left 2
        · congr; rfl; rfl
        · assumption
        · constructor <;> simp <;> assumption
  case sound =>
    intro fm₀ m emA fmA fmA₀ hrefines_fm₀ hok; simp [elabExprA, AlgM_bind_eq] at hok
    cases hrefines_fm₀.lookup v <;> simp_all [AlgM_get_eq, AlgM_throw_eq_ok_contra]
    case somes vmA vm hlookupA hlookup hrefines_vm =>
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
    intro fm₀ m em fmA₀ hrefines_fm₀ helab; simp [elabExprA, AlgM_bind_eq, AlgM_map_eq]
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
    intro fm₀ m emA fmA fmA₀ hrefines_fm₀ hok; simp [elabExprA, AlgM_bind_eq, AlgM_map_eq] at hok
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
    intro fmA₀ fm₀ m em hrefines_fm₀ helab; simp [elabExprA, AlgM_bind_eq, AlgM_map_eq]
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
    intro fm₀ m emA fmA fmA₀ hrefines_fm₀ hok; simp [elabExprA, AlgM_bind_eq, AlgM_map_eq] at hok
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
    intro fmA₀ fm₀ m em hrefines_fm₀ helab; simp [elabExprA, AlgM_pure_eq]
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
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab; simp [elabStmtA, AlgM_map_eq, AlgM_modify_eq]
    cases helab; case declare =>
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · apply hrefines_fm₀.insert ⟨n, T⟩ (by simp)
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtA] at hok
    rcases hok with ⟨rfl, rfl⟩
    exists fm₀.set ⟨n, T⟩ ⟨∅⟩
    constructor
    · apply ElabStmt.declare fm₀ n T
    · apply hrefines_fm₀.insert ⟨n, T⟩ ValueModelA.refines.empty

theorem elabStmtA.correct.exprStmt
    (e₁ : Expr) (hcorrect₁ : elabExprA.Correctness (cfg := cfg) e₁) :
    elabStmtA.Correctness (cfg := cfg) (.exprStmt e₁) := by
  constructor
  case complete =>
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab; simp [elabStmtA, AlgM_map_eq]
    cases helab; case exprStmt em₁ helab₁ =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩
      obtain ⟨fmA₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · assumption
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtA, AlgM_map_eq] at hok
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
    intro fm₀ m em fmA₀ hrefines_fm₀ helab; simp [elabStmtA, AlgM_bind_eq]
    cases helab; case ifStmt m₁ em₁ m₂ fm₂ m₃ fm₃ his_bool helab₁ helab₂ helab₃ =>
      rcases em₁ with ⟨T₁, ref?₁, fm_true₁, fm_false₁⟩; simp_all
      obtain ⟨fmA₁, ⟨T₁', ref?₁', boolInfo₁⟩, hok₁, hrefines_fm₁, hrefines_em₁⟩ :=
        hcorrect₁.complete hrefines_fm₀ helab₁
      rcases hrefines_em₁.types with rfl; simp_all [AlgM_bind_eq, AlgM_map_eq, AlgM_set_eq]
      rcases hrefines_em₁.ref?s with rfl; simp_all
      obtain hrefines_fm₁_true := hrefines_em₁.fm_trues; simp_all
      obtain ⟨fmA₂, hok₂, hrefines_fm₂⟩ := hcorrect₂.complete hrefines_fm₁_true helab₂;
        simp_all [AlgM_get_eq]
      obtain hrefines_fm₁_false := hrefines_em₁.fm_falses; simp_all
      obtain ⟨fmA₃, hok₃, hrefines_fm₃⟩ := hcorrect₃.complete hrefines_fm₁_false helab₃; simp_all
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · exact FlowModelA.refines.join hrefines_fm₂ hrefines_fm₃
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtA, AlgM_bind_eq] at hok
    cases hok₁ : elabExprA e₁ cfg fmA₀ <;> simp_all; case ok result₁ =>
    rcases result₁ with ⟨⟨m₁, emA₁⟩, fmA₁⟩; simp_all
    rcases hcorrect₁.sound hrefines_fm₀ hok₁ with ⟨em₁, helab₁, hrefines_fm₁, hrefines_em₁⟩
    rcases emA₁ with ⟨T₁, ref?₁, boolInfo₁⟩
    rcases hrefines_em₁.types with rfl; simp_all
    by_cases his_bool : em₁.type = Γ.bool <;>
      simp_all [AlgM_bind_eq, AlgM_set_eq, AlgM_throw_eq_ok_contra];
      case pos =>
    cases hok₂ : elabStmtA s₂ cfg (boolInfo₁.getD (fmA₁, fmA₁)).fst <;> simp_all [AlgM_get_eq];
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
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab; simp [elabStmtA, AlgM_map_eq]
    cases helab; case block ms₁ helab₁ =>
    obtain ⟨fmA₁, hok₁, hrefines_fm₁⟩ := hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
    refine ⟨?_, ?_, ?_⟩; rotate_left
    · congr; rfl
    · assumption
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtA, AlgM_map_eq] at hok
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
    intro fm₀ m fm fmA₀ hrefines_fm₀ helab; simp [elabStmtsA, AlgM_bind_eq, AlgM_map_eq]
    cases helab; case cons fm₁ m₁ ms₂ helab₁ helab₂ =>
      obtain ⟨fmA₁, hok₁, hrefines_fm₁⟩ := hcorrect₁.complete hrefines_fm₀ helab₁; simp_all
      obtain ⟨fmA₂, hok₂, hrefines_fm₂⟩ := hcorrect₂.complete hrefines_fm₁ helab₂; simp_all
      refine ⟨?_, ?_, ?_⟩; rotate_left
      · congr; rfl
      · assumption
  case sound =>
    intro fm₀ m fmA fmA₀ hrefines_fm₀ hok; simp [elabStmtsA, AlgM_bind_eq, AlgM_map_eq] at hok
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
