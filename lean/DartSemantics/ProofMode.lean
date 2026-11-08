module
public import DartSemantics.PrimitiveLaws

/-!
# Proof-mode tactics

Tactics for proving weakest preconditions of `LoweredExpr`s in iris-lean's proof mode, modeled on
iris-lean's HeapLang tactics (whose own `wp_*` tactics only work for HeapLang). HeapLang is the
small example language that comes with Iris, which most Iris material uses; its tactics are the
usual way to step through a program in a proof. (The README's "Reading the Iris parts" section
explains proof mode, and weakest preconditions.)

Each tactic takes one or more steps of the program in the goal, so that a proof follows the
program's execution:

- `wp_value`: when the expression has completed, replace its weakest precondition with the
  postcondition applied to its outcome.
- `wp_pure`: take one head step that doesn't depend on, or change, the state.
- `wp_bind`: focus on the subexpression in evaluation position, if it hasn't completed, by binding
  over one evaluation context item.
- `wp_pures`: repeat the three above until none applies. The goal is then either a postcondition,
  or a weakest precondition of an expression whose next step involves the state (or a run-time
  subtype check), wrapped in the evaluation context it came from.
- `wp_alloc ℓ H`: take the step of a declaration at the start of a block, introducing the new cell
  `ℓ` and its points-to `H`.
- `wp_load H`: take the step of reading a variable or an instance variable, using the points-to
  `H` for the cell read. The value's dynamic type is proved automatically for the null object,
  booleans, integers, objects whose header is in the context, and values with a `HasDynamicType`
  hypothesis in the context. Pure side conditions (such as the subtype fact for the promotion
  check) are proved by `decide` or `rfl` when they can be, and otherwise left as goals after the
  main one.
- `wp_store H`: take the step of an assignment to a local variable, using the points-to `H` for
  the variable's cell, which afterwards holds the value assigned. If the variable may be `final`,
  the cell must be unassigned: that side condition is proved when the variable isn't `final`, or
  the cell is `.uninit`, and otherwise left as a goal after the main one.
- `wp_call hf`: take the step of a call of a top-level function whose arguments are all values,
  given the function table's declaration of it (`hf`). `dart_bind_params` then binds the formal
  parameters in the body, once their cells' locations are concrete.
- `wp_call_spec H`: take a call of a top-level function whose arguments are all values, using its
  specification `H` (a `FunSpec`).
- `wp_int_checked`: take the step of an arithmetic operator in integer mode `checked` whose result
  can't be computed by `rfl` (because its operands aren't concrete numbers), leaving the side
  condition that the result is in 64-bit range as a goal.
- `wp_loop_step`: unroll one iteration of a loop. Usually the loop invariant rule is more
  convenient: apply `tac_wp_loop_inv`.

`wp_pures` also takes the steps of literals, returns, labeled statements and breaks (and the
propagation of returns and breaks), the body of a running call (`frame`) once it has completed,
and intrinsic checks, arithmetic, comparisons and equality whose answer `rfl` can compute. It
doesn't run a loop, which it would unroll forever. To reason about a function's body separately
from the call's outcome, apply `tac_wp_frame`, and similarly `tac_wp_labeled` for a labeled
statement.

Steps that involve a run-time subtype check (cast expressions and is-expressions) or a getter that
is user code are taken by applying the laws in `PrimitiveLaws.lean` directly.

Each tactic works by applying a lemma whose conclusion is a proof-mode goal `Δ ⊢ WP e {{ Φ }}`
(where `Δ` is the proof mode's context of Iris hypotheses) for a particular shape of `e`, so that
Lean's unifier, rather than iris-lean's `iapply`, matches it against the goal. (`iapply` doesn't
unfold definitions such as `EctxItem.fill`.)

These macros are deliberately simple. If their error messages or performance become a problem once
there are significant proofs, a meta-level implementation (in the style of Rocq's HeapLang
tactics, with a `PureExec` class and a tactic that finds the redex in an evaluation context, or
tactics that build proof terms directly) may be worth the extra code.
-/

namespace DartSemantics

open DartLang Iris Iris.BI Iris.ProgramLogic Iris.Std

variable {τ : Type}

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)
local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Cell" => Cell (τ := τ)

/-! Rewrite rules that `dart_wp_tidy` uses to tidy goals after a step. -/

public theorem tidy_toExpr_normal (v : Value) :
    (DartLang.Outcome.normal v).toExpr = LoweredExpr.val v := rfl
public theorem tidy_toExpr_throwing (v : Value) :
    (DartLang.Outcome.throwing v).toExpr = LoweredExpr.throwing v := rfl
public theorem tidy_fill_nullCheck (m : LoweredExpr) :
    (EctxItem.nullCheck (τ := τ)).fill m = .nullCheck m := rfl
public theorem tidy_fill_as (T : τ) (m : LoweredExpr) : (EctxItem.as T).fill m = .as m T := rfl
public theorem tidy_fill_is (T : τ) (m : LoweredExpr) : (EctxItem.is T).fill m = .is m T := rfl
public theorem tidy_fill_cond (m₂ m₃ : LoweredExpr) (T : τ) (m : LoweredExpr) :
    (EctxItem.cond m₂ m₃ T).fill m = .cond m m₂ m₃ T := rfl
public theorem tidy_fill_propertyGet (p : Property) (T : τ) (m : LoweredExpr) :
    (EctxItem.propertyGet p T).fill m = .propertyGet m p T := rfl
public theorem tidy_fill_seq (m₂ m : LoweredExpr) : (EctxItem.seq m₂).fill m = .seq m m₂ := rfl
public theorem tidy_fill_variableSetAt (x : Variable) (ℓ : Loc) (m : LoweredExpr) :
    (EctxItem.variableSetAt x ℓ).fill m = .variableSetAt x ℓ m := rfl
public theorem tidy_toExpr_returning (v : Value) :
    (DartLang.Outcome.returning v).toExpr = LoweredExpr.returning v := rfl
public theorem tidy_fill_call (f : String) (vs : List Value) (ms : List LoweredExpr) (T : τ)
    (m : LoweredExpr) : (EctxItem.call f vs ms T).fill m = .call f (vs.map .val ++ m :: ms) T :=
  rfl
public theorem tidy_fill_ret (m : LoweredExpr) : (EctxItem.ret (τ := τ)).fill m = .ret m := rfl
public theorem tidy_fill_frame (T : τ) (m : LoweredExpr) : (EctxItem.frame T).fill m = .frame m T :=
  rfl
public theorem tidy_fill_check (kind : CheckKind) (m : LoweredExpr) :
    (EctxItem.check (τ := τ) kind).fill m = .check kind m := rfl
public theorem tidy_fill_checkEqL (m₂ m : LoweredExpr) :
    (EctxItem.checkEqL m₂).fill m = .checkEq m m₂ := rfl
public theorem tidy_fill_checkEqR (v₁ : Value) (m : LoweredExpr) :
    (EctxItem.checkEqR v₁).fill m = .checkEq (.val v₁) m := rfl
public theorem tidy_toExpr_breaking (l : String) :
    (DartLang.Outcome.breaking (τ := τ) l).toExpr = LoweredExpr.breaking l := rfl
public theorem tidy_fill_labeled (l : String) (m : LoweredExpr) :
    (EctxItem.labeled (τ := τ) l).fill m = .labeled l m := rfl
public theorem tidy_fill_intBinL (op : IntBinOp) (mode : Option IntMode) (m₂ m : LoweredExpr) :
    (EctxItem.intBinL op mode m₂).fill m = .intBin op mode m m₂ := rfl
public theorem tidy_fill_intBinR (op : IntBinOp) (mode : Option IntMode) (v₁ : Value)
    (m : LoweredExpr) : (EctxItem.intBinR op mode v₁).fill m = .intBin op mode (.val v₁) m := rfl
public theorem tidy_fill_intNeg (mode : Option IntMode) (m : LoweredExpr) :
    (EctxItem.intNeg (τ := τ) mode).fill m = .intNeg mode m := rfl
public theorem tidy_fill_primEqL (m₂ m : LoweredExpr) :
    (EctxItem.primEqL m₂).fill m = .primEq m m₂ := rfl
public theorem tidy_fill_primEqR (v₁ : Value) (m : LoweredExpr) :
    (EctxItem.primEqR v₁).fill m = .primEq (.val v₁) m := rfl

variable [Γ : DartRuntimeTypeRepr τ]

/-! Head steps that `dart_pure_head_step` uses for the arguments of a call. -/

/--
An exception thrown by an argument of a call propagates out of the call: if the arguments split
into values, then throwing `v`, then the rest (`hsplit`), the call steps to throwing `v`.
-/
public theorem HeadStep.bubbleException_call [SemanticParams τ] {f : String}
    {args : List LoweredExpr} {T : τ} {vs : List Value} {v : Value} {ms : List LoweredExpr}
    {σ : State (τ := τ)} (hsplit : LoweredExpr.splitVals args = (vs, .throwing v :: ms)) :
    HeadStep (.call f args T) σ (.throwing v) σ := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  subst h
  exact .bubbleException (Ki := .call f vs ms T)

/--
A return in an argument of a call propagates out of the call: if the arguments split into values,
then returning `v`, then the rest (`hsplit`), the call steps to returning `v`.
-/
public theorem HeadStep.bubbleReturn_call [SemanticParams τ] {f : String}
    {args : List LoweredExpr} {T : τ} {vs : List Value} {v : Value} {ms : List LoweredExpr}
    {σ : State (τ := τ)} (hsplit : LoweredExpr.splitVals args = (vs, .returning v :: ms)) :
    HeadStep (.call f args T) σ (.returning v) σ := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  subst h
  exact .bubbleReturn (Ki := .call f vs ms T) rfl

/--
A break in an argument of a call propagates out of the call: if the arguments split into values,
then breaking out of `l`, then the rest (`hsplit`), the call steps to breaking out of `l`.
-/
public theorem HeadStep.bubbleBreak_call [SemanticParams τ] {f : String}
    {args : List LoweredExpr} {T : τ} {vs : List Value} {l : String} {ms : List LoweredExpr}
    {σ : State (τ := τ)} (hsplit : LoweredExpr.splitVals args = (vs, .breaking l :: ms)) :
    HeadStep (.call f args T) σ (.breaking l) σ := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  subst h
  exact .bubbleBreak (Ki := .call f vs ms T) rfl rfl
variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF] [P : SemanticParams τ]
-- (The type of `Φ` is spelled out because a local notation doesn't work in a `variable` binder; see
-- the same binder in `PrimitiveLaws.lean`.)
variable {s : Stuckness} {E : CoPset} {Φ : DartLang.Outcome (τ := τ) → IProp GF}
variable {Δ : IProp GF}

include hlc

open Iris.ProofMode (Entails')

/-! The proof-mode goal `Δ ⊢ P` is `Entails' Δ P`, so the tactic lemmas are stated with it. -/

/--
The proof-mode form of `wp_val`: to prove that `.val v` satisfies `Φ` from the hypotheses `Δ`, prove
`Φ (.normal v)` (`H`).
-/
public theorem tac_wp_val {v : Value} (H : Entails' Δ (Φ (.normal v))) :
    Entails' Δ (WP (LoweredExpr.val v) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_val v)

/--
The proof-mode form of `wp_throwing`: to prove that `.throwing v` satisfies `Φ` from the hypotheses
`Δ`, prove `Φ (.throwing v)` (`H`).
-/
public theorem tac_wp_throwing {v : Value} (H : Entails' Δ (Φ (.throwing v))) :
    Entails' Δ (WP (LoweredExpr.throwing v) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_throwing v)

/--
The proof-mode form of `wp_pure_step`: to prove that `e₁` satisfies `Φ` from the hypotheses `Δ`,
where `e₁` hasn't completed (`hv`) and in every state takes a head step to `e₂` that leaves the
state unchanged (`h`), prove that `e₂` satisfies `Φ` one step later (`H`).
-/
public theorem tac_wp_pure {e₁ e₂ : LoweredExpr} (hv : e₁.toOutcome? = none)
    (h : ∀ σ, HeadStep e₁ σ e₂ σ) (H : Entails' Δ iprop(▷ WP e₂ @ s; E {{ Φ }})) :
    Entails' Δ (WP e₁ @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_pure_step hv h)

/--
The proof-mode form of `wp_bind_item`, for an evaluation context item `Ki` whose hole holds an
expression `e` that hasn't completed (`_he`): to prove that `Ki.fill e` satisfies `Φ` from the
hypotheses `Δ`, prove that `e` satisfies the postcondition that plugging its outcome `o` back into
`Ki` satisfies `Φ` (`H`).
-/
public theorem tac_wp_bind (Ki : EctxItem (τ := τ)) {e : LoweredExpr} (_he : e.toOutcome? = none)
    (H : Entails' Δ (WP e @ s; E {{ o, WP (Ki.fill o.toExpr) @ s; E {{ Φ }} }})) :
    Entails' Δ (WP (Ki.fill e) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_bind_item Ki)

/--
The proof-mode form of `wp_blockDeclare`: to prove that a block that starts with a declaration of
`v` satisfies `Φ` from the hypotheses `Δ`, prove its premise (`H`).
-/
public theorem tac_wp_blockDeclare {v : Variable} {T : τ} {startsNull : Bool}
    {ms : List LoweredExpr}
    (H : Entails' Δ iprop(▷ (∀ ℓ, ℓ ↦ (if startsNull then .val .null else .uninit : Cell) -∗
        WP (LoweredExpr.block (LoweredExpr.resolveBlock v ℓ ms)) @ s; E {{ Φ }}))) :
    Entails' Δ (WP (LoweredExpr.block (.declare v T startsNull :: ms)) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_blockDeclare

/--
The proof-mode form of `wp_varAt`, with the subtype fact as a pure premise (`⌜S ≤ T⌝`), after the
dynamic type: to prove that reading `x`, resolved to the cell at `ℓ`, satisfies `Φ` from the
hypotheses `Δ`, prove `wp_varAt`'s premises (`H`).
-/
public theorem tac_wp_load {x : Variable} {T S : τ} {ℓ : Loc} {dq : DFrac} {v : Value}
    (H : Entails' Δ iprop(HasDynamicType v S ∗ ⌜S ≤ T⌝ ∗ ▷ (ℓ ↦{dq} (.val v : Cell)) ∗
        ▷ ((ℓ ↦{dq} (.val v : Cell)) -∗ Φ (.normal v)))) :
    Entails' Δ (WP (LoweredExpr.varAt x T ℓ) @ s; E {{ Φ }}) := by
  refine (show Δ ⊢ _ from H).trans ?_
  iintro ⟨#Hty, %hST, Hl, HΦ⟩
  iapply wp_varAt hST
  isplitr
  · iexact Hty
  isplitl [Hl]
  · iexact Hl
  · iexact HΦ

/--
The proof-mode form of `wp_propertyGetField`, with its pure facts as premises
(`⌜fs.lookup p.name = some ℓf⌝`, after the object's own cell, and `⌜S ≤ T⌝`, after the dynamic
type): to prove that reading property `p` of the object at `ℓ` satisfies `Φ` from the hypotheses
`Δ`, prove `wp_propertyGetField`'s premises (`H`).
-/
public theorem tac_wp_load_field {ℓ ℓf : Loc} {p : Property} {k : String} {T C S : τ}
    {fs : List (String × Loc)} {dq : DFrac} {w : Value}
    (H : Entails' Δ iprop(ℓ ↦{.discard} (.object k C fs : Cell) ∗ ⌜fs.lookup p.name = some ℓf⌝ ∗
        HasDynamicType w S ∗ ⌜S ≤ T⌝ ∗ ▷ (ℓf ↦{dq} (.val w : Cell)) ∗
        ▷ ((ℓf ↦{dq} (.val w : Cell)) -∗ Φ (.normal w)))) :
    Entails' Δ (WP (LoweredExpr.propertyGet (.val (.obj ℓ)) p T) @ s; E {{ Φ }}) := by
  refine (show Δ ⊢ _ from H).trans ?_
  iintro ⟨#Hobj, %hf, #Hty, %hST, Hl, HΦ⟩
  iapply wp_propertyGetField hf hST
  isplitr
  · iexact Hobj
  isplitr
  · iexact Hty
  isplitl [Hl]
  · iexact Hl
  · iexact HΦ

/--
The proof-mode form of `wp_variableSetAt`, with the points-to first (`H`), so that framing it
determines the cell, and then the facts that the cell isn't an object's own cell (`hc`) and, if
`x` is `final`, is unassigned (`hfin`): to prove that assigning `w` to `x`, resolved to the cell at
`ℓ`, satisfies `Φ` from the hypotheses `Δ`, prove `wp_variableSetAt`'s premises.
-/
public theorem tac_wp_store {x : Variable} {ℓ : Loc} {c : Cell} {w : Value}
    (H : Entails' Δ iprop(▷ (ℓ ↦ c) ∗ ▷ ((ℓ ↦ (.val w : Cell)) -∗ Φ (.normal w))))
    (hc : ∀ k C fs, c ≠ .object k C fs) (hfin : x.isFinal = true → c = .uninit) :
    Entails' Δ (WP (LoweredExpr.variableSetAt x ℓ (.val w)) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_variableSetAt hc hfin)

/--
The proof-mode form of `wp_value` for an expression that is returning `v`: to prove that
`.returning v` satisfies `Φ` from the hypotheses `Δ`, prove `Φ (.returning v)` (`H`).
-/
public theorem tac_wp_returning {v : Value} (H : Entails' Δ (Φ (.returning v))) :
    Entails' Δ (WP (LoweredExpr.returning v) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_value' (v := DartLang.Outcome.returning v))

/--
The proof-mode form of `wp_bind_item` for the argument of a call in evaluation position: if the
arguments split into values `vs`, then an argument `m` that hasn't completed, then the rest `ms`
(`hsplit` and `_hm`), then to prove that the call satisfies `Φ` from the hypotheses `Δ`, prove
that `m` satisfies the postcondition that plugging its outcome `o` back into the call satisfies
`Φ` (`H`). (`wp_bind` finds the split by computing `LoweredExpr.splitVals`.)
-/
public theorem tac_wp_bind_call {f : String} {args : List LoweredExpr} {T : τ} {vs : List Value}
    {m : LoweredExpr} {ms : List LoweredExpr} (hsplit : LoweredExpr.splitVals args = (vs, m :: ms))
    (_hm : m.toOutcome? = none)
    (H : Entails' Δ (WP m @ s; E {{ o, WP ((EctxItem.call f vs ms T).fill o.toExpr) @ s; E
      {{ Φ }} }})) :
    Entails' Δ (WP (LoweredExpr.call f args T) @ s; E {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit] at h
  subst h
  exact (show Δ ⊢ _ from H).trans (wp_bind_item (.call f vs ms T))

/--
The proof-mode form of `wp_call`, for a call whose arguments are all values `vs` (`hsplit`): to
prove that it satisfies `Φ` from the hypotheses `Δ`, where the function table declares `f` as `d`
(`hf`) with one formal parameter per argument (`hlen`), prove `wp_call`'s premise (`H`).
-/
public theorem tac_wp_call {f : String} {args : List LoweredExpr} {T : τ} {vs : List Value}
    {d : FunctionDecl (τ := τ)} (hsplit : LoweredExpr.splitVals args = (vs, []))
    (hf : P.functions f = some d) (hlen : d.params.length = vs.length)
    (H : Entails' Δ iprop(▷ (∀ ℓs, PointsToVals ℓs vs -∗
        WP (LoweredExpr.frame ((d.body.withIntMode (P.intModeOf f)).bindVariables
          (d.params.zip ℓs)) T) @ s; E {{ Φ }}))) :
    Entails' Δ (WP (LoweredExpr.call f args T) @ s; E {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit, List.append_nil] at h
  subst h
  exact (show Δ ⊢ _ from H).trans (wp_call hf hlen)

/--
The proof-mode form of `FunSpec.wp_call`, for a call whose arguments are all values `vs`
(`hsplit`): to prove that it satisfies `Φ` from the hypotheses `Δ`, prove that `f` meets a
specification, its precondition holds, and its postcondition implies `Φ` (`H`).
-/
public theorem tac_wp_call_spec {f : String} {args : List LoweredExpr} {T : τ} {vs : List Value}
    {Pre : List Value → IProp GF} {Post : List Value → DartLang.Outcome (τ := τ) → IProp GF}
    {Φ : DartLang.Outcome (τ := τ) → IProp GF} (hsplit : LoweredExpr.splitVals args = (vs, []))
    (H : Entails' Δ iprop(FunSpec f Pre Post ∗ Pre vs ∗ ∀ o, Post vs o -∗ Φ o)) :
    Entails' Δ (WP (LoweredExpr.call f args T) {{ Φ }}) := by
  have h := LoweredExpr.splitVals_append args
  rw [hsplit, List.append_nil] at h
  subst h
  exact (show Δ ⊢ _ from H).trans FunSpec.wp_call

/--
The proof-mode form of `wp_frame`: to prove that the body `m` of a running call satisfies `Φ` from
the hypotheses `Δ`, prove that `m` satisfies the postcondition that `Φ` holds, one step later, of
the call's outcome (`H`; see `framePost`).
-/
public theorem tac_wp_frame {m : LoweredExpr} {T : τ}
    (H : Entails' Δ (WP m @ s; E {{ o, framePost Φ o }})) :
    Entails' Δ (WP (LoweredExpr.frame m T) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_frame

/--
The proof-mode form of `wp_value` for an expression that is breaking out of labeled statement `l`:
to prove that `.breaking l` satisfies `Φ` from the hypotheses `Δ`, prove `Φ (.breaking l)` (`H`).
-/
public theorem tac_wp_breaking {l : String} (H : Entails' Δ (Φ (.breaking l))) :
    Entails' Δ (WP (LoweredExpr.breaking (τ := τ) l) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_value' (v := DartLang.Outcome.breaking l))

/--
The proof-mode form of `wp_labeled`: to prove that the labeled statement `l` with body `m`
satisfies `Φ` from the hypotheses `Δ`, prove that `m` satisfies the postcondition that `Φ` holds,
one step later, of the labeled statement's outcome (`H`; see `labeledPost`).
-/
public theorem tac_wp_labeled {l : String} {m : LoweredExpr}
    (H : Entails' Δ (WP m @ s; E {{ o, labeledPost l Φ o }})) :
    Entails' Δ (WP (LoweredExpr.labeled l m) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans wp_labeled

/--
The proof-mode form of `wp_loop_inv`: to prove that a loop with body `m` satisfies `Φ` from the
hypotheses `Δ`, given an invariant `I`, prove that `Δ` gives `I` (`HI`), and that `I` makes the
body satisfy the postcondition that gives `I` back when it completes normally, and `Φ` otherwise
(`H`; see `loopInvPost`).
-/
public theorem tac_wp_loop_inv {m : LoweredExpr} (I : IProp GF) (HI : Entails' Δ I)
    (H : I ⊢ WP m @ s; E {{ o, loopInvPost I Φ o }}) :
    Entails' Δ (WP (LoweredExpr.loop m) @ s; E {{ Φ }}) :=
  (show Δ ⊢ _ from HI).trans (wp_loop_inv I H)

/--
The proof-mode form of `wp_intBin`: to prove that a binary operator on integers `n₁` and `n₂`, in
integer mode `mode`, satisfies `Φ` from the hypotheses `Δ`, where its result is `v` (`h`), prove
that `Φ` holds of `v` one step later (`H`).
-/
public theorem tac_wp_intBin {op : IntBinOp} {mode : IntMode} {n₁ n₂ : Int} {v : Value}
    (h : op.eval mode n₁ n₂ = some v) (H : Entails' Δ iprop(▷ Φ (.normal v))) :
    Entails' Δ (WP (LoweredExpr.intBin (τ := τ) op (some mode) (.val (.int n₁)) (.val (.int n₂))) @
      s; E {{ Φ }}) :=
  (show Δ ⊢ _ from H).trans (wp_intBin h)

/--
`tac_wp_intBin` for an arithmetic operator in mode `checked`: to prove that it satisfies `Φ` from
the hypotheses `Δ`, where its exact result is `n` (`hn`, its result in mode `unbounded`), prove
that `n` is in 64-bit range (`hr`), and that `Φ` holds of `n` one step later (`H`).
-/
public theorem tac_wp_intBin_checked {op : IntBinOp} {n₁ n₂ n : Int}
    (hn : op.eval (τ := τ) .unbounded n₁ n₂ = some (.int n)) (hr : -2 ^ 63 ≤ n ∧ n < 2 ^ 63)
    (H : Entails' Δ iprop(▷ Φ (.normal (.int n)))) :
    Entails' Δ (WP (LoweredExpr.intBin (τ := τ) op (some .checked) (.val (.int n₁))
      (.val (.int n₂))) @ s; E {{ Φ }}) :=
  tac_wp_intBin (IntBinOp.eval_checked_of_range hn hr) H

end DartSemantics

/--
Take a head step that doesn't depend on, or change, the state (for `wp_pure`). Running a loop
(`HeadStep.loop`) isn't one of them: `wp_pures` would unroll it forever. Use the loop invariant rule
(`tac_wp_loop_inv`), or `wp_loop_step` to unroll one iteration.
-/
syntax "dart_pure_head_step" : tactic

macro_rules
  | `(tactic| dart_pure_head_step) => `(tactic| first
    | exact DartSemantics.HeadStep.null
    | exact DartSemantics.HeadStep.bool
    | exact DartSemantics.HeadStep.int
    | exact DartSemantics.HeadStep.declare
    | exact DartSemantics.HeadStep.blockNil
    | (refine DartSemantics.HeadStep.blockCons ?_; intro _ _ _ h; cases h)
    | exact DartSemantics.HeadStep.seq
    | exact DartSemantics.HeadStep.nullCheckNull
    | (refine DartSemantics.HeadStep.nullCheck ?_; intro h; cases h)
    | exact DartSemantics.HeadStep.condTrue
    | exact DartSemantics.HeadStep.condFalse
    | exact DartSemantics.HeadStep.bubbleException (Ki := .nullCheck)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .as _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .is _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .cond _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .propertyGet _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .seq _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .variableSetAt _ _)
    | exact DartSemantics.HeadStep.ret
    | exact DartSemantics.HeadStep.frameReturning
    | exact DartSemantics.HeadStep.frameVal
    | exact DartSemantics.HeadStep.checkPass rfl
    | exact DartSemantics.HeadStep.checkFail rfl
    | exact DartSemantics.HeadStep.checkEqPass rfl
    | exact DartSemantics.HeadStep.checkEqFail rfl
    | exact DartSemantics.HeadStep.bubbleException (Ki := .ret)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .frame _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .check _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .checkEqL _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .checkEqR _)
    | exact DartSemantics.HeadStep.bubbleException_call rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .nullCheck) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .as _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .is _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .cond _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .propertyGet _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .seq _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .variableSetAt _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .ret) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .check _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .checkEqL _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .checkEqR _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn_call rfl
    | exact DartSemantics.HeadStep.labeledVal
    | exact DartSemantics.HeadStep.labeledBreak
    | exact DartSemantics.HeadStep.brk
    | exact DartSemantics.HeadStep.intBin rfl
    | exact DartSemantics.HeadStep.intNeg rfl
    | exact DartSemantics.HeadStep.primEq rfl
    | exact DartSemantics.HeadStep.bubbleException (Ki := .labeled _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .intBinL _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .intBinR _ _ _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .intNeg _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .primEqL _)
    | exact DartSemantics.HeadStep.bubbleException (Ki := .primEqR _)
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .labeled _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .intBinL _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .intBinR _ _ _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .intNeg _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .primEqL _) rfl
    | exact DartSemantics.HeadStep.bubbleReturn (Ki := .primEqR _) rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .nullCheck) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .as _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .is _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .cond _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .propertyGet _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .seq _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .variableSetAt _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .ret) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .check _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .checkEqL _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .checkEqR _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .labeled _) (by decide) rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .intBinL _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .intBinR _ _ _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .intNeg _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .primEqL _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak (Ki := .primEqR _) rfl rfl
    | exact DartSemantics.HeadStep.bubbleBreak_call rfl)

/--
Tidy the goal after a step: reduce `Outcome.toExpr`, `EctxItem.fill`, `framePost`, `labeledPost`
and `loopInvPost`, the list operations that plugging into a call's arguments leaves, and
beta-reduce postconditions.
-/
syntax "dart_wp_tidy" : tactic

macro_rules
  | `(tactic| dart_wp_tidy) =>
    `(tactic| try simp only [DartSemantics.tidy_toExpr_normal,
      DartSemantics.tidy_toExpr_throwing, DartSemantics.tidy_toExpr_returning,
      DartSemantics.tidy_toExpr_breaking,
      DartSemantics.tidy_fill_nullCheck, DartSemantics.tidy_fill_as, DartSemantics.tidy_fill_is,
      DartSemantics.tidy_fill_cond, DartSemantics.tidy_fill_propertyGet,
      DartSemantics.tidy_fill_seq, DartSemantics.tidy_fill_variableSetAt,
      DartSemantics.tidy_fill_call, DartSemantics.tidy_fill_ret, DartSemantics.tidy_fill_frame,
      DartSemantics.tidy_fill_check, DartSemantics.tidy_fill_checkEqL,
      DartSemantics.tidy_fill_checkEqR, DartSemantics.tidy_fill_labeled,
      DartSemantics.tidy_fill_intBinL, DartSemantics.tidy_fill_intBinR,
      DartSemantics.tidy_fill_intNeg, DartSemantics.tidy_fill_primEqL,
      DartSemantics.tidy_fill_primEqR, DartSemantics.framePost, DartSemantics.labeledPost,
      DartSemantics.loopInvPost, ite_true, ite_false, ↓reduceIte, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append])

/--
When the expression has completed, replace its weakest precondition with the postcondition applied
to its outcome.
-/
syntax "wp_value" : tactic

macro_rules
  | `(tactic| wp_value) => `(tactic|
    ((first
      | refine DartSemantics.tac_wp_val ?_
      | refine DartSemantics.tac_wp_throwing ?_
      | refine DartSemantics.tac_wp_returning ?_
      | refine DartSemantics.tac_wp_breaking ?_); dart_wp_tidy))

/-- Take one head step that doesn't depend on, or change, the state. -/
syntax "wp_pure" : tactic

macro_rules
  | `(tactic| wp_pure) => `(tactic|
    (apply DartSemantics.tac_wp_pure
     · rfl
     · intro _
       dart_pure_head_step
     inext
     dart_wp_tidy))

/-- Focus on the subexpression in evaluation position, if it hasn't completed. -/
syntax "wp_bind" : tactic

macro_rules
  | `(tactic| wp_bind) => `(tactic|
    ((first
      | refine DartSemantics.tac_wp_bind .nullCheck (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.as _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.is _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.cond _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.propertyGet _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.seq _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.variableSetAt _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind .ret (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.frame _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.check _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.checkEqL _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.checkEqR _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.labeled _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.intBinL _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.intBinR _ _ _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.intNeg _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.primEqL _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind (.primEqR _) (by rfl) ?_
      | refine DartSemantics.tac_wp_bind_call (by rfl) (by rfl) ?_); dart_wp_tidy))

/--
Take every step that doesn't involve the state: repeat `wp_value`, `wp_pure` and `wp_bind` until
none applies.
-/
syntax "wp_pures" : tactic

macro_rules
  | `(tactic| wp_pures) =>
    `(tactic| (dart_wp_tidy; repeat (first | wp_value | wp_pure | wp_bind)))

/--
`wp_alloc ℓ H` takes the step of a declaration at the start of a block, introducing the new cell
`ℓ` and its points-to `H`, and resolves the declared variable in the rest of the block.
-/
syntax "wp_alloc " ident ppSpace ident : tactic

macro_rules
  | `(tactic| wp_alloc $l $h) => `(tactic|
    (refine DartSemantics.tac_wp_blockDeclare ?_
     inext
     iintro %$l $h:ident
     simp (config := { decide := true }) only [DartLang.LoweredExpr.resolveBlock,
       DartLang.LoweredExpr.resolve, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte]))

/-- Prove that a value has a dynamic type: the null object, a boolean, an integer, an object whose
header (a persistent points-to for its own cell) is in the context, or a value with a
`HasDynamicType` hypothesis in the context. -/
syntax "dart_dynamic_type" : tactic

macro_rules
  | `(tactic| dart_dynamic_type) => `(tactic| first
    | iapply DartSemantics.HasDynamicType.null
    | iapply DartSemantics.HasDynamicType.bool
    | iapply DartSemantics.HasDynamicType.int
    | (iapply DartSemantics.HasDynamicType.obj; iassumption)
    | iassumption)

/--
Prove a pure side condition of a load: a subtype fact, or the lookup of an instance variable. If
neither `decide` nor `rfl` proves it (for example, a subtype fact about types that aren't concrete),
it's left as a goal, after the remaining goals.
-/
syntax "dart_load_side_condition" : tactic

macro_rules
  | `(tactic| dart_load_side_condition) =>
    `(tactic| (ipureintro; first | decide | rfl | rotate_left))

/--
`wp_load H` takes the step of reading a variable, or an instance variable of an object, using the
points-to `H` for the cell read. The value's dynamic type comes from `dart_dynamic_type`, and the
pure side conditions (the subtype fact needed for the promotion check, and for an instance
variable, its lookup) from `dart_load_side_condition`; any it can't prove are left as goals after
the main one. Afterwards, `H` is back in the context.
-/
syntax "wp_load " ident : tactic

macro_rules
  | `(tactic| wp_load $h) => `(tactic|
    (first
      | (apply DartSemantics.tac_wp_load
         iframe $h:ident
         isplitr
         · dart_dynamic_type
         isplitr
         dart_load_side_condition)
      | (apply DartSemantics.tac_wp_load_field
         iframe $h:ident
         isplitr
         · iassumption
         isplitr
         dart_load_side_condition
         isplitr
         · dart_dynamic_type
         isplitr
         dart_load_side_condition)
     inext
     iintro $h:ident
     dart_wp_tidy))

/--
`wp_store H` takes the step of an assignment to a local variable, using the points-to `H` for the
variable's cell. Afterwards, `H` is back in the context, saying that the cell holds the value
assigned. The side condition for `final` variables (`hfin` of `wp_variableSetAt`) is proved when
the variable isn't `final` or the cell is `.uninit`, and otherwise left as a goal after the main
one.
-/
syntax "wp_store " ident : tactic

macro_rules
  | `(tactic| wp_store $h) => `(tactic|
    (apply DartSemantics.tac_wp_store
     iframe $h:ident
     rotate_left
     · intro _ _ _ h
       cases h
     first
       | (· intro h
            cases h)
       | (· intro _
            rfl)
       | rotate_left
     inext
     iintro $h:ident
     dart_wp_tidy))

/--
`wp_call hf` takes the step of a call of top-level function `f` whose arguments are all values,
using `hf : P.functions f = some d` (the function table's declaration of `f`). The number of
arguments is checked by `rfl`. Afterwards, the goal is `wp_call`'s premise without its `▷`: for
all locations `ℓs`, given the cells of the formal parameters (`PointsToVals ℓs vs`), the body
satisfies the postcondition.
-/
syntax "wp_call " term : tactic

macro_rules
  | `(tactic| wp_call $hf) => `(tactic|
    (refine DartSemantics.tac_wp_call (by rfl) $hf (by rfl) ?_
     inext))

/--
`wp_call_spec H` takes a call of a top-level function `f` whose arguments are all values, using
the specification `H : FunSpec f Pre Post` in the context. Afterwards, the goal is the
precondition, and that the postcondition implies the goal's postcondition
(`Pre vs ∗ ∀ o, Post vs o -∗ Φ o`).
-/
syntax "wp_call_spec " ident : tactic

macro_rules
  | `(tactic| wp_call_spec $h) => `(tactic|
    (apply DartSemantics.tac_wp_call_spec (by rfl)
     isplitr
     · iexact $h:ident))

/--
`wp_loop_step` takes the step of a loop that runs its body once, and then the loop again (which
`wp_pures` doesn't take; see `dart_pure_head_step`).
-/
syntax "wp_loop_step" : tactic

macro_rules
  | `(tactic| wp_loop_step) => `(tactic|
    (refine DartSemantics.tac_wp_pure rfl (fun _ => DartSemantics.HeadStep.loop) ?_
     inext))

/--
`wp_int_checked` takes the step of an arithmetic operator on integers in mode `checked` whose
result `rfl` can't compute (because its operands aren't concrete numbers, say): it leaves the goal
that the exact result is in 64-bit range, and then the main goal, with the result.
-/
syntax "wp_int_checked" : tactic

macro_rules
  | `(tactic| wp_int_checked) => `(tactic|
    (apply DartSemantics.tac_wp_intBin_checked
     · rfl
     rotate_left
     inext
     dart_wp_tidy
     rotate_right))

/--
Bind the formal parameters of a function's body to their cells, after `wp_call` or in a proof of
`FunSpec.intro`'s premise, once the list of locations is concrete: compute
`(body.withIntMode mode).bindVariables (params.zip ℓs)`, setting the mode of each integer operator
in the body and resolving each parameter in the body to its cell.
-/
syntax "dart_bind_params" : tactic

macro_rules
  | `(tactic| dart_bind_params) => `(tactic|
    simp (config := { decide := true }) only [List.zip_cons_cons, List.zip_nil_left,
      List.zip_nil_right, DartLang.LoweredExpr.bindVariables, List.foldl_cons, List.foldl_nil,
      DartLang.LoweredExpr.withIntMode, DartLang.LoweredExpr.withIntModeList,
      DartLang.LoweredExpr.resolve, DartLang.LoweredExpr.resolveBlock,
      DartLang.LoweredExpr.resolveList, ite_true, ite_false, Bool.false_eq_true, ↓reduceIte])
