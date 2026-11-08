module
public import DartSemantics.GhostState
public import Iris.ProgramLogic.EctxLifting
-- iris-lean's `EctxLifting.lean` doesn't put its lemmas in a `public section`, so under the module
-- system they're private to that module. `import all` makes them visible here.
import all Iris.ProgramLogic.EctxLifting

/-!
# Primitive laws of the program logic

One weakest-precondition law for each head-step rule (`HeadStep`), plus bind. Each law is stated
for every choice of `SemanticParams`. For calls, there are also specifications of functions
(`FunSpec`, a Texan triple for every call of a function): a law for using one (`FunSpec.wp_call`),
and one for proving one by Löb induction (`FunSpec.intro`), which works for recursive functions. A
function's body runs as the body of a running call (`frame`), and a weakest precondition's
postcondition, a predicate on outcomes, says what holds if the body returns
(`Outcome.returning`); `wp_frame` turns that into the call's outcome. A loop is reasoned about
with an invariant (`wp_loop_inv`), which packages the Löb induction that a loop needs.

Run-time subtype checks and promotion checks need the dynamic type of a value. For the null object
and booleans it's fixed; for an object it's recorded in the object's own cell, which never changes.
`HasDynamicType v S` is the persistent knowledge that `v`'s dynamic type is `S`.

Each law has the form `P ⊢ WP e @ s; E {{ Φ }}`, which reads like a Hoare triple: to show that `e`
runs safely and its outcome satisfies the postcondition `Φ`, it suffices to have `P`. `P` usually
includes `▷` (later) applied to what the step leads to, since each step of the program removes one
`▷`. The laws are stated for every stuckness `s` and mask `E`, which the proofs here don't
constrain. See the README's "Reading the Iris parts" section for the notation.
-/

namespace DartSemantics

open DartLang Iris Iris.BI Iris.ProgramLogic Iris.Std

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)
local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "EctxItem" => EctxItem (τ := τ)
local notation "Outcome" => Outcome (τ := τ)
local notation "Cell" => Cell (τ := τ)
local notation "State" => State (τ := τ)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]

/-- The persistent knowledge that the dynamic type of value `v` is `S`. -/
@[expose]
public def HasDynamicType (v : Value) (S : τ) : IProp GF :=
  match v with
  | .null => iprop(⌜S = Γ.Null⌝)
  | .bool _ => iprop(⌜S = Γ.bool⌝)
  | .int _ => iprop(⌜S = Γ.int⌝)
  | .obj ℓ => iprop(∃ k fs, ℓ ↦{.discard} (.object k S fs : Cell))
  | .error _ => iprop(False)
  | .cont _ => iprop(False)

/--
`HasDynamicType v S` is persistent: it's a pure fact, a persistent points-to, or `False`, depending
on `v`.
-/
public instance HasDynamicType_persistent (v : Value) (S : τ) :
    Persistent (HasDynamicType (GF := GF) v S) := by
  cases v <;> simp only [HasDynamicType] <;> infer_instance

/-- The dynamic type of the null object is `Null`. -/
public theorem HasDynamicType.null : ⊢ HasDynamicType (GF := GF) (.null : Value) Γ.Null := by
  simp only [HasDynamicType]
  ipureintro
  trivial

/-- The dynamic type of a boolean is `bool`. -/
public theorem HasDynamicType.bool (b : Bool) :
    ⊢ HasDynamicType (GF := GF) (.bool b : Value) Γ.bool := by
  simp only [HasDynamicType]
  ipureintro
  trivial

/-- The dynamic type of an integer is `int`. -/
public theorem HasDynamicType.int (n : Int) :
    ⊢ HasDynamicType (GF := GF) (.int n : Value) Γ.int := by
  simp only [HasDynamicType]
  ipureintro
  trivial

/--
The dynamic type of an object is recorded in the object's own cell: a persistent points-to for the
cell, recording dynamic type `S` (`ℓ ↦{.discard} (.object k S fs)`), says that the dynamic type of
`.obj ℓ` is `S`.
-/
public theorem HasDynamicType.obj {ℓ : Loc} {k : String} {S : τ} {fs : List (String × Loc)} :
    ℓ ↦{.discard} (.object k S fs : Cell) ⊢ HasDynamicType (GF := GF) (.obj ℓ : Value) S := by
  simp only [HasDynamicType]
  iintro H
  iexists k, fs
  iexact H

/--
The ghost heap agrees with what `HasDynamicType` says: given the ghost heap's interpretation of the
state (`genHeapInterp σ.toMap`), if the dynamic type of `v` is `S` according to the logic
(`HasDynamicType v S`), then it's `S` in the state too (`σ.dynamicType v = some S`).
-/
public theorem HasDynamicType.valid {σ : State} {v : Value} {S : τ} :
    genHeapInterp σ.toMap ∗ HasDynamicType (GF := GF) v S ⊢ |==> ⌜σ.dynamicType v = some S⌝ := by
  cases v with
  | null =>
    simp only [HasDynamicType]
    iintro ⟨-, %h⟩
    imodintro
    ipureintro
    simp [State.dynamicType, h]
  | bool b =>
    simp only [HasDynamicType]
    iintro ⟨-, %h⟩
    imodintro
    ipureintro
    simp [State.dynamicType, h]
  | int n =>
    simp only [HasDynamicType]
    iintro ⟨-, %h⟩
    imodintro
    ipureintro
    simp [State.dynamicType, h]
  | obj ℓ =>
    simp only [HasDynamicType]
    iintro ⟨Hσ, %k, %fs, Hℓ⟩
    imod genHeap_valid $$ [$Hσ $Hℓ] with %h
    imodintro
    ipureintro
    rw [State.get?_toMap] at h
    simp [State.dynamicType, h]
  | error e =>
    simp only [HasDynamicType]
    iintro ⟨-, %h⟩
    exact h.elim
  | cont k =>
    simp only [HasDynamicType]
    iintro ⟨-, %h⟩
    exact h.elim

/--
The object headers in the state interpretation (`ObjectHeaders σ`) give the dynamic type `S` of any
value `v` whose dynamic type in the state is `S` (`h`).
-/
public theorem HasDynamicType.of_headers {σ : State} {v : Value} {S : τ}
    (h : σ.dynamicType v = some S) : ObjectHeaders (GF := GF) σ ⊢ HasDynamicType v S := by
  cases v with
  | null =>
    simp only [State.dynamicType, Option.some.injEq] at h
    subst h
    simp only [HasDynamicType]
    iintro -
    ipureintro
    trivial
  | bool b =>
    simp only [State.dynamicType, Option.some.injEq] at h
    subst h
    simp only [HasDynamicType]
    iintro -
    ipureintro
    trivial
  | int n =>
    simp only [State.dynamicType, Option.some.injEq] at h
    subst h
    simp only [HasDynamicType]
    iintro -
    ipureintro
    trivial
  | obj ℓ =>
    simp only [State.dynamicType] at h
    split at h
    · rename_i k C fs hℓ
      simp only [Option.some.injEq] at h
      subst h
      have hl : ObjectHeaders (GF := GF) σ ⊢ ℓ ↦{.discard} (.object k C fs : Cell) :=
        (BigSepM.bigSepM_lookup (Φ := fun ℓ c => cellHeader (GF := GF) ℓ c)
          (by rw [State.get?_toMap]; exact hℓ)).trans (by simp only [cellHeader]; exact .rfl)
      simp only [HasDynamicType]
      iintro H
      iexists k, fs
      iapply hl $$ H
    · cases h
  | error e => cases h
  | cont k => cases h

omit Γ in
/-- A cell `c` that isn't an object's own cell (`hc`) has no header (`cellHeader ℓ c ⊣⊢ emp`). -/
theorem cellHeader_of_ne_object {ℓ : Loc} {c : Cell} (hc : ∀ k C fs, c ≠ .object k C fs) :
    cellHeader (GF := GF) ℓ c ⊣⊢ emp := by
  cases c with
  | object k C fs => exact absurd rfl (hc k C fs)
  | _ => exact .rfl

omit Γ in
/--
Allocating a cell `c` that isn't an object's own cell (`hc`) leaves the object headers as they were
(`ObjectHeaders σ ⊢ ObjectHeaders (σ.alloc c)`).
-/
public theorem ObjectHeaders.alloc {σ : State} {c : Cell} (hc : ∀ k C fs, c ≠ .object k C fs) :
    ObjectHeaders (GF := GF) σ ⊢ ObjectHeaders (σ.alloc c) := by
  simp only [ObjectHeaders, State.toMap_alloc]
  refine .trans ?_ (BigSepM.bigSepM_insert (by rw [State.get?_toMap, State.lookup_fresh])).2
  exact emp_sep.2.trans (sep_mono_left (cellHeader_of_ne_object hc).2)

omit Γ in
/--
Updating the cell at `ℓ` leaves the object headers as they were
(`ObjectHeaders σ ⊢ ObjectHeaders (σ.update ℓ c)`), if:
- the cell holds `c₀` (`h`), which isn't an object's own cell (`hc₀`); and
- the new contents `c` aren't an object's own cell either (`hc`).
-/
public theorem ObjectHeaders.update {σ : State} {ℓ : Loc} {c₀ c : Cell}
    (h : σ.lookup ℓ = some c₀) (hc₀ : ∀ k C fs, c₀ ≠ .object k C fs)
    (hc : ∀ k C fs, c ≠ .object k C fs) :
    ObjectHeaders (GF := GF) σ ⊢ ObjectHeaders (σ.update ℓ c) := by
  simp only [ObjectHeaders, State.toMap_update h]
  refine (BigSepM.bigSepM_delete (by rw [State.get?_toMap]; exact h)).1.trans ?_
  refine .trans ?_ BigSepM.bigSepM_insert_delete.2
  exact sep_mono_left ((cellHeader_of_ne_object hc₀).1.trans (cellHeader_of_ne_object hc).2)

/--
Ownership of the cells at locations `ℓs`, holding the values `vs`, in order: `ℓ ↦ .val v` for the
cell at each `ℓ` in `ℓs` and the value `v` in the same position in `vs`. If the lists have
different lengths, it's `False`. (A call gives this for the cells of its formal parameters,
holding their arguments; see `wp_call`.)
-/
@[expose]
public def PointsToVals : List Loc → List Value → IProp GF
  | [], [] => iprop(emp)
  | ℓ :: ℓs, v :: vs => iprop(ℓ ↦ (.val v : Cell) ∗ PointsToVals ℓs vs)
  | _, _ => iprop(False)

end

/-! ## Laws -/

section Laws

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF] [P : SemanticParams τ]
-- (The type of `Φ` is spelled out because a local notation such as `Outcome` doesn't work in a
-- `variable` binder: Lean silently elaborates the notation's `τ` to `sorry`, which the theorems
-- below would then be stated with. Only the "declaration uses `sorry`" warning, an error in this
-- library, would show it.)
variable {s : Stuckness} {E : CoPset} {Φ : DartLang.Outcome (τ := τ) → IProp GF}

-- The weakest precondition depends on `hlc` only through instances, so it must be included
-- explicitly.
include hlc

/--
An expression that has completed normally with `v` satisfies a postcondition `Φ` that holds of its
value (`Φ (.normal v)`).
-/
public theorem wp_val (v : Value) : Φ (.normal v) ⊢ WP (LoweredExpr.val v) @ s; E {{ Φ }} :=
  wp_value' (v := Outcome.normal v)

/--
An expression that has thrown `v` satisfies a postcondition `Φ` that holds of its exception
(`Φ (.throwing v)`).
-/
public theorem wp_throwing (v : Value) :
    Φ (.throwing v) ⊢ WP (LoweredExpr.throwing v) @ s; E {{ Φ }} :=
  wp_value' (v := Outcome.throwing v)

/--
Bind, for one evaluation context item: `Ki.fill e` satisfies a postcondition `Φ`
(`WP (Ki.fill e) @ s; E {{ Φ }}`), if `e` satisfies the postcondition that plugging its outcome
`o` back into `Ki` satisfies `Φ` (`WP (Ki.fill o.toExpr) @ s; E {{ Φ }}`).
-/
public theorem wp_bind_item (Ki : EctxItem) {e : LoweredExpr} :
    WP e @ s; E {{ o, WP (Ki.fill o.toExpr) @ s; E {{ Φ }} }} ⊢ WP (Ki.fill e) @ s; E {{ Φ }} :=
  wp_bind (Expr := LoweredExpr) (EvContext.fill [Ki])

/--
`e₁` satisfies a postcondition `Φ` if `e₂` does, one step later (`▷ WP e₂ {{ Φ }}`), provided:
- `e₁` hasn't completed (`hv`); and
- in every state, `e₁` takes a head step to `e₂` that leaves the state unchanged (`h`).
-/
public theorem wp_pure_step {e₁ e₂ : LoweredExpr} (hv : e₁.toOutcome? = none)
    (h : ∀ σ, HeadStep e₁ σ e₂ σ) : ▷ WP e₂ @ s; E {{ Φ }} ⊢ WP e₁ @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_lift_pure_det_base_step_no_fork' (e₂ := e₂) hv ?_ ?_)
  · iintro H
    inext
    iintro -
    iexact H
  · intro σ
    exact ⟨[], e₂, σ, [], h σ, rfl, rfl⟩
  · rintro σ₁ obs e₂' σ₂ eₜ' ⟨hs, hobs, hefs⟩
    obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs (h σ₁)
    exact ⟨hobs, rfl, rfl, hefs⟩

/--
`e` satisfies a postcondition `Φ` if the dynamic type of `v` is `S` (`HasDynamicType v S`) and `e'`
satisfies `Φ` one step later (`▷ WP e' {{ Φ }}`), provided:
- `e` hasn't completed (`hv`); and
- in every state where the dynamic type of `v` is `S`, `e` takes a head step to `e'` that leaves
  the state unchanged (`h`).
-/
public theorem wp_step_of_dynamicType {e e' : LoweredExpr} {v : Value} {S : τ}
    (hv : e.toOutcome? = none) (h : ∀ σ, σ.dynamicType v = some S → HeadStep e σ e' σ) :
    HasDynamicType v S ∗ ▷ WP e' @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Φ }} := by
  iintro ⟨#Hty, H⟩
  iapply wp_lift_base_step hv
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr⟩
  ihave %Hdt : ⌜σ₁.dynamicType v = some S⌝ $$ [Hh Hty]
  · ihave >%Hd := HasDynamicType.valid $$ [$Hh $Hty]
    ipureintro
    exact Hd
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], e', σ₁, [], h σ₁ Hdt, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs (h σ₁ Hdt)
  imod Hclose
  imodintro
  isplitl [Hh]
  · iframe Hh
    iexact Hhdr
  isplitl
  · iexact H
  · isimp
    itrivial

/--
`e` satisfies a postcondition `Φ` that holds, one step later, of completing normally with `v`
(`▷ Φ (.normal v)`), provided:
- `e` hasn't completed (`hv`); and
- in every state, `e` takes a head step to the value `v` that leaves the state unchanged (`h`).
-/
public theorem wp_pure_step_val {e : LoweredExpr} {v : Value} (hv : e.toOutcome? = none)
    (h : ∀ σ, HeadStep e σ (.val v) σ) : ▷ Φ (.normal v) ⊢ WP e @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_pure_step hv h)
  exact later_mono (wp_val v)

/--
`e` satisfies a postcondition `Φ` that holds, one step later, of throwing `v`
(`▷ Φ (.throwing v)`), provided:
- `e` hasn't completed (`hv`); and
- in every state, `e` takes a head step to throwing `v` that leaves the state unchanged (`h`).
-/
public theorem wp_pure_step_throwing {e : LoweredExpr} {v : Value} (hv : e.toOutcome? = none)
    (h : ∀ σ, HeadStep e σ (.throwing v) σ) : ▷ Φ (.throwing v) ⊢ WP e @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_pure_step hv h)
  exact later_mono (wp_throwing v)

/--
The null literal evaluates to the null object: it satisfies a postcondition `Φ` that holds, one step
later, of completing normally with the null object (`▷ Φ (.normal .null)`).
-/
public theorem wp_null : ▷ Φ (.normal .null) ⊢ WP (LoweredExpr.null (τ := τ)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .null

/--
A boolean literal evaluates to its boolean: it satisfies a postcondition `Φ` that holds, one step
later, of completing normally with that boolean (`▷ Φ (.normal (.bool b))`).
-/
public theorem wp_bool {b : Bool} :
    ▷ Φ (.normal (.bool b)) ⊢ WP (LoweredExpr.bool (τ := τ) b) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .bool

/--
An integer literal evaluates to its integer: it satisfies a postcondition `Φ` that holds, one step
later, of completing normally with that integer (`▷ Φ (.normal (.int n))`).
-/
public theorem wp_int {n : Int} :
    ▷ Φ (.normal (.int n)) ⊢ WP (LoweredExpr.int (τ := τ) n) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .int

/--
A declaration outside a block is converted to a block containing just that declaration: it
satisfies a postcondition `Φ` if that block does, one step later
(`▷ WP (LoweredExpr.block [.declare v T startsNull]) {{ Φ }}`).
-/
public theorem wp_declare {v : Variable} {T : τ} {startsNull : Bool} :
    ▷ WP (LoweredExpr.block [.declare v T startsNull]) @ s; E {{ Φ }} ⊢
      WP (LoweredExpr.declare v T startsNull) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .declare

/--
An empty block completes normally, with the null object: it satisfies a postcondition `Φ` that
holds, one step later, of completing normally with the null object (`▷ Φ (.normal .null)`).
-/
public theorem wp_blockNil :
    ▷ Φ (.normal .null) ⊢ WP (LoweredExpr.block (τ := τ) []) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .blockNil

/--
A block that starts with anything other than a declaration (`h`) runs it, then the rest: it
satisfies a postcondition `Φ` if the sequence of the two does, one step later
(`▷ WP (LoweredExpr.seq m (.block ms)) {{ Φ }}`).
-/
public theorem wp_blockCons {m : LoweredExpr} {ms : List LoweredExpr}
    (h : ∀ v T startsNull, m ≠ .declare v T startsNull) :
    ▷ WP (LoweredExpr.seq m (.block ms)) @ s; E {{ Φ }} ⊢
      WP (LoweredExpr.block (m :: ms)) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .blockCons h

/--
Once the first part of a sequence completes normally, the second part `m` runs: the sequence
satisfies a postcondition `Φ` if `m` does, one step later (`▷ WP m {{ Φ }}`).
-/
public theorem wp_seq {v : Value} {m : LoweredExpr} :
    ▷ WP m @ s; E {{ Φ }} ⊢ WP (LoweredExpr.seq (.val v) m) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .seq

/--
A null check on the null object throws: it satisfies a postcondition `Φ` that holds, one step
later, of throwing a type error (`▷ Φ (.throwing (.error .typeError))`).
-/
public theorem wp_nullCheck_null :
    ▷ Φ (.throwing (.error .typeError)) ⊢
      WP (LoweredExpr.nullCheck (τ := τ) (.val .null)) @ s; E {{ Φ }} := by
  refine wp_pure_step_throwing (by rfl) fun _ => ?_
  exact .nullCheckNull

/--
A null check on any other object (`h`) evaluates to it: it satisfies a postcondition `Φ` that
holds, one step later, of completing normally with that object (`▷ Φ (.normal v)`).
-/
public theorem wp_nullCheck {v : Value} (h : v ≠ .null) :
    ▷ Φ (.normal v) ⊢ WP (LoweredExpr.nullCheck (.val v)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .nullCheck h

/--
A conditional whose condition is `true` runs its first branch: it satisfies a postcondition `Φ` if
the first branch does, one step later (`▷ WP m₂ {{ Φ }}`).
-/
public theorem wp_cond_true {m₂ m₃ : LoweredExpr} {T : τ} :
    ▷ WP m₂ @ s; E {{ Φ }} ⊢ WP (LoweredExpr.cond (.val (.bool true)) m₂ m₃ T) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .condTrue

/--
A conditional whose condition is `false` runs its second branch: it satisfies a postcondition `Φ`
if the second branch does, one step later (`▷ WP m₃ {{ Φ }}`).
-/
public theorem wp_cond_false {m₂ m₃ : LoweredExpr} {T : τ} :
    ▷ WP m₃ @ s; E {{ Φ }} ⊢ WP (LoweredExpr.cond (.val (.bool false)) m₂ m₃ T) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .condFalse

/--
An exception `v` propagates out of an evaluation context item `Ki`: `Ki.fill (.throwing v)`
satisfies a postcondition `Φ` that holds, one step later, of throwing `v` (`▷ Φ (.throwing v)`).
-/
public theorem wp_bubble_exception (Ki : EctxItem) (v : Value) :
    ▷ Φ (.throwing v) ⊢ WP (Ki.fill (.throwing v)) @ s; E {{ Φ }} := by
  refine wp_pure_step_throwing (EctxItem.toOutcome?_fill _ _) fun _ => ?_
  exact .bubbleException

/--
A return of `v` propagates out of an evaluation context item `Ki` that doesn't handle returns
(`hKi`: anything but the body of a running call): `Ki.fill (.returning v)` satisfies a
postcondition `Φ` that holds, one step later, of returning `v` (`▷ Φ (.returning v)`).
-/
public theorem wp_bubble_return {Ki : EctxItem} (hKi : Ki.handlesReturn = false) (v : Value) :
    ▷ Φ (.returning v) ⊢ WP (Ki.fill (.returning v)) @ s; E {{ Φ }} := by
  refine (later_mono (wp_value' (v := Outcome.returning v))).trans
    (wp_pure_step (EctxItem.toOutcome?_fill _ _) fun _ => ?_)
  exact .bubbleReturn hKi

/--
A break out of labeled statement `l` propagates out of an evaluation context item `Ki` that
doesn't handle it (`hKi`: anything but the labeled statement `l`), and isn't the body of a running
call (`hret`): `Ki.fill (.breaking l)` satisfies a postcondition `Φ` that holds, one step later, of
breaking out of `l` (`▷ Φ (.breaking l)`).
-/
public theorem wp_bubble_break {Ki : EctxItem} {l : String} (hKi : Ki.handlesBreak l = false)
    (hret : Ki.handlesReturn = false) :
    ▷ Φ (.breaking l) ⊢ WP (Ki.fill (.breaking l)) @ s; E {{ Φ }} := by
  refine (later_mono (wp_value' (v := Outcome.breaking l))).trans
    (wp_pure_step (EctxItem.toOutcome?_fill _ _) fun _ => ?_)
  exact .bubbleBreak hKi hret

/--
A cast `v as T` whose check answers yes evaluates to its operand: if the dynamic type of `v` is `S`
(`HasDynamicType v S`), and the run-time check of whether `S` is a subtype of `T` answers yes
(`h`), the cast satisfies a postcondition `Φ` that holds, one step later, of completing normally
with `v` (`▷ Φ (.normal v)`).
-/
public theorem wp_as_true {v : Value} {S T : τ} (h : RtSub S T true) :
    HasDynamicType v S ∗ ▷ Φ (.normal v) ⊢ WP (LoweredExpr.as (.val v) T) @ s; E {{ Φ }} := by
  refine (sep_mono_right (later_mono (wp_val _))).trans
    (wp_step_of_dynamicType (by rfl) fun _ hS => ?_)
  exact .asTrue hS h

/--
A cast `v as T` whose check answers no throws: if the dynamic type of `v` is `S`
(`HasDynamicType v S`), and the run-time check of whether `S` is a subtype of `T` answers no
(`h`), the cast satisfies a postcondition `Φ` that holds, one step later, of throwing a type error
(`▷ Φ (.throwing (.error .typeError))`).
-/
public theorem wp_as_false {v : Value} {S T : τ} (h : RtSub S T false) :
    HasDynamicType v S ∗ ▷ Φ (.throwing (.error .typeError)) ⊢
      WP (LoweredExpr.as (.val v) T) @ s; E {{ Φ }} := by
  refine (sep_mono_right (later_mono (wp_throwing _))).trans
    (wp_step_of_dynamicType (by rfl) fun _ hS => ?_)
  exact .asFalse hS h

/--
An is-expression `v is T` evaluates to the answer of its check: if the dynamic type of `v` is `S`
(`HasDynamicType v S`), and the run-time check of whether `S` is a subtype of `T` answers `b`
(`h`), the is-expression satisfies a postcondition `Φ` that holds, one step later, of completing
normally with `b` (`▷ Φ (.normal (.bool b))`).
-/
public theorem wp_is {v : Value} {S T : τ} {b : Bool} (h : RtSub S T b) :
    HasDynamicType v S ∗ ▷ Φ (.normal (.bool b)) ⊢
      WP (LoweredExpr.is (.val v) T) @ s; E {{ Φ }} := by
  refine (sep_mono_right (later_mono (wp_val _))).trans
    (wp_step_of_dynamicType (by rfl) fun _ hS => ?_)
  exact .is hS h

/--
A cast `v as T` whose check doesn't terminate doesn't terminate either, so it satisfies every
postcondition `Φ`. The check doesn't terminate if the dynamic type of `v` is `S`
(`HasDynamicType v S`) and the run-time check of whether `S` is a subtype of `T` gives no answer
(`h`).
-/
public theorem wp_as_diverge {v : Value} {S T : τ} (h : ∀ b, ¬ RtSub S T b) :
    HasDynamicType v S ⊢ WP (LoweredExpr.as (.val v) T) @ s; E {{ Φ }} := by
  have hstep : ∀ σ, σ.dynamicType v = some S →
      HeadStep (LoweredExpr.as (.val v) T) σ (LoweredExpr.as (.val v) T) σ :=
    fun _ hS => .asDiverge hS h
  iintro #Hty
  iloeb as IH
  iapply wp_step_of_dynamicType rfl hstep
  isplitl
  · iexact Hty
  · iexact IH

/--
An is-expression `v is T` whose check doesn't terminate doesn't terminate either, so it satisfies
every postcondition `Φ`. The check doesn't terminate if the dynamic type of `v` is `S`
(`HasDynamicType v S`) and the run-time check of whether `S` is a subtype of `T` gives no answer
(`h`).
-/
public theorem wp_is_diverge {v : Value} {S T : τ} (h : ∀ b, ¬ RtSub S T b) :
    HasDynamicType v S ⊢ WP (LoweredExpr.is (.val v) T) @ s; E {{ Φ }} := by
  have hstep : ∀ σ, σ.dynamicType v = some S →
      HeadStep (LoweredExpr.is (.val v) T) σ (LoweredExpr.is (.val v) T) σ :=
    fun _ hS => .isDiverge hS h
  iintro #Hty
  iloeb as IH
  iapply wp_step_of_dynamicType rfl hstep
  isplitl
  · iexact Hty
  · iexact IH

/--
A block that starts with a declaration of `v` allocates a cell for `v`, holding the null object or
uninitialized as the declaration says, and runs the rest of the block with `v` resolved to it: the
block satisfies a postcondition `Φ` if, one step later (`▷`), for every location `ℓ`, given the
ownership of a cell at `ℓ` holding the initial contents
(`ℓ ↦ (if startsNull then .val .null else .uninit)`), the rest of the block, with `v` resolved to
`ℓ`, satisfies `Φ` (`WP (LoweredExpr.block (LoweredExpr.resolveBlock v ℓ ms)) {{ Φ }}`).
-/
public theorem wp_blockDeclare {v : Variable} {T : τ} {startsNull : Bool} {ms : List LoweredExpr} :
    ▷ (∀ ℓ, ℓ ↦ (if startsNull then .val .null else .uninit : Cell) -∗
        WP (LoweredExpr.block (LoweredExpr.resolveBlock v ℓ ms)) @ s; E {{ Φ }}) ⊢
      WP (LoweredExpr.block (.declare v T startsNull :: ms)) @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_base_step rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], _, _, [], .blockDeclare, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs .blockDeclare
  imod Hclose
  have hfresh : get? σ₁.toMap σ₁.fresh = none := by rw [State.get?_toMap, State.lookup_fresh]
  imod genHeap_alloc (v := (if startsNull then .val .null else .uninit : Cell)) hfresh $$ Hh
    with ⟨Hh, Hl, -⟩
  have hc : ∀ k C fs, (if startsNull then .val .null else .uninit : Cell) ≠ .object k C fs := by
    cases startsNull <;> nofun
  ihave #Hhdr' := ObjectHeaders.alloc (GF := GF) (σ := σ₁) hc $$ Hhdr
  imodintro
  isplitl [Hh]
  · rw [State.toMap_alloc]
    iframe Hh
    iexact Hhdr'
  isplitl
  · iapply H $$ Hl
  · isimp
    itrivial

/--
Reading a local variable `x`, resolved to the cell at `ℓ`, with (possibly promoted) static type
`T`, gives the value `v` in its cell, provided the value satisfies `T`, so that the promotion check
passes. The read satisfies a postcondition `Φ` if:
- the dynamic type of `v` is `S` (`HasDynamicType v S`), a subtype of `T` (`hST`);
- one step later, the cell at `ℓ` holds `v` (`▷ ℓ ↦{dq} (.val v)`), with any fraction `dq` of its
  ownership; and
- one step later, `Φ` holds of completing normally with `v` (`Φ (.normal v)`), given the ownership
  back (`▷ (ℓ ↦{dq} (.val v) -∗ …)`).
-/
public theorem wp_varAt {x : Variable} {T S : τ} {ℓ : Loc} {dq : DFrac} {v : Value}
    (hST : S ≤ T) :
    HasDynamicType v S ∗ ▷ (ℓ ↦{dq} (.val v : Cell)) ∗
        ▷ ((ℓ ↦{dq} (.val v : Cell)) -∗ Φ (.normal v)) ⊢
      WP (LoweredExpr.varAt x T ℓ) @ s; E {{ Φ }} := by
  iintro ⟨#Hty, >Hl, HΦ⟩
  iapply wp_lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr⟩
  ihave %Hlook : ⌜σ₁.lookup ℓ = some (.val v)⌝ $$ [Hh Hl]
  · ihave >%Hv := genHeap_valid $$ [$Hh $Hl]
    ipureintro
    rwa [State.get?_toMap] at Hv
  ihave %Hdt : ⌜σ₁.dynamicType v = some S⌝ $$ [Hh Hty]
  · ihave >%Hd := HasDynamicType.valid $$ [$Hh $Hty]
    ipureintro
    exact Hd
  have hstep : HeadStep (LoweredExpr.varAt x T ℓ) σ₁ (.val v) σ₁ :=
    .varAt Hlook (.of_le Hdt hST)
  imodintro
  isplit
  · ipureintro
    exact ⟨[], _, _, [], hstep, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs hstep
  imodintro
  isplit
  · itrivial
  isplitl [Hh]
  · iframe Hh
    iexact Hhdr
  iexists .normal v
  isplit
  · ipureintro
    rfl
  · iapply HΦ $$ Hl

/--
An assignment of `w` to a local variable `x`, resolved to the cell at `ℓ`, stores `w` in the cell,
and evaluates to it. It satisfies a postcondition `Φ` if:
- the cell's contents `c` aren't an object's own cell (`hc`): it's a variable's;
- if `x` is `final`, the cell is unassigned (`hfin`);
- one step later, the cell at `ℓ` is owned (`▷ ℓ ↦ c`); and
- one step later, `Φ` holds of completing normally with `w` (`Φ (.normal w)`), given the ownership
  of the cell, now holding `w` (`▷ (ℓ ↦ (.val w) -∗ …)`).
-/
public theorem wp_variableSetAt {x : Variable} {ℓ : Loc} {c : Cell} {w : Value}
    (hc : ∀ k C fs, c ≠ .object k C fs) (hfin : x.isFinal = true → c = .uninit) :
    ▷ (ℓ ↦ c) ∗ ▷ ((ℓ ↦ (.val w : Cell)) -∗ Φ (.normal w)) ⊢
      WP (LoweredExpr.variableSetAt x ℓ (.val w)) @ s; E {{ Φ }} := by
  iintro ⟨>Hl, HΦ⟩
  iapply wp_lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr⟩
  ihave %Hlook : ⌜σ₁.lookup ℓ = some c⌝ $$ [Hh Hl]
  · ihave >%Hv := genHeap_valid $$ [$Hh $Hl]
    ipureintro
    rwa [State.get?_toMap] at Hv
  have hstep : HeadStep (LoweredExpr.variableSetAt x ℓ (.val w)) σ₁ (.val w)
      (σ₁.update ℓ (.val w)) := .variableSetAt Hlook hc hfin
  imodintro
  isplit
  · ipureintro
    exact ⟨[], _, _, [], hstep, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs hstep
  imod genHeap_update (σ := σ₁.toMap) (l := ℓ) (v₁ := c) (v₂ := (.val w : Cell)) $$ [$Hh $Hl]
    with ⟨Hh, Hl⟩
  ihave #Hhdr' := ObjectHeaders.update (c := (.val w : Cell)) Hlook hc (fun _ _ _ h => by cases h)
    $$ Hhdr
  imodintro
  isplit
  · itrivial
  isplitl [Hh]
  · rw [State.toMap_update Hlook]
    iframe Hh
    iexact Hhdr'
  iexists .normal w
  isplit
  · ipureintro
    rfl
  · iapply HΦ $$ Hl

/--
Reading property `p` of an object, with (possibly promoted) static type `T`, gives the value `w` in
the cell of the instance variable that the object's class dispatches `p.name` to, provided `w`
satisfies `T`, so that the promotion check passes. The read satisfies a postcondition `Φ` if:
- the object's own cell, at `ℓ`, records its class `k` and instance variables `fs`
  (`ℓ ↦{.discard} (.object k C fs)`);
- `k` dispatches `p.name` to the implicit getter of the instance variable whose key is `iv`
  (`hd`: `P.dispatch k p.name = some (.field iv)`), which is at `ℓf`
  (`hf`: `fs.lookup iv = some ℓf`);
- the dynamic type of `w` is `S` (`HasDynamicType w S`), a subtype of `T` (`hST`);
- one step later, the cell at `ℓf` holds `w` (`▷ ℓf ↦{dq} (.val w)`), with any fraction `dq` of its
  ownership; and
- one step later, `Φ` holds of completing normally with `w` (`Φ (.normal w)`), given the ownership
  back (`▷ (ℓf ↦{dq} (.val w) -∗ …)`).
-/
public theorem wp_propertyGetField {ℓ ℓf : Loc} {p : Property} {k iv : String} {T C S : τ}
    {fs : List (String × Loc)} {dq : DFrac} {w : Value}
    (hd : P.dispatch k p.name = some (.field iv)) (hf : fs.lookup iv = some ℓf) (hST : S ≤ T) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗ HasDynamicType w S ∗ ▷ (ℓf ↦{dq} (.val w : Cell)) ∗
        ▷ ((ℓf ↦{dq} (.val w : Cell)) -∗ Φ (.normal w)) ⊢
      WP (LoweredExpr.propertyGet (.val (.obj ℓ)) p T) @ s; E {{ Φ }} := by
  iintro ⟨#Hobj, #Hty, >Hl, HΦ⟩
  iapply wp_lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr⟩
  ihave %Hobjl : ⌜σ₁.lookup ℓ = some (.object k C fs)⌝ $$ [Hh Hobj]
  · ihave >%Hv := genHeap_valid $$ [$Hh $Hobj]
    ipureintro
    rwa [State.get?_toMap] at Hv
  ihave %Hlook : ⌜σ₁.lookup ℓf = some (.val w)⌝ $$ [Hh Hl]
  · ihave >%Hv := genHeap_valid $$ [$Hh $Hl]
    ipureintro
    rwa [State.get?_toMap] at Hv
  ihave %Hdt : ⌜σ₁.dynamicType w = some S⌝ $$ [Hh Hty]
  · ihave >%Hd := HasDynamicType.valid $$ [$Hh $Hty]
    ipureintro
    exact Hd
  have hobj : σ₁.object? (.obj ℓ) = some (k, fs) := by simp [State.object?, Hobjl]
  have hstep : HeadStep (LoweredExpr.propertyGet (.val (.obj ℓ)) p T) σ₁ (.val w) σ₁ :=
    .propertyGetField hobj hd hf Hlook (.of_le Hdt hST)
  imodintro
  isplit
  · ipureintro
    exact ⟨[], _, _, [], hstep, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs hstep
  imodintro
  isplit
  · itrivial
  isplitl [Hh]
  · iframe Hh
    iexact Hhdr
  iexists .normal w
  isplit
  · ipureintro
    rfl
  · iapply HΦ $$ Hl

/-! ### Calls, returns and intrinsic checks -/

omit Γ P in
/--
Allocating a cell for each value in `vs` (`σ.allocAll (vs.map Cell.val)`), as a call does for its
formal parameters, can be mirrored in the ghost state: given the state interpretation for `σ`
(`genHeapInterp σ.toMap ∗ ObjectHeaders σ`), a basic update gives the state interpretation for the
state afterwards, and the ownership of the new cells (`PointsToVals … vs`).
-/
public theorem allocAll_vals (σ : State) (vs : List Value) :
    genHeapInterp σ.toMap ∗ ObjectHeaders (GF := GF) σ ⊢
      |==> ((genHeapInterp (σ.allocAll (vs.map Cell.val)).2.toMap ∗
        ObjectHeaders (σ.allocAll (vs.map Cell.val)).2) ∗
        PointsToVals (σ.allocAll (vs.map Cell.val)).1 vs) := by
  induction vs generalizing σ with
  | nil =>
    simp only [List.map_nil, State.allocAll, PointsToVals]
    iintro ⟨Hh, Hhdr⟩
    imodintro
    isplitl
    · isplitl [Hh]
      · iexact Hh
      · iexact Hhdr
    · itrivial
  | cons v vs ih =>
    have hfresh : get? σ.toMap σ.fresh = none := by rw [State.get?_toMap, State.lookup_fresh]
    have ih' := ih (σ.alloc (.val v))
    rw [State.toMap_alloc] at ih'
    simp only [List.map_cons, State.allocAll, PointsToVals]
    iintro ⟨Hh, #Hhdr⟩
    imod genHeap_alloc (v := (.val v : Cell)) hfresh $$ Hh with ⟨Hh, Hl, -⟩
    ihave #Hhdr' := ObjectHeaders.alloc (GF := GF) (σ := σ) (c := .val v)
      (fun _ _ _ h => by cases h) $$ Hhdr
    imod ih' $$ [$Hh $Hhdr'] with ⟨Hrest, Hls⟩
    imodintro
    isplitl [Hrest]
    · iexact Hrest
    · isplitl [Hl]
      · iexact Hl
      · iexact Hls

/--
A return statement whose operand has evaluated to `v` starts returning `v`: it satisfies a
postcondition `Φ` that holds, one step later, of returning `v` (`▷ Φ (.returning v)`).
-/
public theorem wp_ret {v : Value} :
    ▷ Φ (.returning v) ⊢ WP (LoweredExpr.ret (.val v)) @ s; E {{ Φ }} := by
  refine (later_mono (wp_value' (v := Outcome.returning v))).trans
    (wp_pure_step (by rfl) fun _ => ?_)
  exact .ret

/--
When the body of a running call returns `v`, the call completes normally with `v`: it satisfies a
postcondition `Φ` that holds, one step later, of completing normally with `v` (`▷ Φ (.normal v)`).
-/
public theorem wp_frame_returning {v : Value} {T : τ} :
    ▷ Φ (.normal v) ⊢ WP (LoweredExpr.frame (.returning v) T) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .frameReturning

/--
When the body of a running call completes normally (falling off its end), the call completes
normally with the null object: it satisfies a postcondition `Φ` that holds, one step later, of
completing normally with the null object (`▷ Φ (.normal .null)`).
-/
public theorem wp_frame_val {v : Value} {T : τ} :
    ▷ Φ (.normal .null) ⊢ WP (LoweredExpr.frame (.val v) T) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .frameVal

/--
What the body of a running call must guarantee about its outcome `o`, for the call to satisfy a
postcondition `Φ`: that `Φ` holds, one step later, of the call's outcome. A return of `v` becomes
completing normally with `v`, completing normally (falling off the end of the body) becomes
completing normally with the null object, and an exception propagates. A break can't propagate out
of a function's body (it gets stuck there), so the body must not complete with one (`False`).
-/
@[expose, simp]
public def framePost (Φ : DartLang.Outcome (τ := τ) → IProp GF) :
    DartLang.Outcome (τ := τ) → IProp GF
  | .normal _ => iprop(▷ Φ (.normal .null))
  | .returning v => iprop(▷ Φ (.normal v))
  | .throwing v => iprop(▷ Φ (.throwing v))
  | .breaking _ => iprop(False)

/--
The body `m` of a running call: `.frame m T` satisfies a postcondition `Φ` if `m` satisfies the
postcondition that `Φ` holds, one step later, of the call's outcome for each outcome `o` of the
body (`WP m {{ o, framePost Φ o }}`). This turns a return into completing normally (see
`framePost`), so a specification of a function's body can describe its returns with
postconditions on `Outcome.returning`.
-/
public theorem wp_frame {m : LoweredExpr} {T : τ} :
    WP m @ s; E {{ o, framePost Φ o }} ⊢ WP (LoweredExpr.frame m T) @ s; E {{ Φ }} := by
  refine (wp_mono fun o => ?_).trans (wp_bind_item (.frame T))
  cases o with
  | normal v => exact wp_frame_val
  | returning v => exact wp_frame_returning
  | throwing v => exact wp_bubble_exception (.frame T) v
  | breaking l => exact false_elim

/--
A call of a top-level function `f`, whose arguments have evaluated to `vs`, allocates a cell for
each formal parameter, holding its argument, and runs the body. It satisfies a postcondition `Φ` if:
- the function table declares `f` as `d` (`hf`), with one formal parameter per argument (`hlen`);
  and
- one step later (`▷`), for all locations `ℓs`, given the ownership of cells at `ℓs` holding the
  arguments (`PointsToVals ℓs vs`), the body, with every integer operator's mode set to `f`'s
  integer mode and the formal parameters bound to those cells, run as the body of a running call,
  satisfies `Φ`
  (`WP (.frame ((d.body.withIntMode (P.intModeOf f)).bindVariables (d.params.zip ℓs)) T) {{ Φ }}`).

The `▷` is what makes recursive functions provable: a proof of a specification of `f` may assume
the specification under a `▷` (by Löb induction), and this law removes the `▷` before the body
runs, so the body's own calls of `f` can use it. `FunSpec.intro` packages this.
-/
public theorem wp_call {f : String} {d : FunctionDecl (τ := τ)} {vs : List Value} {T : τ}
    (hf : P.functions f = some d) (hlen : d.params.length = vs.length) :
    ▷ (∀ ℓs, PointsToVals ℓs vs -∗
        WP (LoweredExpr.frame ((d.body.withIntMode (P.intModeOf f)).bindVariables
          (d.params.zip ℓs)) T) @ s; E {{ Φ }}) ⊢
      WP (LoweredExpr.call f (vs.map .val) T) @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_base_step rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], _, _, [], .call hf hlen, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs (.call hf hlen)
  imod Hclose
  imod allocAll_vals σ₁ vs $$ Hσ with ⟨Hσ, Hls⟩
  imodintro
  isplitl [Hσ]
  · iexact Hσ
  isplitl
  · iapply H $$ Hls
  · isimp
    itrivial

/--
An intrinsic check that holds of its operand `v` (`h`) completes normally: it satisfies a
postcondition `Φ` that holds, one step later, of completing normally with the null object
(`▷ Φ (.normal .null)`).
-/
public theorem wp_check_pass {kind : CheckKind} {v : Value} (h : kind.holds v = true) :
    ▷ Φ (.normal .null) ⊢ WP (LoweredExpr.check kind (.val v)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .checkPass h

/--
An intrinsic check that doesn't hold of its operand `v` (`h`) throws: it satisfies a postcondition
`Φ` that holds, one step later, of throwing (`▷ Φ (.throwing (.error .expectFailed))`).
-/
public theorem wp_check_fail {kind : CheckKind} {v : Value} (h : kind.holds v = false) :
    ▷ Φ (.throwing (.error .expectFailed)) ⊢
      WP (LoweredExpr.check kind (.val v)) @ s; E {{ Φ }} := by
  refine wp_pure_step_throwing (by rfl) fun _ => ?_
  exact .checkFail h

/--
An intrinsic equality check whose operands `v₁` and `v₂` are equal (`h`) completes normally: it
satisfies a postcondition `Φ` that holds, one step later, of completing normally with the null
object (`▷ Φ (.normal .null)`).
-/
public theorem wp_checkEq_pass {v₁ v₂ : Value} (h : Value.primEq? v₁ v₂ = some true) :
    ▷ Φ (.normal .null) ⊢ WP (LoweredExpr.checkEq (.val v₁) (.val v₂)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .checkEqPass h

/--
An intrinsic equality check whose operands `v₁` and `v₂` are different (`h`) throws: it satisfies
a postcondition `Φ` that holds, one step later, of throwing
(`▷ Φ (.throwing (.error .expectFailed))`).
-/
public theorem wp_checkEq_fail {v₁ v₂ : Value} (h : Value.primEq? v₁ v₂ = some false) :
    ▷ Φ (.throwing (.error .expectFailed)) ⊢
      WP (LoweredExpr.checkEq (.val v₁) (.val v₂)) @ s; E {{ Φ }} := by
  refine wp_pure_step_throwing (by rfl) fun _ => ?_
  exact .checkEqFail h

/-! ### Loops, breaks and integer arithmetic -/

/--
A loop runs its body, and then the loop again: it satisfies a postcondition `Φ` if the sequence of
the two does, one step later (`▷ WP (LoweredExpr.seq m (.loop m)) {{ Φ }}`). (`wp_loop_inv` is
usually more convenient.)
-/
public theorem wp_loop {m : LoweredExpr} :
    ▷ WP (LoweredExpr.seq m (.loop m)) @ s; E {{ Φ }} ⊢ WP (LoweredExpr.loop m) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .loop

/--
A labeled statement whose body has completed normally completes normally too, with the null
object: it satisfies a postcondition `Φ` that holds, one step later, of completing normally with
the null object (`▷ Φ (.normal .null)`).
-/
public theorem wp_labeled_val {l : String} {v : Value} :
    ▷ Φ (.normal .null) ⊢ WP (LoweredExpr.labeled l (.val v)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .labeledVal

/--
A labeled statement `l` whose body has broken out of it completes normally, with the null object:
it satisfies a postcondition `Φ` that holds, one step later, of completing normally with the null
object (`▷ Φ (.normal .null)`).
-/
public theorem wp_labeled_breaking {l : String} :
    ▷ Φ (.normal .null) ⊢ WP (LoweredExpr.labeled (τ := τ) l (.breaking l)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .labeledBreak

/--
A break statement `break l` starts breaking out of the labeled statement `l`: it satisfies a
postcondition `Φ` that holds, one step later, of breaking out of `l` (`▷ Φ (.breaking l)`).
-/
public theorem wp_brk {l : String} :
    ▷ Φ (.breaking l) ⊢ WP (LoweredExpr.brk (τ := τ) l) @ s; E {{ Φ }} := by
  refine (later_mono (wp_value' (v := Outcome.breaking l))).trans
    (wp_pure_step (by rfl) fun _ => ?_)
  exact .brk

/--
What the body of a labeled statement `l` must guarantee about its outcome `o`, for the labeled
statement to satisfy a postcondition `Φ`: that `Φ` holds, one step later, of the labeled
statement's outcome. Completing normally, or breaking out of `l`, becomes completing normally with
the null object; any other outcome (including a break out of another labeled statement)
propagates.
-/
@[expose, simp]
public def labeledPost (l : String) (Φ : DartLang.Outcome (τ := τ) → IProp GF) :
    DartLang.Outcome (τ := τ) → IProp GF
  | .normal _ => iprop(▷ Φ (.normal .null))
  | .throwing v => iprop(▷ Φ (.throwing v))
  | .returning v => iprop(▷ Φ (.returning v))
  | .breaking l' => if l' = l then iprop(▷ Φ (.normal .null)) else iprop(▷ Φ (.breaking l'))

/--
The body `m` of a labeled statement `l`: `.labeled l m` satisfies a postcondition `Φ` if `m`
satisfies the postcondition that `Φ` holds, one step later, of the labeled statement's outcome for
each outcome `o` of the body (`WP m {{ o, labeledPost l Φ o }}`; see `labeledPost`).
-/
public theorem wp_labeled {l : String} {m : LoweredExpr} :
    WP m @ s; E {{ o, labeledPost l Φ o }} ⊢ WP (LoweredExpr.labeled l m) @ s; E {{ Φ }} := by
  refine (wp_mono fun o => ?_).trans (wp_bind_item (.labeled l))
  cases o with
  | normal v => exact wp_labeled_val
  | throwing v => exact wp_bubble_exception (.labeled l) v
  | returning v => exact wp_bubble_return rfl v
  | breaking l' =>
    simp only [labeledPost]
    split
    · next h =>
      subst h
      exact wp_labeled_breaking
    · next h =>
      refine wp_bubble_break ?_ rfl
      simpa [EctxItem.handlesBreak] using Ne.symm h

/--
The postcondition that a loop's body must satisfy, for the loop invariant rule (`wp_loop_inv`):
if the body completes normally, the invariant `I` holds again, one step later (`▷ I`), ready for
the next iteration; if it completes in any other way (by breaking out of a labeled statement, for
example), which ends the loop, the loop's postcondition `Φ` holds of that outcome.
-/
@[expose, simp]
public def loopInvPost (I : IProp GF) (Φ : DartLang.Outcome (τ := τ) → IProp GF) :
    DartLang.Outcome (τ := τ) → IProp GF
  | .normal _ => iprop(▷ I)
  | .throwing v => Φ (.throwing v)
  | .returning v => Φ (.returning v)
  | .breaking l => Φ (.breaking l)

/--
Bind, for the first part of a sequence: `LoweredExpr.seq m₁ m₂` satisfies a postcondition `Φ` if
`m₁` satisfies the postcondition that the sequence of its outcome `o` and `m₂` satisfies `Φ`
(`WP (LoweredExpr.seq o.toExpr m₂) {{ Φ }}`). This is `wp_bind_item` for `EctxItem.seq`, with
`EctxItem.fill` unfolded, so that `iapply` can use it.
-/
public theorem wp_bind_seq {m₁ m₂ : LoweredExpr} :
    WP m₁ @ s; E {{ o, WP (LoweredExpr.seq o.toExpr m₂) @ s; E {{ Φ }} }} ⊢
      WP (LoweredExpr.seq m₁ m₂) @ s; E {{ Φ }} :=
  wp_bind_item (.seq m₂)

/--
**The loop invariant rule.** A loop with body `m` satisfies a postcondition `Φ`, given an
invariant `I`, if, given `I`, the body satisfies the postcondition that gives `I` back when it
completes normally, and `Φ` when it completes in any other way (`H`; see `loopInvPost`).

A loop only ends by completing abruptly, so `Φ` only needs to hold of abrupt outcomes. The proof
is by Löb induction, which this rule packages so that a proof about a loop needs none of its own:
each iteration takes a step (`wp_loop`), so the invariant only has to hold again one step later.
-/
public theorem wp_loop_inv {m : LoweredExpr} (I : IProp GF)
    (H : I ⊢ WP m @ s; E {{ o, loopInvPost I Φ o }}) :
    I ⊢ WP (LoweredExpr.loop m) @ s; E {{ Φ }} := by
  iintro HI
  iloeb as IH
  iapply wp_loop
  inext
  iapply wp_bind_seq
  ihave Hm := H $$ HI
  iapply wp_wand $$ Hm
  iintro %o Ho
  cases o with
  | normal v =>
    simp only [loopInvPost, DartLang.Outcome.toExpr]
    iapply wp_seq
    inext
    iapply IH $$ Ho
  -- An abrupt completion of the body propagates out of the sequence, and so out of the loop.
  -- (`rw` restates the sequence as `EctxItem.fill`, which `iapply` doesn't unfold.)
  | throwing v =>
    rw [show LoweredExpr.seq (Outcome.throwing v).toExpr (.loop m) =
      (EctxItem.seq (.loop m)).fill (.throwing v) from rfl]
    iapply wp_bubble_exception
    inext
    simp only [loopInvPost]
    iexact Ho
  | returning v =>
    rw [show LoweredExpr.seq (Outcome.returning v).toExpr (.loop m) =
      (EctxItem.seq (.loop m)).fill (.returning v) from rfl]
    iapply wp_bubble_return rfl
    inext
    simp only [loopInvPost]
    iexact Ho
  | breaking l =>
    rw [show LoweredExpr.seq (Outcome.breaking l).toExpr (.loop m) =
      (EctxItem.seq (.loop m)).fill (.breaking l) from rfl]
    iapply wp_bubble_break rfl rfl
    inext
    simp only [loopInvPost]
    iexact Ho

/--
A binary operator on integers `n₁` and `n₂`, whose integer mode is `mode`, evaluates to its result
`v` (`h`; see `IntBinOp.eval`): it satisfies a postcondition `Φ` that holds, one step later, of
completing normally with `v` (`▷ Φ (.normal v)`). In mode `checked`, `h` says in particular that
the result is in 64-bit range.
-/
public theorem wp_intBin {op : IntBinOp} {mode : IntMode} {n₁ n₂ : Int} {v : Value}
    (h : op.eval mode n₁ n₂ = some v) :
    ▷ Φ (.normal v) ⊢
      WP (LoweredExpr.intBin (τ := τ) op (some mode) (.val (.int n₁)) (.val (.int n₂))) @ s; E
        {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .intBin h

/--
Unary minus on an integer `n`, whose integer mode is `mode`, evaluates to `k` (`h`; see
`IntMode.arith`): it satisfies a postcondition `Φ` that holds, one step later, of completing
normally with `k` (`▷ Φ (.normal (.int k))`).
-/
public theorem wp_intNeg {mode : IntMode} {n k : Int} (h : mode.arith (-n) = some k) :
    ▷ Φ (.normal (.int k)) ⊢
      WP (LoweredExpr.intNeg (τ := τ) (some mode) (.val (.int n))) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .intNeg h

/--
Equality of values `v₁` and `v₂` that can be compared evaluates to whether they're equal (`h`; see
`Value.primEq?`): it satisfies a postcondition `Φ` that holds, one step later, of completing
normally with that boolean (`▷ Φ (.normal (.bool b))`).
-/
public theorem wp_primEq {v₁ v₂ : Value} {b : Bool} (h : Value.primEq? v₁ v₂ = some b) :
    ▷ Φ (.normal (.bool b)) ⊢ WP (LoweredExpr.primEq (.val v₁) (.val v₂)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .primEq h

end Laws

/-! ## Specifications of functions -/

section FunSpecs

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF] [P : SemanticParams τ]
include hlc

/--
`FunSpec f Pre Post` is a specification of top-level function `f`: every call of `f` whose
arguments have evaluated to values `vs` satisfying the precondition `Pre vs` completes safely,
with an outcome `o` satisfying the postcondition `Post vs o`.

It's a Texan triple (`{{ Pre vs }} call f vs T {{ o, RET o; Post vs o }}`) for every call of `f`:
for all argument values `vs`, and all static types `T` of the call expression.

A Texan triple `{{ P }} e {{ o, RET o; Q o }}` is Iris's notation for a persistent Hoare triple.
It stands for `□ ∀ Φ, P -∗ ▷ (∀ o, Q o -∗ Φ o) -∗ WP e {{ Φ }}`: given the precondition `P`, `e`
satisfies every postcondition `Φ` that follows from the postcondition `Q`. The implication only
has to hold one step later (`▷`), which is harmless here: a call always takes a step before its
body runs. Being persistent (`□`), a specification can be used for any number of calls.

Naming `FunSpec` lets the laws for using and proving a specification (`FunSpec.wp_call`,
`FunSpec.intro`) be stated once, and keeps proof goals readable, since iris-lean doesn't display
Texan triples compactly.
-/
@[expose]
public def FunSpec (f : String) (Pre : List Value → IProp GF)
    (Post : List Value → DartLang.Outcome (τ := τ) → IProp GF) : IProp GF :=
  iprop(∀ (vs : List Value) (T : τ),
    {{ Pre vs }} (LoweredExpr.call f (vs.map .val) T) {{ o, RET o; Post vs o }})

/-- `FunSpec f Pre Post` is persistent, since each of its Texan triples is. -/
public instance FunSpec_persistent (f : String) (Pre : List Value → IProp GF)
    (Post : List Value → DartLang.Outcome (τ := τ) → IProp GF) :
    Persistent (FunSpec f Pre Post) := by
  unfold FunSpec
  infer_instance

/--
Using a specification: a call of `f` whose arguments have evaluated to `vs` satisfies a
postcondition `Φ`, given a specification of `f` (`FunSpec f Pre Post`), its precondition
(`Pre vs`), and that its postcondition implies `Φ` (`∀ o, Post vs o -∗ Φ o`). (The Texan triple
only needs that implication one step later, under a `▷`; having it now is enough.)
-/
public theorem FunSpec.wp_call {f : String} {Pre : List Value → IProp GF}
    {Post : List Value → DartLang.Outcome (τ := τ) → IProp GF} {vs : List Value} {T : τ}
    {Φ : DartLang.Outcome (τ := τ) → IProp GF} :
    FunSpec f Pre Post ∗ Pre vs ∗ (∀ o, Post vs o -∗ Φ o) ⊢
      WP (LoweredExpr.call f (vs.map .val) T) {{ Φ }} := by
  unfold FunSpec
  iintro ⟨#Hspec, HPre, HΦ⟩
  ihave Hcall := Hspec $$ %vs %T %Φ HPre
  iapply Hcall
  inext
  iexact HΦ

/--
Proving a specification of a top-level function `f`, by Löb induction: `f` meets the
specification `FunSpec f Pre Post` if:
- the function table declares `f` as `d` (`hf`);
- the precondition implies that there's one argument per formal parameter (`hlen`); and
- for all argument values `vs`, static types `T` and locations `ℓs`, the body, with every integer
  operator's mode set to `f`'s integer mode and the formal parameters bound to cells at `ℓs`, run
  as the body of a running call, satisfies the postcondition
  (`WP (.frame ((d.body.withIntMode (P.intModeOf f)).bindVariables (d.params.zip ℓs)) T)
  {{ o, Post vs o }}`), given the precondition (`Pre vs`), the ownership of the cells, holding the
  arguments (`PointsToVals ℓs vs`), and the specification itself (`FunSpec f Pre Post`), for the
  body's own calls of `f` (`H`).

Assuming the specification for the body's calls isn't circular: each call takes a step before its
body runs, which is what Löb induction requires (see `wp_call`). For a function that doesn't call
itself, `H` can ignore the assumption.
-/
public theorem FunSpec.intro {f : String} {d : FunctionDecl (τ := τ)}
    {Pre : List Value → IProp GF} {Post : List Value → DartLang.Outcome (τ := τ) → IProp GF}
    (hf : P.functions f = some d) (hlen : ∀ vs, Pre vs ⊢ ⌜d.params.length = vs.length⌝)
    (H : ∀ vs T ℓs, FunSpec f Pre Post ∗ Pre vs ∗ PointsToVals ℓs vs ⊢
      WP (LoweredExpr.frame ((d.body.withIntMode (P.intModeOf f)).bindVariables
        (d.params.zip ℓs)) T) {{ o, Post vs o }}) :
    ⊢ FunSpec f Pre Post := by
  iloeb as IH
  unfold FunSpec
  iintro %vs %T
  imodintro
  iintro %Φ HPre HΦ
  rcases Decidable.em (d.params.length = vs.length) with hl | hl
  · iapply DartSemantics.wp_call hf hl
    inext
    -- `unfold FunSpec` above unfolded the specification in `IH` too. Fold it back, as `H` needs.
    ihave #IH' : FunSpec f Pre Post $$ []
    · unfold FunSpec
      iexact IH
    iintro %ℓs Hls
    ihave Hwp := H vs T ℓs $$ [$IH' $HPre $Hls]
    iapply wp_wand $$ Hwp
    iintro %o Ho
    iapply HΦ $$ Ho
  · ihave %h := hlen vs $$ HPre
    exact absurd h hl

end FunSpecs

end DartSemantics
