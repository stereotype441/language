module
public import DartSemantics.GhostState
public import Iris.ProgramLogic.EctxLifting
-- iris-lean's `EctxLifting.lean` doesn't put its lemmas in a `public section`, so under the module
-- system they're private to that module. `import all` makes them visible here.
import all Iris.ProgramLogic.EctxLifting

/-!
# Primitive laws of the program logic

One weakest-precondition law for each head-step rule (`HeadStep`), plus bind. Each law is stated
for every choice of `SemanticParams`.

Run-time subtype checks and promotion checks need the dynamic type of a value. For the null object
and booleans it's fixed; for an object it's recorded in the object's own cell, which never changes.
`HasDynamicType v S` is the persistent knowledge that `v`'s dynamic type is `S`.
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
  | .obj ℓ => iprop(∃ fs, ℓ ↦{.discard} (.object S fs : Cell))
  | .error _ => iprop(False)
  | .cont _ => iprop(False)

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

/-- The dynamic type of an object is recorded in the object's own cell. -/
public theorem HasDynamicType.obj {ℓ : Loc} {S : τ} {fs : List (String × Loc)} :
    ℓ ↦{.discard} (.object S fs : Cell) ⊢ HasDynamicType (GF := GF) (.obj ℓ : Value) S := by
  simp only [HasDynamicType]
  iintro H
  iexists fs
  iexact H

/-- The ghost heap agrees with what `HasDynamicType` says. -/
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
  | obj ℓ =>
    simp only [HasDynamicType]
    iintro ⟨Hσ, %fs, Hℓ⟩
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

/-- The object headers in the state interpretation give the dynamic type of any value. -/
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
  | obj ℓ =>
    simp only [State.dynamicType] at h
    split at h
    · rename_i C fs hℓ
      simp only [Option.some.injEq] at h
      subst h
      have hl : ObjectHeaders (GF := GF) σ ⊢ ℓ ↦{.discard} (.object C fs : Cell) :=
        (BigSepM.bigSepM_lookup (Φ := fun ℓ c => cellHeader (GF := GF) ℓ c)
          (by rw [State.get?_toMap]; exact hℓ)).trans (by simp only [cellHeader]; exact .rfl)
      simp only [HasDynamicType]
      iintro H
      iexists fs
      iapply hl $$ H
    · cases h
  | error e => cases h
  | cont k => cases h

/--
The persistent knowledge that value `v` doesn't refer to an object with an instance variable named
`name`, so that reading property `name` of `v` runs a getter that is user code.

This mirrors how the semantics currently chooses between the two (`State.instanceVariable?`, which
looks at the instance variables recorded in the object's own cell). Once the semantics has class
declarations, a property read will dispatch on the members of the receiver's class instead (which
also closes the known gaps described at `State.instanceVariable?`), and this will be replaced by a
fact about that class.
-/
@[expose]
public def NoInstanceVariable (v : Value) (name : String) : IProp GF :=
  match v with
  | .obj ℓ => iprop(∃ C fs, ℓ ↦{.discard} (.object C fs : Cell) ∗ ⌜fs.lookup name = none⌝)
  | _ => iprop(True)

public instance NoInstanceVariable_persistent (v : Value) (name : String) :
    Persistent (NoInstanceVariable (GF := GF) v name) := by
  cases v <;> simp only [NoInstanceVariable] <;> infer_instance

omit Γ in
/-- The ghost heap agrees with what `NoInstanceVariable` says. -/
public theorem NoInstanceVariable.valid {σ : State} {v : Value} {name : String} :
    genHeapInterp σ.toMap ∗ NoInstanceVariable (GF := GF) v name ⊢
      |==> ⌜σ.instanceVariable? v name = none⌝ := by
  cases v with
  | obj ℓ =>
    simp only [NoInstanceVariable]
    iintro ⟨Hσ, %C, %fs, Hℓ, %hf⟩
    imod genHeap_valid $$ [$Hσ $Hℓ] with %h
    imodintro
    ipureintro
    rw [State.get?_toMap] at h
    simp [State.instanceVariable?, h, hf]
  | _ =>
    iintro -
    imodintro
    ipureintro
    rfl

omit Γ in
/-- Allocating a cell that isn't an object's own cell leaves the object headers as they were. -/
public theorem ObjectHeaders.alloc {σ : State} {c : Cell}
    (hc : cellHeader (GF := GF) σ.fresh c ⊣⊢ emp) :
    ObjectHeaders (GF := GF) σ ⊢ ObjectHeaders (σ.alloc c) := by
  simp only [ObjectHeaders, State.toMap_alloc]
  refine .trans ?_ (BigSepM.bigSepM_insert (by rw [State.get?_toMap, State.lookup_fresh])).2
  exact emp_sep.2.trans (sep_mono_left hc.2)

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

/-- An expression that has completed normally satisfies a postcondition that holds of its value. -/
public theorem wp_val (v : Value) : Φ (.normal v) ⊢ WP (LoweredExpr.val v) @ s; E {{ Φ }} :=
  wp_value' (v := Outcome.normal v)

/-- An expression that has thrown satisfies a postcondition that holds of its exception. -/
public theorem wp_throwing (v : Value) :
    Φ (.throwing v) ⊢ WP (LoweredExpr.throwing v) @ s; E {{ Φ }} :=
  wp_value' (v := Outcome.throwing v)

/--
Bind, for one evaluation context item: to show `Ki.fill e` satisfies a postcondition, show that
`e` satisfies one saying that plugging its outcome back into `Ki` does.
-/
public theorem wp_bind_item (Ki : EctxItem) {e : LoweredExpr} :
    WP e @ s; E {{ o, WP (Ki.fill o.toExpr) @ s; E {{ Φ }} }} ⊢ WP (Ki.fill e) @ s; E {{ Φ }} :=
  wp_bind (Expr := LoweredExpr) (EvContext.fill [Ki])

/--
If `e₁` hasn't completed, and in every state takes a head step to `e₂` that leaves the state
unchanged, then `e₁` satisfies a postcondition if `e₂` does, one step later (`▷`).
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
If `e` hasn't completed, and in every state where the dynamic type of `v` is `S` takes a head step
to `e'` that leaves the state unchanged, then, given that the dynamic type of `v` is `S`, `e`
satisfies a postcondition if `e'` does, one step later (`▷`).
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
If `e` hasn't completed, and in every state takes a head step to the value `v` that leaves the
state unchanged, then `e` satisfies a postcondition that holds, one step later (`▷`), of completing
normally with `v`.
-/
public theorem wp_pure_step_val {e : LoweredExpr} {v : Value} (hv : e.toOutcome? = none)
    (h : ∀ σ, HeadStep e σ (.val v) σ) : ▷ Φ (.normal v) ⊢ WP e @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_pure_step hv h)
  exact later_mono (wp_val v)

/--
If `e` hasn't completed, and in every state takes a head step to throwing `v` that leaves the state
unchanged, then `e` satisfies a postcondition that holds, one step later (`▷`), of throwing `v`.
-/
public theorem wp_pure_step_throwing {e : LoweredExpr} {v : Value} (hv : e.toOutcome? = none)
    (h : ∀ σ, HeadStep e σ (.throwing v) σ) : ▷ Φ (.throwing v) ⊢ WP e @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_pure_step hv h)
  exact later_mono (wp_throwing v)

/-- The null literal evaluates to the null object. -/
public theorem wp_null : ▷ Φ (.normal .null) ⊢ WP (LoweredExpr.null (τ := τ)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .null

/-- A declaration outside a block is converted to a block containing just that declaration. -/
public theorem wp_declare {v : Variable} {T : τ} {startsNull : Bool} :
    ▷ WP (LoweredExpr.block [.declare v T startsNull]) @ s; E {{ Φ }} ⊢
      WP (LoweredExpr.declare v T startsNull) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .declare

/-- An empty block completes normally, with the null object. -/
public theorem wp_blockNil :
    ▷ Φ (.normal .null) ⊢ WP (LoweredExpr.block (τ := τ) []) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .blockNil

/-- A block that starts with anything other than a declaration runs it, then the rest. -/
public theorem wp_blockCons {m : LoweredExpr} {ms : List LoweredExpr}
    (h : ∀ v T startsNull, m ≠ .declare v T startsNull) :
    ▷ WP (LoweredExpr.seq m (.block ms)) @ s; E {{ Φ }} ⊢
      WP (LoweredExpr.block (m :: ms)) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .blockCons h

/-- Once the first part of a sequence completes normally, the second part runs. -/
public theorem wp_seq {v : Value} {m : LoweredExpr} :
    ▷ WP m @ s; E {{ Φ }} ⊢ WP (LoweredExpr.seq (.val v) m) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .seq

/-- A null check on the null object throws. -/
public theorem wp_nullCheck_null :
    ▷ Φ (.throwing (.error .typeError)) ⊢
      WP (LoweredExpr.nullCheck (τ := τ) (.val .null)) @ s; E {{ Φ }} := by
  refine wp_pure_step_throwing (by rfl) fun _ => ?_
  exact .nullCheckNull

/-- A null check on any other object evaluates to it. -/
public theorem wp_nullCheck {v : Value} (h : v ≠ .null) :
    ▷ Φ (.normal v) ⊢ WP (LoweredExpr.nullCheck (.val v)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .nullCheck h

/-- A conditional whose condition is `true` runs its first branch. -/
public theorem wp_cond_true {m₂ m₃ : LoweredExpr} {T : τ} :
    ▷ WP m₂ @ s; E {{ Φ }} ⊢ WP (LoweredExpr.cond (.val (.bool true)) m₂ m₃ T) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .condTrue

/-- A conditional whose condition is `false` runs its second branch. -/
public theorem wp_cond_false {m₂ m₃ : LoweredExpr} {T : τ} :
    ▷ WP m₃ @ s; E {{ Φ }} ⊢ WP (LoweredExpr.cond (.val (.bool false)) m₂ m₃ T) @ s; E {{ Φ }} := by
  refine wp_pure_step (by rfl) fun _ => ?_
  exact .condFalse

/-- An exception propagates out of an evaluation context item. -/
public theorem wp_bubble (Ki : EctxItem) (v : Value) :
    ▷ Φ (.throwing v) ⊢ WP (Ki.fill (.throwing v)) @ s; E {{ Φ }} := by
  refine wp_pure_step_throwing (EctxItem.toOutcome?_fill _ _) fun _ => ?_
  exact .bubble

/-- A cast whose check answers yes evaluates to its operand. -/
public theorem wp_as_true {v : Value} {S T : τ} (h : RtSub S T true) :
    HasDynamicType v S ∗ ▷ Φ (.normal v) ⊢ WP (LoweredExpr.as (.val v) T) @ s; E {{ Φ }} := by
  refine (sep_mono_right (later_mono (wp_val _))).trans
    (wp_step_of_dynamicType (by rfl) fun _ hS => ?_)
  exact .asTrue hS h

/-- A cast whose check answers no throws. -/
public theorem wp_as_false {v : Value} {S T : τ} (h : RtSub S T false) :
    HasDynamicType v S ∗ ▷ Φ (.throwing (.error .typeError)) ⊢
      WP (LoweredExpr.as (.val v) T) @ s; E {{ Φ }} := by
  refine (sep_mono_right (later_mono (wp_throwing _))).trans
    (wp_step_of_dynamicType (by rfl) fun _ hS => ?_)
  exact .asFalse hS h

/-- An is-expression evaluates to the answer of its check. -/
public theorem wp_is {v : Value} {S T : τ} {b : Bool} (h : RtSub S T b) :
    HasDynamicType v S ∗ ▷ Φ (.normal (.bool b)) ⊢
      WP (LoweredExpr.is (.val v) T) @ s; E {{ Φ }} := by
  refine (sep_mono_right (later_mono (wp_val _))).trans
    (wp_step_of_dynamicType (by rfl) fun _ hS => ?_)
  exact .is hS h

/-- A cast whose check doesn't terminate doesn't terminate, so it satisfies every postcondition. -/
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
An is-expression whose check doesn't terminate doesn't terminate, so it satisfies every
postcondition.
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
uninitialized as the declaration says, and runs the rest of the block with `v` resolved to it.
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
  have hc : cellHeader (GF := GF) σ₁.fresh (if startsNull then .val .null else .uninit : Cell) ⊣⊢
      emp := by
    cases startsNull <;> exact .rfl
  ihave #Hhdr' := ObjectHeaders.alloc hc $$ Hhdr
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
Reading a local variable gives the value in its cell, provided the value satisfies the variable's
(possibly promoted) static type, so that the promotion check passes.
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
Reading a property of an object that has an instance variable of that name (`fs.lookup p.name =
some ℓf`) gives the value in the instance variable's cell, provided the value satisfies the
property's (possibly promoted) static type.
-/
public theorem wp_propertyGetField {ℓ ℓf : Loc} {p : Property} {T C S : τ}
    {fs : List (String × Loc)} {dq : DFrac} {w : Value} (hf : fs.lookup p.name = some ℓf)
    (hST : S ≤ T) :
    ℓ ↦{.discard} (.object C fs : Cell) ∗ HasDynamicType w S ∗ ▷ (ℓf ↦{dq} (.val w : Cell)) ∗
        ▷ ((ℓf ↦{dq} (.val w : Cell)) -∗ Φ (.normal w)) ⊢
      WP (LoweredExpr.propertyGet (.val (.obj ℓ)) p T) @ s; E {{ Φ }} := by
  iintro ⟨#Hobj, #Hty, >Hl, HΦ⟩
  iapply wp_lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr⟩
  ihave %Hobjl : ⌜σ₁.lookup ℓ = some (.object C fs)⌝ $$ [Hh Hobj]
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
  have hiv : σ₁.instanceVariable? (.obj ℓ) p.name = some ℓf := by
    simp [State.instanceVariable?, Hobjl, hf]
  have hstep : HeadStep (LoweredExpr.propertyGet (.val (.obj ℓ)) p T) σ₁ (.val w) σ₁ :=
    .propertyGetField hiv Hlook (.of_le Hdt hST)
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

/--
Reading a property of a value that doesn't refer to an object with an instance variable of that
name runs the property's getter, which is user code (see `SemanticParams.getterImpl`).

Until the semantics has calls, a getter is a function of the whole state, which a proof doesn't
own, so this law takes a specification of the getter instead: it never gets stuck (`hans`), and
every value it returns satisfies the property's declared type `p.type`, and satisfies `Q` (`hQ`),
as the getter's own body would guarantee. The read's static type
`T`, possibly promoted, must be a supertype of `p.type` (`hT`), so the promotion check passes. The
postcondition must then hold for every such value. The placeholder getter model can't loop forever
or throw; real getters can, and the law will change when calls replace `SemanticParams.getterImpl`.
-/
public theorem wp_propertyGetGetter {v : Value} {p : Property} {T : τ} (Q : Value → Prop)
    (hans : ∀ σ, ∃ w, P.getterImpl p v σ = some w)
    (hQ : ∀ σ w, P.getterImpl p v σ = some w →
      Q w ∧ ∃ S, σ.dynamicType w = some S ∧ S ≤ p.type)
    (hT : p.type ≤ T) :
    NoInstanceVariable v p.name ∗
        ▷ (∀ w S, ⌜Q w⌝ -∗ HasDynamicType w S -∗ ⌜S ≤ p.type⌝ -∗ Φ (.normal w)) ⊢
      WP (LoweredExpr.propertyGet (.val v) p T) @ s; E {{ Φ }} := by
  iintro ⟨#Hno, HΦ⟩
  iapply wp_lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr⟩
  ihave %Hiv : ⌜σ₁.instanceVariable? v p.name = none⌝ $$ [Hh Hno]
  · ihave >%Hd := NoInstanceVariable.valid $$ [$Hh $Hno]
    ipureintro
    exact Hd
  obtain ⟨w, hw⟩ := hans σ₁
  obtain ⟨hq, S, hS, hSp⟩ := hQ σ₁ w hw
  have hstep : HeadStep (LoweredExpr.propertyGet (.val v) p T) σ₁ (.val w) σ₁ :=
    .propertyGetGetter Hiv hw (.of_le hS (le_trans hSp hT))
  imodintro
  isplit
  · ipureintro
    exact ⟨[], _, _, [], hstep, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs hstep
  ihave #Htyw := HasDynamicType.of_headers hS $$ Hhdr
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
  · iapply HΦ $$ %w %S %hq Htyw %hSp

end Laws

end DartSemantics
