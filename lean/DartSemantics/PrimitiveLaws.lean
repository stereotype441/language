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

For objects, a law about an object usually needs its *header*: a persistent points-to for its own
cell (`ℓ ↦{.discard} .object k C fs`), which records its class `k` (and so, through the program's
class table, which member each name dispatches to) and where its instance variables are stored.
Members have specifications too (`MemberSpec`, a Texan triple for every run of a member's body),
with laws for using one in a method call or property read (`MemberSpec.wp_methodCall`,
`MemberSpec.wp_propertyGet`) and one for proving one by Löb induction (`MemberSpec.intro`).

Run-time subtype checks and promotion checks need the dynamic type of a value. For the null object
and booleans it's fixed; for an object it's recorded in the object's own cell, which never changes.
`HasDynamicType v S` is the persistent knowledge that `v`'s dynamic type is `S`.

Strings are objects too, whose cells never change, so a law about a string needs a persistent
points-to for its cell (`ℓ ↦{.discard} .string cu`). A string constant evaluates to its canonical
object (`wp_constant_string`, which provides `IsConst`), and a string concatenation to a new
string (`wp_concat`, which provides `Fresh`, so that a proof can tell that two new strings are
different objects).

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

/--
The persistent knowledge that the dynamic type of value `v` is `S`. For an object in the heap, it's
recorded in the object's own cell: for an instance of a class, its dynamic type is in the cell;
a string's dynamic type is `String`.
-/
@[expose]
public def HasDynamicType (v : Value) (S : τ) : IProp GF :=
  match v with
  | .null => iprop(⌜S = Γ.Null⌝)
  | .bool _ => iprop(⌜S = Γ.bool⌝)
  | .int _ => iprop(⌜S = Γ.int⌝)
  | .obj ℓ => iprop((∃ k fs, ℓ ↦{.discard} (.object k S fs : Cell)) ∨
      (⌜S = Γ.String⌝ ∗ ∃ cu, ℓ ↦{.discard} (.string cu : Cell)))
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
  ileft
  iexists k, fs
  iexact H

/--
The dynamic type of a string is `String`: a persistent points-to for the string's cell
(`ℓ ↦{.discard} (.string cu)`) says that the dynamic type of `.obj ℓ` is `String`.
-/
public theorem HasDynamicType.string {ℓ : Loc} {cu : List UInt16} :
    ℓ ↦{.discard} (.string cu : Cell) ⊢ HasDynamicType (GF := GF) (.obj ℓ : Value) Γ.String := by
  simp only [HasDynamicType]
  iintro H
  iright
  isplitr
  · ipureintro
    trivial
  · iexists cu
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
    iintro ⟨Hσ, ⟨%k, %fs, Hℓ⟩ | ⟨%hS, %cu, Hℓ⟩⟩
    · imod genHeap_valid $$ [$Hσ $Hℓ] with %h
      imodintro
      ipureintro
      rw [State.get?_toMap] at h
      simp [State.dynamicType, h]
    · imod genHeap_valid $$ [$Hσ $Hℓ] with %h
      imodintro
      ipureintro
      rw [State.get?_toMap] at h
      simp [State.dynamicType, h, hS]
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
      ileft
      iexists k, fs
      iapply hl $$ H
    · rename_i cu hℓ
      simp only [Option.some.injEq] at h
      subst h
      have hl : ObjectHeaders (GF := GF) σ ⊢ ℓ ↦{.discard} (.string cu : Cell) :=
        (BigSepM.bigSepM_lookup (Φ := fun ℓ c => cellHeader (GF := GF) ℓ c)
          (by rw [State.get?_toMap]; exact hℓ)).trans (by simp only [cellHeader]; exact .rfl)
      iintro H
      iapply HasDynamicType.string
      iapply hl $$ H
    · cases h
  | error e => cases h
  | cont k => cases h

omit Γ in
/-- A variable's cell `c` (`hc`) has no header (`cellHeader ℓ c ⊣⊢ emp`). -/
theorem cellHeader_of_isVar {ℓ : Loc} {c : Cell} (hc : c.isVar = true) :
    cellHeader (GF := GF) ℓ c ⊣⊢ emp := by
  cases c <;> simp [Cell.isVar] at hc <;> exact .rfl

omit Γ in
/--
Allocating a variable's cell `c` (`hc`) leaves the object headers as they were
(`ObjectHeaders σ ⊢ ObjectHeaders (σ.alloc c)`).
-/
public theorem ObjectHeaders.alloc {σ : State} {c : Cell} (hc : c.isVar = true) :
    ObjectHeaders (GF := GF) σ ⊢ ObjectHeaders (σ.alloc c) := by
  simp only [ObjectHeaders, State.toMap_alloc]
  refine .trans ?_ (BigSepM.bigSepM_insert (by rw [State.get?_toMap, State.lookup_fresh])).2
  exact emp_sep.2.trans (sep_mono_left (cellHeader_of_isVar hc).2)

omit Γ in
/--
Allocating an object's own cell `c` adds its header to the object headers: given the headers of
`σ` (`ObjectHeaders σ`) and a persistent points-to for the new cell (`σ.fresh ↦{.discard} c`),
the headers of `σ.alloc c` hold.
-/
public theorem ObjectHeaders.alloc_object {σ : State} {k : String} {C : τ}
    {fs : List (String × Loc)} :
    ObjectHeaders (GF := GF) σ ∗ σ.fresh ↦{.discard} (.object k C fs : Cell) ⊢
      ObjectHeaders (σ.alloc (.object k C fs)) := by
  simp only [ObjectHeaders, State.toMap_alloc]
  refine .trans ?_ (BigSepM.bigSepM_insert (by rw [State.get?_toMap, State.lookup_fresh])).2
  simp only [cellHeader]
  exact sep_comm.1

omit Γ in
/--
Updating the cell at `ℓ` leaves the object headers as they were
(`ObjectHeaders σ ⊢ ObjectHeaders (σ.update ℓ c)`), if:
- the cell holds `c₀` (`h`), which is a variable's cell (`hc₀`); and
- the new contents `c` are a variable's cell too (`hc`).
-/
public theorem ObjectHeaders.update {σ : State} {ℓ : Loc} {c₀ c : Cell}
    (h : σ.lookup ℓ = some c₀) (hc₀ : c₀.isVar = true) (hc : c.isVar = true) :
    ObjectHeaders (GF := GF) σ ⊢ ObjectHeaders (σ.update ℓ c) := by
  simp only [ObjectHeaders, State.toMap_update h]
  refine (BigSepM.bigSepM_delete (by rw [State.get?_toMap]; exact h)).1.trans ?_
  refine .trans ?_ BigSepM.bigSepM_insert_delete.2
  exact sep_mono_left ((cellHeader_of_isVar hc₀).1.trans (cellHeader_of_isVar hc).2)

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

/--
Ownership of the cells at locations `ℓs`, all uninitialized. (An instance creation gives this for
the cells of the new object's instance variables; see `wp_new`.)
-/
@[expose]
public def PointsToUninit : List Loc → IProp GF
  | [] => iprop(emp)
  | ℓ :: ℓs => iprop(ℓ ↦ (.uninit : Cell) ∗ PointsToUninit ℓs)

omit Γ in
/--
What the logic knows about each entry of a table of constants `consts` gives what it knows about
the entry that `lookup` finds for `c` (`h`): `ConstEntry τ c ℓ`.
-/
public theorem ConstEntry.of_lookup {consts : List (ConstValue × Loc)} {c : ConstValue} {ℓ : Loc}
    (h : consts.lookup c = some ℓ) :
    ([∗list] p ∈ consts, ConstEntry τ (GF := GF) p.1 p.2) ⊢ ConstEntry τ c ℓ := by
  induction consts with
  | nil => simp [List.lookup] at h
  | cons p consts ih =>
    obtain ⟨c', ℓ'⟩ := p
    refine BigSepL.bigSepL_cons.1.trans ?_
    by_cases hc : c = c'
    · subst hc
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact sep_elim_left
    · have hb : (c == c') = false := by simp [hc]
      simp only [List.lookup, hb] at h
      exact sep_elim_right.trans (ih h)

omit Γ in
/--
Allocating a string's cell adds its header to the object headers: given the headers of `σ`
(`ObjectHeaders σ`) and a persistent points-to for the new cell (`σ.fresh ↦{.discard} .string cu`),
the headers of `σ.alloc (.string cu)` hold.
-/
public theorem ObjectHeaders.alloc_string {σ : State} {cu : List UInt16} :
    ObjectHeaders (GF := GF) σ ∗ σ.fresh ↦{.discard} (.string cu : Cell) ⊢
      ObjectHeaders (σ.alloc (.string cu)) := by
  simp only [ObjectHeaders, State.toMap_alloc]
  refine .trans ?_ (BigSepM.bigSepM_insert (by rw [State.get?_toMap, State.lookup_fresh])).2
  simp only [cellHeader]
  exact sep_comm.1

omit Γ in
variable (τ) in
/--
`ℓ` is a location that a step allocated, as the logic tracks it: the step's law provides
`Fresh τ ℓ`, which can't be duplicated, so locations with `Fresh` are all different (`Fresh.ne`).
It's iris-lean's `metaToken ℓ ⊤`, which the ghost heap provides for each newly allocated cell. (The
type representation `τ` is explicit, since nothing else determines it.)
-/
@[expose]
public def Fresh (ℓ : Loc) : IProp GF := metaToken (V := Cell) (GF := GF) ℓ ⊤

omit Γ in
/-- Locations with `Fresh` are different: `Fresh τ ℓ₁ ∗ Fresh τ ℓ₂ ⊢ ⌜ℓ₁ ≠ ℓ₂⌝`. -/
public theorem Fresh.ne {ℓ₁ ℓ₂ : Loc} : Fresh τ (GF := GF) ℓ₁ ∗ Fresh τ ℓ₂ ⊢ ⌜ℓ₁ ≠ ℓ₂⌝ := by
  have hne : (⊤ : CoPset) ≠ ∅ := fun h => CoPset.mem_empty (p := 1) (h ▸ CoPset.mem_full)
  unfold Fresh
  iintro ⟨H₁, H₂⟩
  iapply metaToken_ne hne $$ H₁ H₂

omit Γ in
/--
Allocating a string, holding code units `cu`, can be mirrored in the ghost state: given the state
interpretation's ghost heap and object headers for `σ`, a basic update gives them for
`σ.alloc (.string cu)`, a persistent points-to for the new string's cell, and that it's newly
allocated (`Fresh τ σ.fresh`).
-/
public theorem allocString_ghost (σ : State) (cu : List UInt16) :
    genHeapInterp σ.toMap ∗ ObjectHeaders (GF := GF) σ ⊢
      |==> ((genHeapInterp (σ.alloc (.string cu)).toMap ∗ ObjectHeaders (σ.alloc (.string cu))) ∗
        σ.fresh ↦{.discard} (.string cu : Cell) ∗ Fresh τ σ.fresh) := by
  iintro ⟨Hh, #Hhdr⟩
  have hfresh : get? σ.toMap σ.fresh = none := by rw [State.get?_toMap, State.lookup_fresh]
  imod genHeap_alloc (v := (.string cu : Cell)) hfresh $$ Hh with ⟨Hh, Hl, Hm⟩
  imod pointsTo_persist $$ Hl with #Hl
  ihave #Hhdr' := ObjectHeaders.alloc_string (GF := GF) (σ := σ) (cu := cu) $$ [$Hhdr $Hl]
  imodintro
  isplitl [Hh]
  · rw [State.toMap_alloc]
    iframe Hh
    iexact Hhdr'
  · isplitr
    · iexact Hl
    · unfold Fresh
      iexact Hm

omit Γ in
/--
The knowledge that `cu` is the string form of value `v`, as a part of a string concatenation (see
`State.stringPart?`): for an object, a persistent points-to for its cell, which is a string holding
`cu`; for any other value, that `cu` is its string form (which doesn't depend on the state, so it's
stated for `State.empty`; it's `False` for a value that has no string form).
-/
@[expose]
public def StringPart (v : Value) (cu : List UInt16) : IProp GF :=
  match v with
  | .obj ℓ => iprop(ℓ ↦{.discard} (.string cu : Cell))
  | v => iprop(⌜(State.empty (τ := τ)).stringPart? v = some cu⌝)

omit Γ in
/-- `StringPart v cu` is persistent: it's a persistent points-to or a pure fact. -/
public instance StringPart_persistent (v : Value) (cu : List UInt16) :
    Persistent (StringPart (GF := GF) v cu) := by
  cases v <;> simp only [StringPart] <;> infer_instance

omit Γ in
/--
`StringPart v cu` for each value `v` in `vs` and the code units `cu` in the same position in
`cus`. If the lists have different lengths, it's `False`.
-/
@[expose]
public def StringParts : List Value → List (List UInt16) → IProp GF
  | [], [] => iprop(emp)
  | v :: vs, cu :: cus => iprop(StringPart v cu ∗ StringParts vs cus)
  | _, _ => iprop(False)

omit Γ in
/-- `StringParts vs cus` is persistent: it's a separating conjunction of persistent propositions. -/
public instance StringParts_persistent (vs : List Value) (cus : List (List UInt16)) :
    Persistent (StringParts (GF := GF) vs cus) := by
  induction vs generalizing cus with
  | nil => cases cus <;> simp only [StringParts] <;> infer_instance
  | cons v vs ih => cases cus <;> simp only [StringParts] <;> infer_instance

omit Γ in
/--
The ghost heap agrees with `StringPart`: given the ghost heap's interpretation of the state
(`genHeapInterp σ.toMap`), if `cu` is the string form of `v` according to the logic
(`StringPart v cu`), then it is in the state too (`σ.stringPart? v = some cu`).
-/
public theorem StringPart.valid {σ : State} {v : Value} {cu : List UInt16} :
    genHeapInterp σ.toMap ∗ StringPart (GF := GF) v cu ⊢ |==> ⌜σ.stringPart? v = some cu⌝ := by
  cases v with
  | obj ℓ =>
    simp only [StringPart]
    iintro ⟨Hσ, Hℓ⟩
    imod genHeap_valid $$ [$Hσ $Hℓ] with %h
    imodintro
    ipureintro
    rw [State.get?_toMap] at h
    simp [State.stringPart?, State.string?, h]
  | _ =>
    simp only [StringPart]
    iintro ⟨-, %h⟩
    imodintro
    ipureintro
    exact h

omit Γ in
/--
The ghost heap agrees with `StringParts`: given the ghost heap's interpretation of the state
(`genHeapInterp σ.toMap`), if `cus` are the string forms of `vs` according to the logic
(`StringParts vs cus`), then they are in the state too (`vs.mapM σ.stringPart? = some cus`).
-/
public theorem StringParts.valid {σ : State} {vs : List Value} {cus : List (List UInt16)} :
    genHeapInterp σ.toMap ∗ StringParts (GF := GF) vs cus ⊢
      |==> ⌜vs.mapM σ.stringPart? = some cus⌝ := by
  induction vs generalizing cus with
  | nil =>
    cases cus with
    | nil =>
      iintro -
      imodintro
      ipureintro
      rfl
    | cons cu cus =>
      simp only [StringParts]
      iintro ⟨-, %h⟩
      exact h.elim
  | cons v vs ih =>
    cases cus with
    | nil =>
      simp only [StringParts]
      iintro ⟨-, %h⟩
      exact h.elim
    | cons cu cus =>
      simp only [StringParts]
      iintro ⟨Hσ, #Hv, #Hvs⟩
      ihave %h₁ : ⌜σ.stringPart? v = some cu⌝ $$ [Hσ Hv]
      · ihave >%h := StringPart.valid $$ [$Hσ $Hv]
        ipureintro
        exact h
      ihave >%h₂ := ih $$ [$Hσ $Hvs]
      imodintro
      ipureintro
      simp [List.mapM_cons, h₁, h₂]

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
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
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
  isplitl [Hh Hc]
  · iframe Hh
    iframe Hc
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
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
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
  have hc : (if startsNull then .val .null else .uninit : Cell).isVar = true := by
    cases startsNull <;> rfl
  ihave #Hhdr' := ObjectHeaders.alloc (GF := GF) (σ := σ₁) hc $$ Hhdr
  imodintro
  isplitl [Hh Hc]
  · rw [State.toMap_alloc]
    iframe Hh
    iframe Hhdr'
    rw [State.constants_alloc]
    iexact Hc
  isplitl
  · iapply H $$ Hl
  · isimp
    itrivial

/--
A let expression whose initializer has evaluated to `w` allocates a cell for its variable `v`,
holding `w`, and continues with its body `m₂`, with `v` resolved to the cell: it satisfies a
postcondition `Φ` if, one step later (`▷`), for every location `ℓ`, given the ownership of a cell
at `ℓ` holding `w` (`ℓ ↦ .val w`), the body with `v` resolved to `ℓ` satisfies `Φ`
(`WP (m₂.resolve v ℓ) {{ Φ }}`). (Before the initializer has evaluated, the let expression is an
evaluation context item, `EctxItem.letIn`, so `wp_bind_item` applies.)
-/
public theorem wp_letIn {v : Variable} {w : Value} {m₂ : LoweredExpr} :
    ▷ (∀ ℓ, ℓ ↦ (.val w : Cell) -∗ WP (m₂.resolve v ℓ) @ s; E {{ Φ }}) ⊢
      WP (LoweredExpr.letIn v (.val w) m₂) @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_base_step rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], _, _, [], .letIn, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs .letIn
  imod Hclose
  have hfresh : get? σ₁.toMap σ₁.fresh = none := by rw [State.get?_toMap, State.lookup_fresh]
  imod genHeap_alloc (v := (.val w : Cell)) hfresh $$ Hh with ⟨Hh, Hl, -⟩
  ihave #Hhdr' := ObjectHeaders.alloc (GF := GF) (σ := σ₁) (c := .val w) rfl $$ Hhdr
  imodintro
  isplitl [Hh Hc]
  · rw [State.toMap_alloc]
    iframe Hh
    iframe Hhdr'
    rw [State.constants_alloc]
    iexact Hc
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
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
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
  isplitl [Hh Hc]
  · iframe Hh
    iframe Hc
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
    (hc : c.isVar = true) (hfin : x.isFinal = true → c = .uninit) :
    ▷ (ℓ ↦ c) ∗ ▷ ((ℓ ↦ (.val w : Cell)) -∗ Φ (.normal w)) ⊢
      WP (LoweredExpr.variableSetAt x ℓ (.val w)) @ s; E {{ Φ }} := by
  iintro ⟨>Hl, HΦ⟩
  iapply wp_lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
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
  ihave #Hhdr' := ObjectHeaders.update (c := (.val w : Cell)) Hlook hc rfl
    $$ Hhdr
  imodintro
  isplit
  · itrivial
  isplitl [Hh Hc]
  · rw [State.toMap_update Hlook]
    iframe Hh
    iframe Hhdr'
    rw [State.constants_update]
    iexact Hc
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
public theorem wp_propertyGet_field {ℓ ℓf : Loc} {p : Property} {k iv : String} {T C S : τ}
    {fs : List (String × Loc)} {dq : DFrac} {w : Value}
    (hd : P.dispatch k p.name = some (.field iv)) (hf : fs.lookup iv = some ℓf) (hST : S ≤ T) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗ HasDynamicType w S ∗ ▷ (ℓf ↦{dq} (.val w : Cell)) ∗
        ▷ ((ℓf ↦{dq} (.val w : Cell)) -∗ Φ (.normal w)) ⊢
      WP (LoweredExpr.propertyGet (.val (.obj ℓ)) p T) @ s; E {{ Φ }} := by
  iintro ⟨#Hobj, #Hty, >Hl, HΦ⟩
  iapply wp_lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
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
  isplitl [Hh Hc]
  · iframe Hh
    iframe Hc
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
      rfl $$ Hhdr
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
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, Hhdr, Hc⟩
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
  imod allocAll_vals σ₁ vs $$ [$Hh $Hhdr] with ⟨Hσ, Hls⟩
  imodintro
  isplitl [Hσ Hc]
  · icases Hσ with ⟨Hh, Hhdr⟩
    iframe Hh
    iframe Hhdr
    simp only [State.constants_allocAll]
    iexact Hc
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
  exact .checkEqPass (State.primEq?_of_value h)

/--
An intrinsic equality check whose operands `v₁` and `v₂` are different (`h`) throws: it satisfies
a postcondition `Φ` that holds, one step later, of throwing
(`▷ Φ (.throwing (.error .expectFailed))`).
-/
public theorem wp_checkEq_fail {v₁ v₂ : Value} (h : Value.primEq? v₁ v₂ = some false) :
    ▷ Φ (.throwing (.error .expectFailed)) ⊢
      WP (LoweredExpr.checkEq (.val v₁) (.val v₂)) @ s; E {{ Φ }} := by
  refine wp_pure_step_throwing (by rfl) fun _ => ?_
  exact .checkEqFail (State.primEq?_of_value h)

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
  exact .primEq (State.primEq?_of_value h)

/-! ### Objects -/

omit Γ P in
/--
Allocating an uninitialized cell for each of `names` (`σ.allocAll (names.map fun _ => .uninit)`),
as an instance creation does for the new object's instance variables, can be mirrored in the ghost
state: given the state interpretation for `σ`, a basic update gives the state interpretation for
the state afterwards, and the ownership of the new cells (`PointsToUninit …`).
-/
public theorem allocAll_uninit (σ : State) (names : List String) :
    genHeapInterp σ.toMap ∗ ObjectHeaders (GF := GF) σ ⊢
      |==> ((genHeapInterp (σ.allocAll (names.map fun _ => .uninit)).2.toMap ∗
        ObjectHeaders (σ.allocAll (names.map fun _ => .uninit)).2) ∗
        PointsToUninit (τ := τ) (σ.allocAll (names.map fun _ => .uninit)).1) := by
  induction names generalizing σ with
  | nil =>
    simp only [List.map_nil, State.allocAll, PointsToUninit]
    iintro ⟨Hh, Hhdr⟩
    imodintro
    isplitl
    · isplitl [Hh]
      · iexact Hh
      · iexact Hhdr
    · itrivial
  | cons n names ih =>
    have hfresh : get? σ.toMap σ.fresh = none := by rw [State.get?_toMap, State.lookup_fresh]
    have ih' := ih (σ.alloc .uninit)
    rw [State.toMap_alloc] at ih'
    simp only [List.map_cons, State.allocAll, PointsToUninit]
    iintro ⟨Hh, #Hhdr⟩
    imod genHeap_alloc (v := (.uninit : Cell)) hfresh $$ Hh with ⟨Hh, Hl, -⟩
    ihave #Hhdr' := ObjectHeaders.alloc (GF := GF) (σ := σ) (c := .uninit)
      rfl $$ Hhdr
    imod ih' $$ [$Hh $Hhdr'] with ⟨Hrest, Hls⟩
    imodintro
    isplitl [Hrest]
    · iexact Hrest
    · isplitl [Hl]
      · iexact Hl
      · iexact Hls

omit Γ P in
/--
Allocating an object (`σ.allocObject cls T names`) can be mirrored in the ghost state: given the
state interpretation for `σ`, a basic update gives the state interpretation for the state
afterwards, a persistent points-to for the object's own cell, the ownership of the cells of its
instance variables, all uninitialized (`PointsToUninit ℓs`), and that there's one such cell per
instance variable (`ℓs.length = names.length`).
-/
public theorem allocObject_ghost (σ : State) (cls : String) (T : τ) (names : List String) :
    genHeapInterp σ.toMap ∗ ObjectHeaders (GF := GF) σ ⊢
      |==> ((genHeapInterp (σ.allocObject cls T names).2.toMap ∗
        ObjectHeaders (σ.allocObject cls T names).2) ∗
        ∃ ℓs, (σ.allocObject cls T names).1 ↦{.discard}
          (.object cls T (names.zip ℓs) : Cell) ∗ PointsToUninit (τ := τ) ℓs ∗
          ⌜ℓs.length = names.length⌝) := by
  simp only [State.allocObject]
  iintro Hσ
  imod allocAll_uninit σ names $$ Hσ with ⟨⟨Hh, #Hhdr⟩, Hls⟩
  have hfresh : get? (σ.allocAll (names.map fun _ => .uninit)).2.toMap
      (σ.allocAll (names.map fun _ => .uninit)).2.fresh = none := by
    rw [State.get?_toMap, State.lookup_fresh]
  imod genHeap_alloc
    (v := (.object cls T (names.zip (σ.allocAll (names.map fun _ => .uninit)).1) : Cell)) hfresh
    $$ Hh with ⟨Hh, Hl, -⟩
  imod pointsTo_persist $$ Hl with #Hl
  ihave #Hhdr' := ObjectHeaders.alloc_object (GF := GF)
    (σ := (σ.allocAll (names.map fun _ => .uninit)).2) (k := cls) (C := T)
    (fs := names.zip (σ.allocAll (names.map fun _ => .uninit)).1) $$ [$Hhdr $Hl]
  imodintro
  isplitl [Hh]
  · rw [State.toMap_alloc]
    iframe Hh
    iexact Hhdr'
  · iexists (σ.allocAll (names.map fun _ => .uninit)).1
    isplitr
    · iexact Hl
    isplitl
    · iexact Hls
    · ipureintro
      simp

/--
`e` satisfies a postcondition `Φ` if, one step later, for all locations `ℓs`, given the ownership of
cells at `ℓs` holding `vs` (`PointsToVals ℓs vs`), `e' ℓs` satisfies `Φ`, provided:
- `e` hasn't completed (`hv`); and
- in every state `σ`, `e` takes a head step that allocates a cell for each of `vs`, to `e' ℓs`,
  where `ℓs` are the new cells' locations (`h`).

(Calls of members take such steps, allocating cells for `this` and the formal parameters.)
-/
public theorem wp_step_alloc {e : LoweredExpr} {vs : List Value} {e' : List Loc → LoweredExpr}
    (hv : e.toOutcome? = none)
    (h : ∀ σ, HeadStep e σ (e' (σ.allocAll (vs.map Cell.val)).1) (σ.allocAll (vs.map Cell.val)).2) :
    ▷ (∀ ℓs, PointsToVals ℓs vs -∗ WP (e' ℓs) @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_base_step hv
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, Hhdr, Hc⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], _, _, [], h σ₁, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs (h σ₁)
  imod Hclose
  imod allocAll_vals σ₁ vs $$ [$Hh $Hhdr] with ⟨Hσ, Hls⟩
  imodintro
  isplitl [Hσ Hc]
  · icases Hσ with ⟨Hh, Hhdr⟩
    iframe Hh
    iframe Hhdr
    simp only [State.constants_allocAll]
    iexact Hc
  isplitl
  · iapply H $$ Hls
  · isimp
    itrivial

/--
`wp_step_alloc` for a step that also depends on the object at `ℓ` (`ℓ ↦{.discard} .object k C fs`,
its own cell, which never changes): `h` need only hold in states where the cell at `ℓ` is that.
-/
public theorem wp_step_alloc_of_header {e : LoweredExpr} {ℓ : Loc} {k : String} {C : τ}
    {fs : List (String × Loc)} {vs : List Value} {e' : List Loc → LoweredExpr}
    (hv : e.toOutcome? = none)
    (h : ∀ σ, σ.lookup ℓ = some (.object k C fs) →
      HeadStep e σ (e' (σ.allocAll (vs.map Cell.val)).1) (σ.allocAll (vs.map Cell.val)).2) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗
        ▷ (∀ ℓs, PointsToVals ℓs vs -∗ WP (e' ℓs) @ s; E {{ Φ }}) ⊢
      WP e @ s; E {{ Φ }} := by
  iintro ⟨#Hobj, H⟩
  iapply wp_lift_base_step hv
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, Hhdr, Hc⟩
  ihave %Hobjl : ⌜σ₁.lookup ℓ = some (.object k C fs)⌝ $$ [Hh Hobj]
  · ihave >%Hv := genHeap_valid $$ [$Hh $Hobj]
    ipureintro
    rwa [State.get?_toMap] at Hv
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], _, _, [], h σ₁ Hobjl, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs (h σ₁ Hobjl)
  imod Hclose
  imod allocAll_vals σ₁ vs $$ [$Hh $Hhdr] with ⟨Hσ, Hls⟩
  imodintro
  isplitl [Hσ Hc]
  · icases Hσ with ⟨Hh, Hhdr⟩
    iframe Hh
    iframe Hhdr
    simp only [State.constants_allocAll]
    iexact Hc
  isplitl
  · iapply H $$ Hls
  · isimp
    itrivial

/--
`e` satisfies a postcondition `Φ`, by a step that stores `w` in the cell at `ℓf`, if:
- the cell at `ℓf` holds `c`, which isn't an object's own cell (`hc`), and is owned one step later
  (`▷ ℓf ↦ c`);
- one step later, given the ownership of the cell at `ℓf`, now holding `w`, `e'` satisfies `Φ`
  (`▷ (ℓf ↦ .val w -∗ WP e' {{ Φ }})`);
- `e` hasn't completed (`hv`); and
- in every state in which the cell at `ℓ` is the object's own cell `.object k C fs`, of which the
  logic has a persistent points-to (`ℓ ↦{.discard} .object k C fs`), and the cell at `ℓf` holds
  `c`, `e` takes a head step to `e'` that stores `w` in the cell at `ℓf` (`h`).

(Initializers of instance variables, and assignments through their implicit setters, take such
steps.)
-/
public theorem wp_store_of_header {e e' : LoweredExpr} {ℓ ℓf : Loc} {k : String} {C : τ}
    {fs : List (String × Loc)} {c : Cell} {w : Value} (hv : e.toOutcome? = none)
    (hc : c.isVar = true)
    (h : ∀ σ, σ.lookup ℓ = some (.object k C fs) → σ.lookup ℓf = some c →
      HeadStep e σ e' (σ.update ℓf (.val w))) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗ ▷ (ℓf ↦ c) ∗
        ▷ ((ℓf ↦ (.val w : Cell)) -∗ WP e' @ s; E {{ Φ }}) ⊢
      WP e @ s; E {{ Φ }} := by
  iintro ⟨#Hobj, >Hl, H⟩
  iapply wp_lift_base_step hv
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
  ihave %Hobjl : ⌜σ₁.lookup ℓ = some (.object k C fs)⌝ $$ [Hh Hobj]
  · ihave >%Hv := genHeap_valid $$ [$Hh $Hobj]
    ipureintro
    rwa [State.get?_toMap] at Hv
  ihave %Hlook : ⌜σ₁.lookup ℓf = some c⌝ $$ [Hh Hl]
  · ihave >%Hv := genHeap_valid $$ [$Hh $Hl]
    ipureintro
    rwa [State.get?_toMap] at Hv
  have hstep := h σ₁ Hobjl Hlook
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], _, _, [], hstep, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs hstep
  imod Hclose
  imod genHeap_update (σ := σ₁.toMap) (l := ℓf) (v₁ := c) (v₂ := (.val w : Cell)) $$ [$Hh $Hl]
    with ⟨Hh, Hl⟩
  ihave #Hhdr' := ObjectHeaders.update (c := (.val w : Cell)) Hlook hc
    rfl $$ Hhdr
  imodintro
  isplitl [Hh Hc]
  · rw [State.toMap_update Hlook]
    iframe Hh
    iframe Hhdr'
    rw [State.constants_update]
    iexact Hc
  isplitl
  · iapply H $$ Hl
  · isimp
    itrivial

/--
An instance creation by constructor `k`, whose arguments have evaluated to `vs`, allocates a new
object and runs the constructor on it. It satisfies a postcondition `Φ` if:
- the constructor table declares `k` as `d` (`hk`), and the class table declares its class as `c`
  (`hc`); and
- one step later (`▷`), for the new object's own cell at some `ℓ`, recording the class's instance
  variables at some locations `ℓs` (`ℓ ↦{.discard} .object d.cls c.type (c.instanceVariables.zip
  ℓs)`), one per instance variable (`⌜ℓs.length = c.instanceVariables.length⌝`), given the
  ownership of their cells, all uninitialized (`PointsToUninit ℓs`), running the constructor on the
  object and then evaluating to it satisfies `Φ`.
-/
public theorem wp_new {k : String} {d : ConstructorDecl (τ := τ)} {c : ClassDecl (τ := τ)}
    {vs : List Value} {T : τ} (hk : P.constructors k = some d) (hc : P.classes d.cls = some c) :
    ▷ (∀ ℓ ℓs, ⌜ℓs.length = c.instanceVariables.length⌝ -∗
        ℓ ↦{.discard} (.object d.cls c.type (c.instanceVariables.zip ℓs) : Cell) -∗
        PointsToUninit (τ := τ) ℓs -∗
        WP (LoweredExpr.seq (.ctorRun ℓ k vs) (.val (.obj ℓ))) @ s; E {{ Φ }}) ⊢
      WP (LoweredExpr.new k (vs.map .val) T) @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_base_step rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, Hhdr, Hc⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], _, _, [], .new hk hc, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs (.new hk hc)
  imod Hclose
  imod allocObject_ghost σ₁ d.cls c.type c.instanceVariables $$ [$Hh $Hhdr] with
    ⟨Hσ, %ℓs, #Ho, Hls, %hlen⟩
  imodintro
  isplitl [Hσ Hc]
  · icases Hσ with ⟨Hh, Hhdr⟩
    iframe Hh
    iframe Hhdr
    simp only [State.constants_allocObject]
    iexact Hc
  isplitl
  · iapply H $$ %_ %ℓs %hlen Ho Hls
  · isimp
    itrivial

/--
Running constructor `k` on the object at `ℓ`, with argument values `vs`, allocates a cell for `this`
and for each formal parameter, and runs the initializers and the body. It satisfies a postcondition
`Φ` if:
- the constructor table declares `k` as `d` (`hk`), with one formal parameter per argument
  (`hlen`); and
- one step later (`▷`), for all locations `ℓs`, given the ownership of cells at `ℓs` holding the
  object and the arguments (`PointsToVals ℓs (.obj ℓ :: vs)`), the initializers and body, with
  `this` and the formal parameters bound to those cells (see `SemanticParams.memberBody`), run as
  the body of a running constructor, satisfy `Φ`.
-/
public theorem wp_ctorRun {ℓ : Loc} {k : String} {d : ConstructorDecl (τ := τ)} {vs : List Value}
    (hk : P.constructors k = some d) (hlen : d.params.length = vs.length) :
    ▷ (∀ ℓs, PointsToVals ℓs (.obj ℓ :: vs) -∗
        WP (LoweredExpr.ctorFrame (P.memberBody k d.cls (d.this :: d.params)
          (.block (d.initializers ++ [d.body])) ℓs)) @ s; E {{ Φ }}) ⊢
      WP (LoweredExpr.ctorRun ℓ k vs) @ s; E {{ Φ }} :=
  wp_step_alloc (e' := fun ℓs => .ctorFrame (P.memberBody k d.cls (d.this :: d.params)
    (.block (d.initializers ++ [d.body])) ℓs)) rfl fun _ => .ctorRun hk hlen

/--
A `super(args)` or `this(args)` call in an initializer list, whose receiver is the object at `ℓ` and
whose arguments have evaluated to `vs`, runs constructor `k` on the object: it satisfies a
postcondition `Φ` if running the constructor does, one step later
(`▷ WP (.ctorRun ℓ k vs) {{ Φ }}`).
-/
public theorem wp_initCtor {ℓ : Loc} {k : String} {vs : List Value} :
    ▷ WP (LoweredExpr.ctorRun ℓ k vs) @ s; E {{ Φ }} ⊢
      WP (LoweredExpr.initCtor (.val (.obj ℓ)) k (vs.map .val)) @ s; E {{ Φ }} :=
  wp_pure_step rfl fun _ => .initCtor

/--
What the initializers and body of a running constructor must guarantee about their outcome `o`,
for the constructor to satisfy a postcondition `Φ`: that `Φ` holds, one step later, of the
constructor's outcome. Completing normally, and a return, become completing normally with the null
object, and an exception propagates. A break can't propagate out of a constructor's body (it gets
stuck there), so the body must not complete with one (`False`).
-/
@[expose, simp]
public def ctorFramePost (Φ : DartLang.Outcome (τ := τ) → IProp GF) :
    DartLang.Outcome (τ := τ) → IProp GF
  | .normal _ => iprop(▷ Φ (.normal .null))
  | .returning _ => iprop(▷ Φ (.normal .null))
  | .throwing v => iprop(▷ Φ (.throwing v))
  | .breaking _ => iprop(False)

/--
The initializers and body `m` of a running constructor: `.ctorFrame m` satisfies a postcondition
`Φ` if `m` satisfies the postcondition that `Φ` holds, one step later, of the constructor's
outcome, for each outcome of `m` (`WP m {{ o, ctorFramePost Φ o }}`).
-/
public theorem wp_ctorFrame {m : LoweredExpr} :
    WP m @ s; E {{ o, ctorFramePost Φ o }} ⊢ WP (LoweredExpr.ctorFrame m) @ s; E {{ Φ }} := by
  refine (wp_mono fun o => ?_).trans (wp_bind_item .ctorFrame)
  cases o with
  | normal v => exact wp_pure_step_val (by rfl) fun _ => .ctorFrameVal
  | returning v => exact wp_pure_step_val (by rfl) fun _ => .ctorFrameReturning
  | throwing v => exact wp_bubble_exception .ctorFrame v
  | breaking l => exact false_elim

/--
An initializer of the instance variable whose key is `name` of the object at `ℓ` stores `w` in its
cell. It satisfies a postcondition `Φ` if:
- the object's own cell records its instance variables `fs`
  (`ℓ ↦{.discard} .object k C fs`), among them one with key `name` at `ℓf` (`hf`);
- one step later, the cell at `ℓf` is owned (`▷ ℓf ↦ c`), and `c` isn't an object's own cell
  (`hc`); and
- one step later, `Φ` holds of completing normally with the null object, given the ownership of the
  cell, now holding `w` (`▷ (ℓf ↦ .val w -∗ Φ (.normal .null))`).
-/
public theorem wp_initField {ℓ ℓf : Loc} {name k : String} {C : τ} {fs : List (String × Loc)}
    {c : Cell} {w : Value} (hf : fs.lookup name = some ℓf) (hc : c.isVar = true) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗ ▷ (ℓf ↦ c) ∗
        ▷ ((ℓf ↦ (.val w : Cell)) -∗ Φ (.normal .null)) ⊢
      WP (LoweredExpr.initField (.val (.obj ℓ)) name (.val w)) @ s; E {{ Φ }} := by
  iintro ⟨#Hobj, Hl, HΦ⟩
  iapply wp_store_of_header (ℓ := ℓ) (k := k) (C := C) (fs := fs) (e' := .val .null) rfl hc
    fun σ hσ hℓf =>
    .initField (k := k) (fs := fs) (by simp [State.object?, hσ]) hf hℓf hc
  isplitr
  · iexact Hobj
  isplitl [Hl]
  · iexact Hl
  · inext
    iintro Hl
    iapply wp_val
    iapply HΦ $$ Hl

/--
An assignment of `w` to property `name` of the object at `ℓ`, whose class `k` dispatches the setter
`name=` to the implicit setter of the instance variable whose key is `iv` (`hd`), stores `w` in that
instance variable's cell (at `ℓf`; `hf`), and evaluates to `w`. It satisfies a postcondition `Φ`
under the same conditions as `wp_initField`, with `Φ (.normal w)` in place of `Φ (.normal .null)`.
-/
public theorem wp_propertySet_field {ℓ ℓf : Loc} {name k iv : String} {C : τ}
    {fs : List (String × Loc)} {c : Cell} {w : Value}
    (hd : P.dispatch k (name ++ "=") = some (.field iv)) (hf : fs.lookup iv = some ℓf)
    (hc : c.isVar = true) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗ ▷ (ℓf ↦ c) ∗
        ▷ ((ℓf ↦ (.val w : Cell)) -∗ Φ (.normal w)) ⊢
      WP (LoweredExpr.propertySet (.val (.obj ℓ)) name (.val w)) @ s; E {{ Φ }} := by
  iintro ⟨#Hobj, Hl, HΦ⟩
  iapply wp_store_of_header (ℓ := ℓ) (k := k) (C := C) (fs := fs) (e' := .val w) rfl hc
    fun σ hσ hℓf =>
    .propertySetField (k := k) (fs := fs) (by simp [State.object?, hσ]) hd hf hℓf hc
  isplitr
  · iexact Hobj
  isplitl [Hl]
  · iexact Hl
  · inext
    iintro Hl
    iapply wp_val
    iapply HΦ $$ Hl

/--
An assignment of `w` to property `name` of the object at `ℓ`, whose class `k` dispatches the setter
`name=` to a setter that is user code (`hd`, `hm`, with one formal parameter: `hlen`), runs the
setter, and then evaluates to `w`. It satisfies a postcondition `Φ` if:
- the object's own cell records its class `k` (`ℓ ↦{.discard} .object k C fs`); and
- one step later (`▷`), for all locations `ℓs`, given the ownership of cells at `ℓs` holding the
  object and `w` (`PointsToVals ℓs [.obj ℓ, w]`), running the setter's body (see
  `SemanticParams.memberBody`), and then evaluating to `w`, satisfies `Φ`.
-/
public theorem wp_propertySet_setter {ℓ : Loc} {name k key holder : String} {C : τ}
    {fs : List (String × Loc)} {d : MemberDecl (τ := τ)} {w : Value}
    (hd : P.dispatch k (name ++ "=") = some (.proc key holder)) (hm : P.members key = some d)
    (hlen : d.params.length = 1) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗
        ▷ (∀ ℓs, PointsToVals ℓs [.obj ℓ, w] -∗
          WP (LoweredExpr.seq (.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs)
            Γ.Null) (.val w)) @ s; E {{ Φ }}) ⊢
      WP (LoweredExpr.propertySet (.val (.obj ℓ)) name (.val w)) @ s; E {{ Φ }} :=
  wp_step_alloc_of_header (e' := fun ℓs => .seq (.frame (P.memberBody key holder
    (d.this :: d.params) d.body ℓs) Γ.Null) (.val w)) rfl fun _ hσ =>
    .propertySetSetter (fs := fs) (by simp [State.object?, hσ]) hd hm hlen

/--
A method call on the object at `ℓ`, whose arguments have evaluated to `vs`, where the object's
class `k` dispatches the method's name to member `key`, provided by class `holder` (`hd`), declared
as `d` (`hm`) with one formal parameter per argument (`hlen`), runs the method's body. It satisfies
a postcondition `Φ` if:
- the object's own cell records its class `k` (`ℓ ↦{.discard} .object k C fs`); and
- one step later (`▷`), for all locations `ℓs`, given the ownership of cells at `ℓs` holding the
  object and the arguments (`PointsToVals ℓs (.obj ℓ :: vs)`), the body, with `this` and the formal
  parameters bound to those cells (see `SemanticParams.memberBody`), run as the body of a running
  call, satisfies `Φ`.

As for `wp_call`, the `▷` is what makes recursive methods provable (see `MemberSpec.intro`).
-/
public theorem wp_methodCall {ℓ : Loc} {name k key holder : String} {C : τ}
    {fs : List (String × Loc)} {d : MemberDecl (τ := τ)} {vs : List Value} {T : τ}
    (hd : P.dispatch k name = some (.proc key holder)) (hm : P.members key = some d)
    (hlen : d.params.length = vs.length) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗
        ▷ (∀ ℓs, PointsToVals ℓs (.obj ℓ :: vs) -∗
          WP (LoweredExpr.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs) T) @ s;
            E {{ Φ }}) ⊢
      WP (LoweredExpr.methodCall (.val (.obj ℓ)) name (vs.map .val) T) @ s; E {{ Φ }} :=
  wp_step_alloc_of_header (e' := fun ℓs => .frame (P.memberBody key holder (d.this :: d.params)
    d.body ℓs) T) rfl fun _ hσ => .methodCall (fs := fs) (by simp [State.object?, hσ])
    hd hm hlen

/--
A super method call with receiver `v`, whose slot has been filled in with `sup` and whose arguments
have evaluated to `vs`, where `sup` dispatches the method's name to member `key`, provided by class
`holder` (`hd`), declared as `d` (`hm`) with one formal parameter per argument (`hlen`), runs the
method's body with `v` as `this`. It satisfies a postcondition `Φ` if, one step later, the body
does, as for `wp_methodCall`.
-/
public theorem wp_superCall {v : Value} {name sup key holder : String} {d : MemberDecl (τ := τ)}
    {vs : List Value} {T : τ} (hd : P.dispatch sup name = some (.proc key holder))
    (hm : P.members key = some d) (hlen : d.params.length = vs.length) :
    ▷ (∀ ℓs, PointsToVals ℓs (v :: vs) -∗
        WP (LoweredExpr.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs) T) @ s;
          E {{ Φ }}) ⊢
      WP (LoweredExpr.superCall (.val v) name (some sup) (vs.map .val) T) @ s; E {{ Φ }} :=
  wp_step_alloc (e' := fun ℓs => .frame (P.memberBody key holder (d.this :: d.params) d.body ℓs)
    T) rfl fun _ => .superCall hd hm hlen

/--
Reading property `p` of the object at `ℓ`, whose class `k` dispatches the property's name to a
getter that is user code (`hd`, `hm`, with no formal parameters: `hlen`), runs the getter's body,
and then checks the result against the property's (possibly promoted) static type `T`. It satisfies
a postcondition `Φ` if:
- the object's own cell records its class `k` (`ℓ ↦{.discard} .object k C fs`); and
- one step later (`▷`), for all locations `ℓs`, given the ownership of a cell at `ℓs` holding the
  object (`PointsToVals ℓs [.obj ℓ]`), the body, with `this` bound to that cell, run as the body of
  a running call, and then the promotion check (`checkPromotion`), satisfy `Φ`.
-/
public theorem wp_propertyGet_getter {ℓ : Loc} {p : Property} {k key holder : String} {C T : τ}
    {fs : List (String × Loc)} {d : MemberDecl (τ := τ)}
    (hd : P.dispatch k p.name = some (.proc key holder)) (hm : P.members key = some d)
    (hlen : d.params.length = 0) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗
        ▷ (∀ ℓs, PointsToVals ℓs [(.obj ℓ : Value)] -∗
          WP (LoweredExpr.checkPromotion T
            (.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs) T)) @ s;
            E {{ Φ }}) ⊢
      WP (LoweredExpr.propertyGet (.val (.obj ℓ)) p T) @ s; E {{ Φ }} :=
  wp_step_alloc_of_header (e' := fun ℓs => .checkPromotion T (.frame (P.memberBody key holder
    (d.this :: d.params) d.body ℓs) T)) rfl fun _ hσ =>
    .propertyGetGetter (fs := fs) (by simp [State.object?, hσ]) hd hm hlen

/--
Reading property `name` with `super`, with the receiver the object at `ℓ`, whose slot has been
filled in with `sup`, where `sup` dispatches `name` to the implicit getter of the instance variable
whose key is `iv` (`hd`), reads that instance variable of the object (at `ℓf`; `hf`), as
`wp_propertyGet_field` does.
-/
public theorem wp_superGet_field {ℓ ℓf : Loc} {name sup k iv : String} {T C S : τ}
    {fs : List (String × Loc)} {dq : DFrac} {w : Value}
    (hd : P.dispatch sup name = some (.field iv)) (hf : fs.lookup iv = some ℓf) (hST : S ≤ T) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗ HasDynamicType w S ∗ ▷ (ℓf ↦{dq} (.val w : Cell)) ∗
        ▷ ((ℓf ↦{dq} (.val w : Cell)) -∗ Φ (.normal w)) ⊢
      WP (LoweredExpr.superGet (.val (.obj ℓ)) name (some sup) T) @ s; E {{ Φ }} := by
  iintro ⟨#Hobj, #Hty, >Hl, HΦ⟩
  iapply wp_lift_atomic_base_step_no_fork rfl
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
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
  have hstep : HeadStep (LoweredExpr.superGet (.val (.obj ℓ)) name (some sup) T) σ₁ (.val w) σ₁ :=
    .superGetField hd hobj hf Hlook (.of_le Hdt hST)
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
  isplitl [Hh Hc]
  · iframe Hh
    iframe Hc
    iexact Hhdr
  iexists .normal w
  isplit
  · ipureintro
    rfl
  · iapply HΦ $$ Hl

/--
Reading property `name` with `super`, with receiver `v`, whose slot has been filled in with `sup`,
where `sup` dispatches `name` to a getter that is user code (`hd`, `hm`, `hlen`), runs the getter
with `v` as `this`. It satisfies a postcondition `Φ` if, one step later, the getter's body and the
promotion check do, as for `wp_propertyGet_getter`.
-/
public theorem wp_superGet_getter {v : Value} {name sup key holder : String} {T : τ}
    {d : MemberDecl (τ := τ)} (hd : P.dispatch sup name = some (.proc key holder))
    (hm : P.members key = some d) (hlen : d.params.length = 0) :
    ▷ (∀ ℓs, PointsToVals ℓs [v] -∗
        WP (LoweredExpr.checkPromotion T
          (.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs) T)) @ s; E {{ Φ }}) ⊢
      WP (LoweredExpr.superGet (.val v) name (some sup) T) @ s; E {{ Φ }} :=
  wp_step_alloc (e' := fun ℓs => .checkPromotion T (.frame (P.memberBody key holder
    (d.this :: d.params) d.body ℓs) T)) rfl fun _ => .superGetGetter hd hm hlen

/--
An assignment of `w` to property `name` with `super`, with the receiver the object at `ℓ`, whose
slot has been filled in with `sup`, where `sup` dispatches the setter `name=` to the implicit
setter of the instance variable whose key is `iv` (`hd`), stores `w` in that instance variable of
the object (at `ℓf`; `hf`), as `wp_propertySet_field` does.
-/
public theorem wp_superSet_field {ℓ ℓf : Loc} {name sup k iv : String} {C : τ}
    {fs : List (String × Loc)} {c : Cell} {w : Value}
    (hd : P.dispatch sup (name ++ "=") = some (.field iv)) (hf : fs.lookup iv = some ℓf)
    (hc : c.isVar = true) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗ ▷ (ℓf ↦ c) ∗
        ▷ ((ℓf ↦ (.val w : Cell)) -∗ Φ (.normal w)) ⊢
      WP (LoweredExpr.superSet (.val (.obj ℓ)) name (some sup) (.val w)) @ s; E {{ Φ }} := by
  iintro ⟨#Hobj, Hl, HΦ⟩
  iapply wp_store_of_header (ℓ := ℓ) (k := k) (C := C) (fs := fs) (e' := .val w) rfl hc
    fun σ hσ hℓf =>
    .superSetField (k := k) (fs := fs) hd (by simp [State.object?, hσ]) hf hℓf
    hc
  isplitr
  · iexact Hobj
  isplitl [Hl]
  · iexact Hl
  · inext
    iintro Hl
    iapply wp_val
    iapply HΦ $$ Hl

/--
An assignment of `w` to property `name` with `super`, with receiver `v`, whose slot has been filled
in with `sup`, where `sup` dispatches the setter `name=` to a setter that is user code (`hd`, `hm`,
`hlen`), runs the setter with `v` as `this`, and then evaluates to `w`. It satisfies a postcondition
`Φ` if, one step later, the setter's body and then evaluating to `w` do, as for
`wp_propertySet_setter`.
-/
public theorem wp_superSet_setter {v w : Value} {name sup key holder : String}
    {d : MemberDecl (τ := τ)} (hd : P.dispatch sup (name ++ "=") = some (.proc key holder))
    (hm : P.members key = some d) (hlen : d.params.length = 1) :
    ▷ (∀ ℓs, PointsToVals ℓs [v, w] -∗
        WP (LoweredExpr.seq (.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs)
          Γ.Null) (.val w)) @ s; E {{ Φ }}) ⊢
      WP (LoweredExpr.superSet (.val v) name (some sup) (.val w)) @ s; E {{ Φ }} :=
  wp_step_alloc (e' := fun ℓs => .seq (.frame (P.memberBody key holder (d.this :: d.params) d.body
    ℓs) Γ.Null) (.val w)) rfl fun _ => .superSetSetter hd hm hlen

/--
The promotion check of a getter's result `w` against type `T` passes if `w`'s dynamic type is `S`
(`HasDynamicType w S`), a subtype of `T` (`hST`): it satisfies a postcondition `Φ` that holds, one
step later, of completing normally with `w` (`▷ Φ (.normal w)`).
-/
public theorem wp_checkPromotion {w : Value} {S T : τ} (hST : S ≤ T) :
    HasDynamicType w S ∗ ▷ Φ (.normal w) ⊢
      WP (LoweredExpr.checkPromotion T (.val w)) @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_step_of_dynamicType (v := w) (S := S) rfl fun _ hS =>
    .checkPromotion (.of_le hS hST))
  iintro ⟨#Hty, HΦ⟩
  isplitr
  · iexact Hty
  · inext
    iapply wp_val
    iexact HΦ

/--
`identical` of values `v₁` and `v₂` that can be compared evaluates to whether they're the same
object (`h`; see `Value.identical?`): it satisfies a postcondition `Φ` that holds, one step later,
of completing normally with that boolean (`▷ Φ (.normal (.bool b))`).
-/
public theorem wp_identical {v₁ v₂ : Value} {b : Bool} (h : Value.identical? v₁ v₂ = some b) :
    ▷ Φ (.normal (.bool b)) ⊢ WP (LoweredExpr.identical (.val v₁) (.val v₂)) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .identical h

/-! ### Strings and constants -/

/--
A constant whose value is the null object, a boolean or an integer `v` (`h`) evaluates to it: it
satisfies a postcondition `Φ` that holds, one step later, of completing normally with `v`
(`▷ Φ (.normal v)`).
-/
public theorem wp_constant_prim {c : ConstValue} {v : Value} (h : c.prim? (τ := τ) = some v) :
    ▷ Φ (.normal v) ⊢ WP (LoweredExpr.constant (τ := τ) c) @ s; E {{ Φ }} := by
  refine wp_pure_step_val (by rfl) fun _ => ?_
  exact .constant (by simp [State.constant?, h])

/--
A string constant, with code units `cu`, evaluates to its canonical object: it satisfies a
postcondition `Φ` if, one step later (`▷`), for the location `ℓ` of a string holding `cu`
(`ℓ ↦{.discard} .string cu`) that is the canonical object of the constant
(`IsConst τ (.string cu) ℓ`), `Φ` holds of completing normally with the object.

So every evaluation of the constant gives the same object (`IsConst.agree`). The first one
allocates it, which is why `ℓ` is only known one step later.
-/
public theorem wp_constant_string {cu : List UInt16} :
    ▷ (∀ ℓ, ℓ ↦{.discard} (.string cu : Cell) -∗ IsConst τ (.string cu) ℓ -∗
        Φ (.normal (.obj ℓ))) ⊢
      WP (LoweredExpr.constant (τ := τ) (.string cu)) @ s; E {{ Φ }} := by
  iintro HΦ
  iapply wp_lift_atomic_base_step_no_fork rfl
  isimp [stateInterp, ConstsInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, %m, Hauth, %hm, #Hents⟩
  cases hl : σ₁.constants.lookup (.string cu) with
  | some ℓ =>
    have hstep : HeadStep (LoweredExpr.constant (τ := τ) (.string cu)) σ₁ (.val (.obj ℓ)) σ₁ :=
      .constant (by simp [State.constant?, ConstValue.prim?, hl])
    have hent : ([∗list] p ∈ σ₁.constants, ConstEntry τ (GF := GF) p.1 p.2) ⊢
        ConstEntry τ (.string cu) ℓ := ConstEntry.of_lookup hl
    ihave #Hent := hent $$ Hents
    simp only [ConstEntry]
    icases Hent with ⟨#Hic, %cu', %heq, #Hl⟩
    cases heq
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
    isplitl [Hh Hauth]
    · iframe Hh
      iframe Hhdr
      iexists m
      iframe Hauth
      isplitr
      · ipureintro
        exact hm
      · iexact Hents
    iexists .normal (.obj ℓ)
    isplit
    · ipureintro
      rfl
    · iapply HΦ $$ Hl Hic
  | none =>
    have hstep : HeadStep (LoweredExpr.constant (τ := τ) (.string cu)) σ₁ (.val (.obj σ₁.fresh))
        (σ₁.allocConst (.string cu) (.string cu)) :=
      .constant (by simp [State.constant?, ConstValue.prim?, hl])
    imodintro
    isplit
    · ipureintro
      exact ⟨[], _, _, [], hstep, rfl, rfl⟩
    inext
    iintro %e₂ %σ₂ %eₜ %Hstep _
    obtain ⟨hs, -, rfl⟩ := Hstep
    obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs hstep
    imod allocString_ghost σ₁ cu $$ [$Hh $Hhdr] with ⟨⟨Hh, #Hhdr'⟩, #Hl, -⟩
    have hk : get? m (ConstValue.string cu).key = none := by rw [hm, hl]
    imod ghost_map_insert_persist _ σ₁.fresh hk $$ Hauth with ⟨Hauth, #Hfrag⟩
    ihave #Hic : IsConst τ (.string cu) σ₁.fresh $$ [Hfrag]
    · simp only [IsConst]
      iexact Hfrag
    imodintro
    isplit
    · itrivial
    isplitl [Hh Hauth]
    · rw [State.toMap_allocConst]
      iframe Hh
      isplitr
      · simp only [ObjectHeaders, State.toMap_allocConst]
        iexact Hhdr'
      iexists insert m (ConstValue.string cu).key σ₁.fresh
      iframe Hauth
      rw [State.constants_allocConst]
      isplitr
      · ipureintro
        intro c
        by_cases hc : c = .string cu
        · subst hc
          simp [LawfulPartialMap.get?_insert]
        · have hk' : (ConstValue.string cu).key ≠ c.key := fun e => hc (ConstValue.key_inj e).symm
          have hb : (c == ConstValue.string cu) = false := by simp [hc]
          simp [LawfulPartialMap.get?_insert, List.lookup, hk', hb, hm]
      · iapply BigSepL.bigSepL_cons.2
        isplitr
        · simp only [ConstEntry]
          iframe Hic
          iexists cu
          isplitr
          · ipureintro
            rfl
          · iexact Hl
        · iexact Hents
    iexists .normal (.obj σ₁.fresh)
    isplit
    · ipureintro
      rfl
    · iapply HΦ $$ Hl Hic

/--
A string concatenation whose parts have evaluated to `vs` allocates a new string, holding the
concatenation of the parts' string forms `cus`: it satisfies a postcondition `Φ` if:
- `cus` are the string forms of `vs` (`StringParts vs cus`: for each string part, a persistent
  points-to for its cell); and
- one step later (`▷`), for the location `ℓ` of a string holding the concatenation
  (`ℓ ↦{.discard} .string cus.flatten`), which is newly allocated (`Fresh τ ℓ`), `Φ` holds of
  completing normally with the string.

The new string is a new object, so it's not identical to any other (see `Fresh.ne`).
-/
public theorem wp_concat {vs : List Value} {cus : List (List UInt16)} :
    StringParts vs cus ∗
        ▷ (∀ ℓ, ℓ ↦{.discard} (.string cus.flatten : Cell) -∗ Fresh τ ℓ -∗
          Φ (.normal (.obj ℓ))) ⊢
      WP (LoweredExpr.concat (vs.map .val)) @ s; E {{ Φ }} := by
  iintro ⟨#Hparts, HΦ⟩
  iapply wp_lift_atomic_base_step_no_fork (by simp [LoweredExpr.toOutcome?])
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
  ihave %hcus : ⌜vs.mapM σ₁.stringPart? = some cus⌝ $$ [Hh Hparts]
  · ihave >%h := StringParts.valid $$ [$Hh $Hparts]
    ipureintro
    exact h
  have hstep : HeadStep (LoweredExpr.concat (vs.map .val)) σ₁ (.val (.obj σ₁.fresh))
      (σ₁.alloc (.string cus.flatten)) := .concat hcus
  imodintro
  isplit
  · ipureintro
    exact ⟨[], _, _, [], hstep, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs hstep
  imod allocString_ghost σ₁ cus.flatten $$ [$Hh $Hhdr] with ⟨⟨Hh, #Hhdr'⟩, #Hl, Hfresh⟩
  imodintro
  isplit
  · itrivial
  isplitl [Hh Hc]
  · iframe Hh
    iframe Hhdr'
    rw [State.constants_alloc]
    iexact Hc
  iexists .normal (.obj σ₁.fresh)
  isplit
  · ipureintro
    rfl
  · iapply HΦ $$ Hl Hfresh

/--
`e` satisfies a postcondition `Φ` if the cells at `ℓ₁` and `ℓ₂` are strings holding `cu₁` and
`cu₂` (`ℓ₁ ↦{.discard} .string cu₁`, `ℓ₂ ↦{.discard} .string cu₂`) and `e'` satisfies `Φ` one step
later (`▷ WP e' {{ Φ }}`), provided:
- `e` hasn't completed (`hv`); and
- in every state where the cells at `ℓ₁` and `ℓ₂` are those strings, `e` takes a head step to `e'`
  that leaves the state unchanged (`h`).

(Comparisons of two strings take such steps.)
-/
public theorem wp_step_of_strings {e e' : LoweredExpr} {ℓ₁ ℓ₂ : Loc} {cu₁ cu₂ : List UInt16}
    (hv : e.toOutcome? = none)
    (h : ∀ σ, σ.lookup ℓ₁ = some (.string cu₁) → σ.lookup ℓ₂ = some (.string cu₂) →
      HeadStep e σ e' σ) :
    ℓ₁ ↦{.discard} (.string cu₁ : Cell) ∗ ℓ₂ ↦{.discard} (.string cu₂ : Cell) ∗
        ▷ WP e' @ s; E {{ Φ }} ⊢
      WP e @ s; E {{ Φ }} := by
  iintro ⟨#Hl₁, #Hl₂, H⟩
  iapply wp_lift_base_step hv
  isimp [stateInterp]
  iintro %σ₁ %ns %obs %obs' %nt ⟨Hh, #Hhdr, Hc⟩
  ihave %Hlook₁ : ⌜σ₁.lookup ℓ₁ = some (.string cu₁)⌝ $$ [Hh Hl₁]
  · ihave >%Hv := genHeap_valid $$ [$Hh $Hl₁]
    ipureintro
    rwa [State.get?_toMap] at Hv
  ihave %Hlook₂ : ⌜σ₁.lookup ℓ₂ = some (.string cu₂)⌝ $$ [Hh Hl₂]
  · ihave >%Hv := genHeap_valid $$ [$Hh $Hl₂]
    ipureintro
    rwa [State.get?_toMap] at Hv
  have hstep := h σ₁ Hlook₁ Hlook₂
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplit
  · ipureintro
    exact ⟨[], e', σ₁, [], hstep, rfl, rfl⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨hs, -, rfl⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := HeadStep.deterministic hs hstep
  imod Hclose
  imodintro
  isplitl [Hh Hc]
  · iframe Hh
    iframe Hc
    iexact Hhdr
  isplitl
  · iexact H
  · isimp
    itrivial

/--
`==` on two strings, holding `cu₁` and `cu₂` (`ℓ₁ ↦{.discard} .string cu₁`,
`ℓ₂ ↦{.discard} .string cu₂`), compares their code units: it satisfies a postcondition `Φ` that
holds, one step later, of completing normally with whether they're equal
(`▷ Φ (.normal (.bool (cu₁ == cu₂)))`).
-/
public theorem wp_primEq_string {ℓ₁ ℓ₂ : Loc} {cu₁ cu₂ : List UInt16} :
    ℓ₁ ↦{.discard} (.string cu₁ : Cell) ∗ ℓ₂ ↦{.discard} (.string cu₂ : Cell) ∗
        ▷ Φ (.normal (.bool (cu₁ == cu₂))) ⊢
      WP (LoweredExpr.primEq (τ := τ) (.val (.obj ℓ₁)) (.val (.obj ℓ₂))) @ s; E {{ Φ }} := by
  iintro ⟨#Hl₁, #Hl₂, HΦ⟩
  iapply wp_step_of_strings (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (cu₁ := cu₁) (cu₂ := cu₂) rfl
    (fun σ h₁ h₂ => .primEq (b := cu₁ == cu₂) (by simp [State.primEq?, State.string?, h₁, h₂]))
  isplitr
  · iexact Hl₁
  isplitr
  · iexact Hl₂
  inext
  iapply wp_val
  iexact HΦ

/--
An intrinsic equality check of two strings with the same code units `cu`
(`ℓ₁ ↦{.discard} .string cu`, `ℓ₂ ↦{.discard} .string cu`) completes normally: it satisfies a
postcondition `Φ` that holds, one step later, of completing normally with the null object
(`▷ Φ (.normal .null)`).
-/
public theorem wp_checkEq_string_pass {ℓ₁ ℓ₂ : Loc} {cu : List UInt16} :
    ℓ₁ ↦{.discard} (.string cu : Cell) ∗ ℓ₂ ↦{.discard} (.string cu : Cell) ∗
        ▷ Φ (.normal .null) ⊢
      WP (LoweredExpr.checkEq (τ := τ) (.val (.obj ℓ₁)) (.val (.obj ℓ₂))) @ s; E {{ Φ }} := by
  iintro ⟨#Hl₁, #Hl₂, HΦ⟩
  iapply wp_step_of_strings (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (cu₁ := cu) (cu₂ := cu) rfl
    (fun σ h₁ h₂ => .checkEqPass (by simp [State.primEq?, State.string?, h₁, h₂]))
  isplitr
  · iexact Hl₁
  isplitr
  · iexact Hl₂
  inext
  iapply wp_val
  iexact HΦ

/--
An intrinsic equality check of two strings with different code units `cu₁` and `cu₂` (`h`;
`ℓ₁ ↦{.discard} .string cu₁`, `ℓ₂ ↦{.discard} .string cu₂`) throws: it satisfies a postcondition
`Φ` that holds, one step later, of throwing (`▷ Φ (.throwing (.error .expectFailed))`).
-/
public theorem wp_checkEq_string_fail {ℓ₁ ℓ₂ : Loc} {cu₁ cu₂ : List UInt16} (h : cu₁ ≠ cu₂) :
    ℓ₁ ↦{.discard} (.string cu₁ : Cell) ∗ ℓ₂ ↦{.discard} (.string cu₂ : Cell) ∗
        ▷ Φ (.throwing (.error .expectFailed)) ⊢
      WP (LoweredExpr.checkEq (τ := τ) (.val (.obj ℓ₁)) (.val (.obj ℓ₂))) @ s; E {{ Φ }} := by
  iintro ⟨#Hl₁, #Hl₂, HΦ⟩
  iapply wp_step_of_strings (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (cu₁ := cu₁) (cu₂ := cu₂) rfl
    (fun σ h₁ h₂ => .checkEqFail (by simp [State.primEq?, State.string?, h₁, h₂, h]))
  isplitr
  · iexact Hl₁
  isplitr
  · iexact Hl₂
  inext
  iapply wp_throwing
  iexact HΦ

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

/--
`MemberSpec key holder Pre Post` is a specification of member `key` (a method, getter or setter in
the member table), as provided by class `holder`: every run of its body, with `this` and the formal
parameters bound to cells holding values `vs` (the receiver, then the arguments) that satisfy the
precondition `Pre vs`, as the body of a running call, completes safely, with an outcome `o`
satisfying the postcondition `Post vs o`.

It's a Texan triple (see `FunSpec`) for every such run: for all values `vs`, locations `ℓs` of the
cells, and static types `T`,
`{{ Pre vs ∗ PointsToVals ℓs vs }} frame (body …) T {{ o, RET o; Post vs o }}`. Unlike `FunSpec`, it
describes the member's body rather than a call, since a member can be run by a method call, a
property read or assignment, or a `super` access. The laws for using it take it under a `▷`, which
the step into the body removes (see `MemberSpec.wp_methodCall`), so that it can be proved by Löb
induction (`MemberSpec.intro`).

A specification is for one `holder`, since the `super` accesses in the body depend on it (see
`Member.proc`).
-/
@[expose]
public def MemberSpec (key holder : String) (Pre : List Value → IProp GF)
    (Post : List Value → DartLang.Outcome (τ := τ) → IProp GF) : IProp GF :=
  iprop(∀ (d : MemberDecl (τ := τ)) (vs : List Value) (ℓs : List Loc) (T : τ),
    ⌜P.members key = some d⌝ →
    {{ Pre vs ∗ PointsToVals ℓs vs }}
      (LoweredExpr.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs) T)
    {{ o, RET o; Post vs o }})

/-- `MemberSpec key holder Pre Post` is persistent, since each of its Texan triples is. -/
public instance MemberSpec_persistent (key holder : String) (Pre : List Value → IProp GF)
    (Post : List Value → DartLang.Outcome (τ := τ) → IProp GF) :
    Persistent (MemberSpec key holder Pre Post) := by
  unfold MemberSpec
  infer_instance

/--
Using a specification of member `key`, provided by class `holder`, for a method call: a method call
on the object at `ℓ`, whose arguments have evaluated to `vs`, satisfies a postcondition `Φ`, if:
- the object's own cell records its class `k` (`ℓ ↦{.discard} .object k C fs`), which dispatches
  the method's name to `key`, provided by `holder` (`hd`), declared as `d` (`hm`) with one formal
  parameter per argument (`hlen`);
- `key` meets a specification (`MemberSpec key holder Pre Post`), which is only needed one step
  later (`▷`);
- the precondition holds of the receiver and the arguments (`Pre (.obj ℓ :: vs)`); and
- the postcondition implies `Φ`, one step later (`▷ ∀ o, Post (.obj ℓ :: vs) o -∗ Φ o`).
-/
public theorem MemberSpec.wp_methodCall {ℓ : Loc} {name k key holder : String} {C : τ}
    {fs : List (String × Loc)} {d : MemberDecl (τ := τ)} {vs : List Value} {T : τ}
    {Pre : List Value → IProp GF} {Post : List Value → DartLang.Outcome (τ := τ) → IProp GF}
    {Φ : DartLang.Outcome (τ := τ) → IProp GF}
    (hd : P.dispatch k name = some (.proc key holder)) (hm : P.members key = some d)
    (hlen : d.params.length = vs.length) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗ ▷ MemberSpec key holder Pre Post ∗
        Pre (.obj ℓ :: vs) ∗ ▷ (∀ o, Post (.obj ℓ :: vs) o -∗ Φ o) ⊢
      WP (LoweredExpr.methodCall (.val (.obj ℓ)) name (vs.map .val) T) {{ Φ }} := by
  iintro ⟨#Hobj, #Hspec, HPre, HΦ⟩
  iapply DartSemantics.wp_methodCall hd hm hlen
  isplitr
  · iexact Hobj
  inext
  iintro %ℓs Hls
  ihave HPre' : iprop(Pre (.obj ℓ :: vs) ∗ PointsToVals ℓs (.obj ℓ :: vs)) $$ [HPre Hls]
  · isplitl [HPre]
    · iexact HPre
    · iexact Hls
  unfold MemberSpec
  ihave Hrun := Hspec $$ %d %(.obj ℓ :: vs) %ℓs %T %hm %Φ HPre'
  iapply Hrun
  inext
  iexact HΦ

/--
Using a specification of member `key`, provided by class `holder`, for a property read: reading
property `p` of the object at `ℓ`, with (possibly promoted) static type `T`, satisfies a
postcondition `Φ`, if:
- the object's own cell records its class `k` (`ℓ ↦{.discard} .object k C fs`), which dispatches
  the property's name to the getter `key`, provided by `holder` (`hd`), declared as `d` (`hm`) with
  no formal parameters (`hlen`);
- `key` meets a specification (`MemberSpec key holder Pre Post`), which is only needed one step
  later (`▷`);
- the precondition holds of the receiver (`Pre [.obj ℓ]`); and
- one step later, for each outcome `o` that the postcondition allows, the promotion check of `o`
  against `T` satisfies `Φ` (`▷ ∀ o, Post [.obj ℓ] o -∗ WP (.checkPromotion T o.toExpr) {{ Φ }}`;
  see `wp_checkPromotion`).
-/
public theorem MemberSpec.wp_propertyGet {ℓ : Loc} {p : Property} {k key holder : String}
    {C T : τ} {fs : List (String × Loc)} {d : MemberDecl (τ := τ)} {Pre : List Value → IProp GF}
    {Post : List Value → DartLang.Outcome (τ := τ) → IProp GF}
    {Φ : DartLang.Outcome (τ := τ) → IProp GF}
    (hd : P.dispatch k p.name = some (.proc key holder)) (hm : P.members key = some d)
    (hlen : d.params.length = 0) :
    ℓ ↦{.discard} (.object k C fs : Cell) ∗ ▷ MemberSpec key holder Pre Post ∗
        Pre [.obj ℓ] ∗
        ▷ (∀ o, Post [.obj ℓ] o -∗ WP (LoweredExpr.checkPromotion T o.toExpr) {{ Φ }}) ⊢
      WP (LoweredExpr.propertyGet (.val (.obj ℓ)) p T) {{ Φ }} := by
  iintro ⟨#Hobj, #Hspec, HPre, HΦ⟩
  iapply DartSemantics.wp_propertyGet_getter hd hm hlen
  isplitr
  · iexact Hobj
  inext
  iintro %ℓs Hls
  rw [show LoweredExpr.checkPromotion T
      (.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs) T) =
      (EctxItem.checkPromotion T).fill
        (.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs) T) from rfl]
  iapply wp_bind_item
  ihave HPre' : iprop(Pre [.obj ℓ] ∗ PointsToVals ℓs [.obj ℓ]) $$ [HPre Hls]
  · isplitl [HPre]
    · iexact HPre
    · iexact Hls
  unfold MemberSpec
  ihave Hrun := Hspec $$ %d %([.obj ℓ] : List Value) %ℓs %T %hm HPre'
  iapply Hrun
  inext
  simp only [EctxItem.fill]
  iexact HΦ

/--
Proving a specification of member `key`, provided by class `holder`, by Löb induction: `key` meets
the specification `MemberSpec key holder Pre Post` if:
- the member table declares `key` as `d` (`hm`); and
- for all values `vs`, locations `ℓs` and static types `T`, the body, with `this` and the formal
  parameters bound to cells at `ℓs` (see `SemanticParams.memberBody`), run as the body of a running
  call, satisfies the postcondition (`WP (.frame (…) T) {{ o, Post vs o }}`), given the
  precondition (`Pre vs`), the ownership of the cells, holding `vs` (`PointsToVals ℓs vs`), and
  the specification itself one step later (`▷ MemberSpec key holder Pre Post`), for the body's own
  calls of `key` (`H`).

Assuming the specification for the body's calls isn't circular: the laws for using it only need it
one step later, after the step into the body (see `MemberSpec.wp_methodCall`). For a member that
doesn't call itself, `H` can ignore the assumption.
-/
public theorem MemberSpec.intro {key holder : String} {d : MemberDecl (τ := τ)}
    {Pre : List Value → IProp GF} {Post : List Value → DartLang.Outcome (τ := τ) → IProp GF}
    (hm : P.members key = some d)
    (H : ∀ vs ℓs T, ▷ MemberSpec key holder Pre Post ∗ Pre vs ∗ PointsToVals ℓs vs ⊢
      WP (LoweredExpr.frame (P.memberBody key holder (d.this :: d.params) d.body ℓs) T)
        {{ o, Post vs o }}) :
    ⊢ MemberSpec key holder Pre Post := by
  iloeb as IH
  unfold MemberSpec
  iintro %d' %vs %ℓs %T %hm'
  obtain rfl : d' = d := Option.some.inj (hm'.symm.trans hm)
  imodintro
  iintro %Φ ⟨HPre, Hls⟩ HΦ
  -- `unfold MemberSpec` above unfolded the specification in `IH` too. Fold it back, as `H` needs.
  ihave #IH' : ▷ MemberSpec key holder Pre Post $$ []
  · unfold MemberSpec
    iexact IH
  ihave Hwp := H vs ℓs T $$ [$IH' $HPre $Hls]
  ihave Hwp' := wp_frame_step_l' (R := iprop(∀ o, Post vs o -∗ Φ o)) rfl
    Std.LawfulSet.subset_refl $$ [$HΦ $Hwp]
  iapply wp_mono _ $$ Hwp'
  intro o
  iintro ⟨HΦ, Ho⟩
  iapply HΦ $$ Ho

end FunSpecs

end DartSemantics
