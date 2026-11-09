module
public import DartSemantics.Heap
public import DartSemantics.Language
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Adequacy
public import Iris.BI.Lib.GenHeap
public import Iris.ProofMode
public import Iris.Std.GenSetsInstances

/-!
# Ghost state and adequacy

The program logic for the semantics is iris-lean's weakest-precondition logic, instantiated with a
*ghost heap* that mirrors the run-time heap. It is iris-lean's `gen_heap` library, as in HeapLang,
over the finite-map view of the heap (`State.toMap`). Its points-to assertion `ℓ ↦ c` says that
the cell at `ℓ` holds `c`, and grants ownership of the cell.

An object's own cell (`Cell.object`) never changes once the object exists: it records the object's
class, its dynamic type and the locations of its instance variables. Neither does a string's cell
(`Cell.string`), since strings are immutable. So the logic keeps a
*persistent* points-to `ℓ ↦{DFrac.discard} c` (written `ℓ ↦□ c` in Rocq iris) for each object
cell, which can be freely duplicated: knowing an object's class and dynamic type doesn't require
owning it. The state interpretation holds these for every object in the heap (`ObjectHeaders`), so
that a proof can always learn the class and dynamic type of an object that a value refers to.

The table of canonical constants (`State.constants`) is mirrored by a *ghost map* (iris-lean's
`ghost_map`, a finite map in the ghost state). The state interpretation holds its authoritative
part, which agrees with the table, and a proof can hold persistent fragments of it: `IsConst τ c ℓ`
says that `ℓ` is the canonical object of constant `c`. Two fragments for the same constant agree
(`IsConst.agree`), which is how a proof learns that two evaluations of a constant give the same
object.

The Iris vocabulary used here (ghost state, points-to, persistent propositions, basic updates,
the state interpretation, weakest preconditions, adequacy) is explained in the README's "Reading
the Iris parts" section.

Much of the rest of the file is setup that iris-lean requires of every language, following the
naming conventions of Rocq Iris. `DartGpreS` and `DartGS` say which kinds of ghost state the logic
needs: `…GpreS` before the ghost state has been created, `…GS` once it exists. `DartS` is a concrete
choice of ghost state that satisfies them, which `adequacy` needs in order to say that the ghost
state can be created.
-/

namespace DartSemantics

open DartLang Iris Iris.BI Iris.ProgramLogic Iris.Std

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Outcome" => Outcome (τ := τ)
local notation "Cell" => Cell (τ := τ)
local notation "State" => State (τ := τ)

/--
A key for constant `c` in a finite map (see `ConstMap`): an injective encoding of `c` as a list
of integers (`ConstValue.key_inj`), a type that the standard library's tree maps can use as keys.
-/
@[expose]
public def _root_.DartLang.ConstValue.key : ConstValue → List Int
  | .null => [0]
  | .bool b => [1, if b then 1 else 0]
  | .int n => [2, n]
  | .string cu => 3 :: cu.map fun u => (u.toNat : Int)

/-- The constant whose key is `k` (see `ConstValue.key`), if any. -/
@[expose]
public def _root_.DartLang.ConstValue.ofKey : List Int → Option ConstValue
  | [0] => some .null
  | [1, b] => some (.bool (b == 1))
  | [2, n] => some (.int n)
  | 3 :: us => some (.string (us.map fun u => u.toNat.toUInt16))
  | _ => none

/-- Decoding a constant's key gives the constant back (`ofKey c.key = some c`). -/
public theorem _root_.DartLang.ConstValue.ofKey_key (c : ConstValue) :
    ConstValue.ofKey c.key = some c := by
  cases c with
  | null => rfl
  | bool b => cases b <;> rfl
  | int n => rfl
  | string cu =>
    simp only [ConstValue.key, ConstValue.ofKey, List.map_map, Option.some.injEq,
      ConstValue.string.injEq]
    conv => rhs; rw [← List.map_id cu]
    exact List.map_congr_left fun u _ => by simp

/-- Different constants have different keys: `c.key = c'.key` (`h`) only if `c = c'`. -/
public theorem _root_.DartLang.ConstValue.key_inj {c c' : ConstValue} (h : c.key = c'.key) :
    c = c' := by
  have h' := ConstValue.ofKey_key c
  rw [h, ConstValue.ofKey_key] at h'
  exact (Option.some.inj h').symm

/--
Finite maps keyed by constants' keys (`ConstValue.key`), the kind of map that the ghost map of
canonical constants is built on (see `IsConst`).
-/
public abbrev ConstMap := fun V => Std.ExtTreeMap (List Int) V compare

variable (τ) in
/-- The ghost state that the logic needs before a program starts running. -/
public class DartGpreS (GF : BundledGFunctors) extends InvGpreS GF where
  /-- The ghost heap, before it is initialized. -/
  heap_pre : genHeapPreS Loc Cell GF LocMap
  /-- The ghost map of canonical constants, before it is created. -/
  consts_pre : GhostMapG GF (List Int) Loc ConstMap

attribute [reducible, instance] DartGpreS.heap_pre
attribute [reducible, instance] DartGpreS.consts_pre

variable (τ) in
/-- The ghost state of a running program. -/
public class DartGS (hlc : outParam HasLC) (GF : BundledGFunctors) where
  /-- The invariant machinery. (Not an instance, to avoid diamonds with `IrisGS_gen`.) -/
  [invGS : InvGS_gen hlc GF]
  /-- The ghost heap. -/
  heap : genHeapGS Loc Cell GF LocMap
  /-- The kind of ghost state of the ghost map of canonical constants (see `IsConst`). -/
  consts : GhostMapG GF (List Int) Loc ConstMap
  /-- The ghost name of the ghost map of canonical constants. -/
  constsName : GName

attribute [reducible, instance] DartGS.heap
attribute [reducible, instance] DartGS.consts

section

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]

/--
The persistent knowledge that the logic keeps about the cell `c` at `ℓ`: if `c` is an object's own
cell (an instance of a class, or a string), a persistent points-to for it; otherwise nothing.
-/
@[expose]
public def cellHeader (ℓ : Loc) : Cell → IProp GF
  | .object k C fs => ℓ ↦{.discard} (.object k C fs : Cell)
  | .string cu => ℓ ↦{.discard} (.string cu : Cell)
  | _ => iprop(emp)

/-- `cellHeader ℓ c` is persistent: it's either a persistent points-to or `emp`. -/
public instance cellHeader_persistent (ℓ : Loc) (c : Cell) :
    Persistent (cellHeader (GF := GF) ℓ c) := by
  cases c <;> simp only [cellHeader] <;> infer_instance

/--
A persistent points-to for the own cell of every object in the heap of `σ` (instances of classes,
and strings).

The state interpretation holds these so that a proof can learn the class and dynamic type of an
object it has no other knowledge of (see `HasDynamicType.of_headers` in `PrimitiveLaws.lean`). The
laws so far get the facts they need from their preconditions instead, including objects' headers.
-/
@[expose]
public def ObjectHeaders (σ : State) : IProp GF :=
  [∗map] ℓ ↦ c ∈ σ.toMap, cellHeader ℓ c

/-- `ObjectHeaders σ` is persistent: it's a separating conjunction of persistent propositions. -/
public instance ObjectHeaders_persistent (σ : State) : Persistent (ObjectHeaders (GF := GF) σ) :=
  BigSepM.bigSepM_persistent_inst

omit Γ in
variable (τ) in
/--
`ℓ` is the canonical object of constant `c` (see `LoweredExpr.constant`): every evaluation of `c`
evaluates to the object at `ℓ`. It's persistent, and a constant has only one canonical object
(`IsConst.agree`). It's a persistent fragment of a ghost map (iris-lean's `ghost_map`), keyed by
the constant (`ConstValue.key`), whose authoritative part is in the state interpretation
(`ConstsInterp`). (The type representation `τ` is explicit, since nothing else determines it.)
-/
@[expose]
public def IsConst (c : ConstValue) (ℓ : Loc) : IProp GF :=
  DartGS.constsName τ GF ↪◯MAP[c.key]{.discard} ℓ

omit Γ in
/-- `IsConst τ c ℓ` is persistent. -/
public instance IsConst_persistent (c : ConstValue) (ℓ : Loc) :
    Persistent (IsConst τ (GF := GF) c ℓ) := by
  unfold IsConst
  infer_instance

omit Γ in
/--
A constant has only one canonical object: if `ℓ` and `ℓ'` are both canonical objects of `c`, they
are the same location (`IsConst τ c ℓ ∗ IsConst τ c ℓ' ⊢ ⌜ℓ = ℓ'⌝`).
-/
public theorem IsConst.agree {c : ConstValue} {ℓ ℓ' : Loc} :
    IsConst τ (GF := GF) c ℓ ∗ IsConst τ c ℓ' ⊢ ⌜ℓ = ℓ'⌝ := by
  unfold IsConst
  exact ghost_map_elem_agree _ _ _ _ _ _

omit Γ in
variable (τ) in
/--
What the logic knows about entry `(c, ℓ)` of a table of constants (see `State.constants`): `ℓ` is
the canonical object of `c` (`IsConst`), and it's a string with `c`'s code units, of which there's
a persistent points-to. (So far, string constants are the only constants recorded.)
-/
@[expose]
public def ConstEntry (c : ConstValue) (ℓ : Loc) : IProp GF :=
  iprop(IsConst τ c ℓ ∗ ∃ cu, ⌜c = .string cu⌝ ∗ ℓ ↦{.discard} (.string cu : Cell))

omit Γ in
/-- `ConstEntry c ℓ` is persistent: it's made of persistent propositions. -/
public instance ConstEntry_persistent (c : ConstValue) (ℓ : Loc) :
    Persistent (ConstEntry τ (GF := GF) c ℓ) := by
  unfold ConstEntry
  infer_instance

omit Γ in
variable (τ) in
/--
The part of the state interpretation for a table of constants `consts` (see `State.constants`):
the authoritative part of the ghost map of canonical constants (see `IsConst`), which agrees with
the table, and what the logic knows about each entry (`ConstEntry`).

It depends only on the table, not on the heap, so the steps that only change the heap preserve it
without further ado: a string's cell never changes.
-/
@[expose]
public def ConstsInterp (consts : List (ConstValue × Loc)) : IProp GF :=
  iprop(∃ m : ConstMap Loc, (DartGS.constsName τ GF ↪●MAP m) ∗
    ⌜∀ c, get? m c.key = consts.lookup c⌝ ∗ [∗list] p ∈ consts, ConstEntry τ p.1 p.2)

/--
The ownership of the cell `c` at `ℓ` that a program starts out with: a persistent points-to if `c`
is an object's own cell (which never changes), and an ordinary points-to otherwise.
-/
@[expose]
public def cellOwn (ℓ : Loc) : Cell → IProp GF
  | .object k C fs => ℓ ↦{.discard} (.object k C fs : Cell)
  | .string cu => ℓ ↦{.discard} (.string cu : Cell)
  | c => ℓ ↦ c

omit Γ in
/--
Turn ownership of a cell (`ℓ ↦ c`), by a basic update, into its persistent header
(`cellHeader ℓ c`) and the ownership a program starts with (`cellOwn ℓ c`).
-/
theorem pointsTo_init (ℓ : Loc) (c : Cell) :
    ℓ ↦ c ⊢ |==> (cellHeader (GF := GF) ℓ c ∗ cellOwn ℓ c) := by
  cases c with
  | object k C fs =>
    simp only [cellHeader, cellOwn]
    iintro H
    imod pointsTo_persist $$ H with #H
    imodintro
    isplitl
    · iexact H
    · iexact H
  | string cu =>
    simp only [cellHeader, cellOwn]
    iintro H
    imod pointsTo_persist $$ H with #H
    imodintro
    isplitl
    · iexact H
    · iexact H
  | val v =>
    simp only [cellHeader, cellOwn]
    iintro H
    imodintro
    isplitr [H]
    · itrivial
    · iexact H
  | uninit =>
    simp only [cellHeader, cellOwn]
    iintro H
    imodintro
    isplitr [H]
    · itrivial
    · iexact H

omit Γ in
/--
A basic update can be applied to every element of a big separating conjunction: if `h` turns each
`Φ ℓ c` into `Ψ ℓ c` by a basic update, then one basic update turns the conjunction of `Φ ℓ c` over
the entries of `m` into the conjunction of `Ψ ℓ c`.
-/
public theorem bigSepM_bupd {Φ Ψ : Loc → Cell → IProp GF} (h : ∀ ℓ c, Φ ℓ c ⊢ |==> Ψ ℓ c)
    (m : LocMap Cell) : ([∗map] ℓ ↦ c ∈ m, Φ ℓ c) ⊢ |==> [∗map] ℓ ↦ c ∈ m, Ψ ℓ c := by
  induction m using LawfulFiniteMap.induction_on with
  | hemp =>
    iintro _
    imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  | hins ℓ c m hℓ ih =>
    refine (BigSepM.bigSepM_insert hℓ).1.trans ?_
    iintro ⟨H₁, H₂⟩
    imod (h ℓ c) $$ H₁ with H₁
    imod ih $$ H₂ with H₂
    imodintro
    iapply (BigSepM.bigSepM_insert hℓ).2
    isplitl [H₁]
    · iexact H₁
    · iexact H₂

omit Γ in
/--
From the ownership of every cell of `m` (`[∗map] ℓ ↦ c ∈ m, ℓ ↦ c`), a basic update gives the
persistent object headers that the state interpretation keeps (`[∗map] … cellHeader ℓ c`), and the
ownership that the program starts with (`[∗map] … cellOwn ℓ c`). (`adequacy` uses this:
initializing the ghost heap gives the ownership of every cell of the initial state.)
-/
theorem bigSepM_pointsTo_init (m : LocMap Cell) :
    ([∗map] ℓ ↦ c ∈ m, ℓ ↦ c) ⊢
      |==> (([∗map] ℓ ↦ c ∈ m, cellHeader (GF := GF) ℓ c) ∗ [∗map] ℓ ↦ c ∈ m, cellOwn ℓ c) := by
  iintro H
  imod bigSepM_bupd (fun ℓ c => pointsTo_init ℓ c) m $$ H with H
  imodintro
  iapply (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1 $$ H

/--
The state interpretation: the ghost heap agrees with the heap of `σ`, the object headers hold, and
the ghost map of canonical constants agrees with the table of constants of `σ`.
-/
public instance dartStateInterp : StateInterp State Obs GF where
  stateInterp σ _ _ _ := iprop(genHeapInterp σ.toMap ∗ ObjectHeaders σ ∗ ConstsInterp τ σ.constants)

variable [SemanticParams τ]

/--
The semantics, with the ghost heap, as an iris-lean language with a program logic.

Each step of the program grants no extra `▷`s beyond the one that every step removes
(`numLatersPerStep`), and threads forked by the program (there are none yet) have no
postcondition (`forkPost`).
-/
public instance dartIrisGS : IrisGS_gen hlc LoweredExpr GF where
  invGS := DartGS.invGS τ
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono σ ns obs nt := by
    let := @DartGS.invGS τ hlc GF _
    iintro $

end

variable (τ) in
/--
A concrete bundle of the cameras (the algebraic structures from which Iris builds ghost state) that
the logic needs: entries `0` to `3` for iris-lean's invariants and later credits, `4` to `6`
for the ghost heap, and `7` for the ghost map of canonical constants. `instDartGpreS_DartS` says
where each one is.
-/
@[expose]
public def DartS : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Loc (Agree (DiscreteO Cell)) LocMap), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Loc (Agree (DiscreteO GName)) LocMap), by infer_instance⟩
  | 6 => ⟨constOF MetaUR, by infer_instance⟩
  | 7 => ⟨constOF (HeapView (List Int) (Agree (DiscreteO Loc)) ConstMap), by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

/--
`DartS` provides all the ghost state that the logic needs, by giving the index in `DartS` of each
camera that iris-lean's invariants (`toWsatGpreS`), later credits (`toLcGpreS`), ghost heap
(`heap_pre`) and the ghost map of canonical constants (`consts_pre`) use.
-/
public instance instDartGpreS_DartS : DartGpreS τ (DartS τ) where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  heap_pre := by
    constructor
    · constructor
      exists 4
    · constructor
      exists 5
    · exists 6
  consts_pre := by
    constructor
    exists 7

/--
**Adequacy** connects the logic to the semantics: running a program `e` from state `σ` never gets
stuck, even if it runs forever (`.NotStuck`), and if it completes, its outcome satisfies `φ`
(`fun o _ => φ o`), if, given ownership of the cells of `σ`
(`[∗map] ℓ ↦ c ∈ σ.toMap, cellOwn ℓ c`), `e` satisfies a weakest precondition whose postcondition is
the pure property `φ` of its outcome (`WP e {{ o, ⌜φ o⌝ }}`) (`Hwp`). No constant may have been
evaluated yet in `σ` (`hσ`; it holds by `rfl` for a state written out with no constants, such as
`State.empty`).

A postcondition that also mentions cells has to be weakened to its pure part first; claims about
the final heap would need a corollary of iris's strong adequacy theorem.
-/
public theorem adequacy [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF]
    (e : LoweredExpr) (σ : State) (φ : Outcome → Prop)
    (Hwp : ∀ [DartGS τ .hasLC GF],
      ([∗map] ℓ ↦ c ∈ σ.toMap, cellOwn (GF := GF) ℓ c) ⊢ WP e {{ o, ⌜φ o⌝ }})
    (hσ : σ.constants = [] := by rfl) :
    adequate .NotStuck e σ (fun o _ => φ o) := by
  refine wp_adequacy (GF := GF) .NotStuck e σ φ ?_
  intro inst κs
  imod genHeap_init (L := Loc) (V := Cell) (H := LocMap) σ.toMap with ⟨%G, Hh, Hpts, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List Int) (V := Loc) (H := ConstMap)
    with ⟨%γ, Hc⟩
  let : DartGS τ .hasLC GF := ⟨G, inferInstance, γ⟩
  imod bigSepM_pointsTo_init (GF := GF) σ.toMap $$ Hpts with ⟨Hhdr, Hown⟩
  imodintro
  iexists (fun σ _ => iprop(genHeapInterp σ.toMap ∗ ObjectHeaders σ ∗ ConstsInterp τ σ.constants))
  iexists (fun _ => iprop(True))
  isplitl [Hh Hhdr Hc]
  · isplitl [Hh]
    · iexact Hh
    isplitl [Hhdr]
    · simp only [ObjectHeaders]
      iexact Hhdr
    · simp only [ConstsInterp]
      iexists ∅
      isplitl [Hc]
      · iexact Hc
      · isplitr
        · ipureintro
          intro c
          simp_all [LawfulPartialMap.get?_empty]
        · rw [hσ]
          iapply BigSepL.bigSepL_nil.2
          itrivial
  · iapply (@Hwp _) $$ Hown

end DartSemantics
