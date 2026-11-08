module
import DartSemantics
import DartLang.SimpleTypes

/-!
# Specs proved with the program logic

Weakest preconditions for small programs, on `SimpleType`, for every choice of `SemanticParams`.
They exercise the primitive laws and the proof-mode tactics (see `ProofMode.lean`). A larger
example with calls, and specifications of functions, is in `CallSpecs.lean`.

The spec of `{ x._f!; x._f }` is proved twice, to compare: once applying the laws for its four
reads by hand (45 lines of tactics, not counting comments), and once with `wp_load` (11 lines).
The program takes 10 steps; `wp_pures` takes the pure ones in both proofs.
-/

namespace DartSemantics.Tests.Specs

open DartLang SimpleType Iris Iris.BI Iris.ProgramLogic

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Variable" => Variable (τ := SimpleType)
local notation "Value" => Value (τ := SimpleType)
local notation "Outcome" => Outcome (τ := SimpleType)
local notation "Cell" => Cell (τ := SimpleType)

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS SimpleType hlc GF]
variable [P : SemanticParams SimpleType]

include hlc

/-- `{ null!; null }` throws, without touching the state. -/
example : ⊢@{IProp GF} WP (LoweredExpr.block (τ := SimpleType) [.nullCheck .null, .null]) {{ o,
    ⌜o = DartLang.Outcome.throwing (.error .typeError)⌝ }} := by
  iintro
  wp_pures
  ipureintro
  trivial

/-- `true ? 1 : 2` evaluates to `1`: boolean and integer literals evaluate to their values. -/
example : ⊢@{IProp GF} WP (LoweredExpr.cond (τ := SimpleType) (.bool true) (.int 1) (.int 2) int)
    {{ o, ⌜o = DartLang.Outcome.normal (.int 1)⌝ }} := by
  iintro
  wp_pures
  ipureintro
  trivial

/-- `Expect.equals(1, 1)` passes: it completes normally with the null object. -/
example : ⊢@{IProp GF} WP (LoweredExpr.checkEq (τ := SimpleType) (.int 1) (.int 1))
    {{ o, ⌜o = DartLang.Outcome.normal .null⌝ }} := by
  iintro
  wp_pures
  ipureintro
  trivial

/-- `Expect.isNull(true)` fails: it throws. -/
example : ⊢@{IProp GF} WP (LoweredExpr.check (τ := SimpleType) .isNull (.bool true))
    {{ o, ⌜o = DartLang.Outcome.throwing (.error .expectFailed)⌝ }} := by
  iintro
  wp_pures
  ipureintro
  trivial

/--
The body `{ return 1; 2; }` of a running call (`frame`) makes the call complete normally with `1`:
the return propagates out of the block, and `wp_frame` turns it into completing normally.
-/
example : ⊢@{IProp GF} WP (LoweredExpr.frame (τ := SimpleType) (.block [.ret (.int 1), .int 2])
    int) {{ o, ⌜o = DartLang.Outcome.normal (.int 1)⌝ }} := by
  iintro
  refine DartSemantics.tac_wp_frame ?_
  wp_pures
  inext
  ipureintro
  trivial

/--
A call of `int one() { return 1; }` returns `1`, for every function table that declares `one` that
way (`hf`). `wp_call` takes the call's step, and the body then runs with no parameters.
-/
example
    (hf : SemanticParams.functions "one" = some ⟨[], LoweredExpr.ret (τ := SimpleType) (.int 1)⟩) :
    ⊢@{IProp GF} WP (LoweredExpr.call (τ := SimpleType) "one" [] int)
      {{ o, ⌜o = DartLang.Outcome.normal (.int 1)⌝ }} := by
  iintro
  wp_call hf
  iintro %ℓs Hls
  rcases ℓs with _ | ⟨ℓ, ℓs⟩
  · dart_bind_params
    wp_pures
    ipureintro
    trivial
  · simp only [PointsToVals]
    iexfalso
    iexact Hls

/-- `L: { break L; 1; }` completes normally: the break skips the rest of the labeled statement. -/
example : ⊢@{IProp GF} WP (LoweredExpr.labeled (τ := SimpleType) "L" (.block [.brk "L", .int 1]))
    {{ o, ⌜o = DartLang.Outcome.normal .null⌝ }} := by
  iintro
  wp_pures
  ipureintro
  trivial

/-- `-(2 * 3) < 1 + 2` evaluates to `true`, in any integer mode, here `checked`. -/
example : ⊢@{IProp GF} WP (LoweredExpr.intBin (τ := SimpleType) .lt (some .checked)
    (.intNeg (some .checked) (.intBin .mul (some .checked) (.int 2) (.int 3)))
    (.intBin .add (some .checked) (.int 1) (.int 2)))
    {{ o, ⌜o = DartLang.Outcome.normal (.bool true)⌝ }} := by
  iintro
  wp_pures
  ipureintro
  trivial

/--
`n + 1`, in mode `checked`, evaluates to `n + 1` if `n` is small enough (`h`). `wp_int_checked`
leaves the side condition that the result is in 64-bit range.
-/
example (n : Int) (h : 0 ≤ n ∧ n < 100) :
    ⊢@{IProp GF} WP (LoweredExpr.intBin (τ := SimpleType) .add (some .checked) (.int n) (.int 1))
      {{ o, ⌜o = DartLang.Outcome.normal (.int (n + 1))⌝ }} := by
  iintro
  wp_pures
  wp_int_checked
  · omega
  · ipureintro
    trivial

/-- A local variable of type `bool`. -/
def b : Variable := { name := "b", type := bool }

/--
`{ bool b = true; while (b) { b = false; } }` completes normally. The loop is proved with the loop
invariant rule (`tac_wp_loop_inv`): the invariant is that `b` holds some boolean.
-/
example : ⊢@{IProp GF} WP (LoweredExpr.block (τ := SimpleType)
    [.declare b bool false, .variableSet b (.bool true),
      .labeled "L" (.loop (.cond (.var b bool) (.variableSet b (.bool false)) (.brk "L") Null))])
    {{ o, ⌜o = DartLang.Outcome.normal .null⌝ }} := by
  iintro
  wp_alloc ℓ Hl
  wp_pures
  wp_store Hl
  wp_pures
  refine DartSemantics.tac_wp_loop_inv iprop(∃ v, ℓ ↦ (.val (.bool v) : Cell)) ?_ ?_
  · iexists true
    iexact Hl
  · iintro ⟨%v, Hl⟩
    wp_pures
    wp_load Hl
    cases v
    · -- `b` is `false`: the loop breaks out of `L`, and the program completes.
      wp_pures
      ipureintro
      trivial
    · -- `b` is `true`: the body sets it to `false`, and the invariant holds again.
      wp_pures
      wp_store Hl
      inext
      iexists false
      iexact Hl

def x : Variable := { name := "x", type := ObjectQ }

/-- `{ Object? x; x! }` throws: a declared nullable variable starts out null. -/
example : ⊢@{IProp GF} WP (LoweredExpr.block (τ := SimpleType)
    [.declare x ObjectQ true, .nullCheck (.var x ObjectQ)]) {{ o,
    ⌜o = DartLang.Outcome.throwing (.error .typeError)⌝ }} := by
  iintro
  wp_alloc ℓ Hl
  wp_pures
  wp_load Hl
  wp_pures
  ipureintro
  trivial

/--
`{ Object? x; x = true; x! }` completes normally: after the assignment, `x` holds `true`, so the
null check succeeds.
-/
example : ⊢@{IProp GF} WP (LoweredExpr.block (τ := SimpleType)
    [.declare x ObjectQ true, .variableSet x (.bool true), .nullCheck (.var x ObjectQ)])
    {{ o, ⌜o = DartLang.Outcome.normal .null⌝ }} := by
  iintro
  wp_alloc ℓ Hl
  wp_pures
  wp_store Hl
  wp_pures
  wp_load Hl
  wp_pures
  ipureintro
  trivial

/-- A `final` local variable, with type `Object?`. -/
def z : Variable := { name := "z", type := ObjectQ, isFinal := true }

/--
`{ final Object? z; z = true; z! }` completes normally: a `final` variable starts out unassigned
(flow analysis sets `startsNull` to `false`), so it can be assigned once.
-/
example : ⊢@{IProp GF} WP (LoweredExpr.block (τ := SimpleType)
    [.declare z ObjectQ false, .variableSet z (.bool true), .nullCheck (.var z ObjectQ)])
    {{ o, ⌜o = DartLang.Outcome.normal .null⌝ }} := by
  iintro
  wp_alloc ℓ Hl
  wp_pures
  wp_store Hl
  wp_pures
  wp_load Hl
  wp_pures
  ipureintro
  trivial

/-- A promotable property. -/
def f : Property (τ := SimpleType) := ⟨"_f", ObjectQ, true⟩

/--
`{ x._f!; x._f }`, where parameter `x` (at `ℓ`) refers to an object of class `C` and type `int` (at
`ℓo`) whose instance variable `_f` (at `ℓf`) holds `true`, completes normally, and leaves the cells
as they were, if `C` dispatches `_f` to the instance variable (`hd`). The second read is promoted
to `Object`, which the promotion check verifies.
-/
example (ℓ ℓo ℓf : Loc) (hd : P.dispatch "C" "_f" = some (.field "_f")) :
    {{ ℓ ↦ (.val (.obj ℓo) : Cell) ∗ ℓo ↦{.discard} (.object "C" int [("_f", ℓf)] : Cell) ∗
        ℓf ↦ (.val (.bool true) : Cell) }}
      (LoweredExpr.block (τ := SimpleType)
        [.nullCheck (.propertyGet (.varAt x ObjectQ ℓ) f ObjectQ),
          .propertyGet (.varAt x ObjectQ ℓ) f Object])
    {{ RET .normal .null; ℓ ↦ (.val (.obj ℓo) : Cell) ∗ ℓf ↦ (.val (.bool true) : Cell) }} := by
  iintro %Φ ⟨Hl, #Ho, Hf⟩ HΦ
  wp_pures
  -- Read `x`.
  iapply DartSemantics.wp_varAt (v := .obj ℓo) (S := int) (by decide)
  isplitr
  · iapply HasDynamicType.obj
    iexact Ho
  isplitl [Hl]
  · iexact Hl
  inext
  iintro Hl
  wp_pures
  -- Read `x._f`, of static type `Object?`.
  iapply DartSemantics.wp_propertyGet_field (fs := [("_f", ℓf)]) (w := .bool true)
    (S := SimpleType.bool) hd rfl (by decide)
  isplitr
  · iexact Ho
  isplitr
  · iapply HasDynamicType.bool
  isplitl [Hf]
  · iexact Hf
  inext
  iintro Hf
  -- `true!`, then the rest of the block.
  wp_pures
  -- Read `x` again.
  iapply DartSemantics.wp_varAt (v := .obj ℓo) (S := int) (by decide)
  isplitr
  · iapply HasDynamicType.obj
    iexact Ho
  isplitl [Hl]
  · iexact Hl
  inext
  iintro Hl
  wp_pures
  -- Read `x._f`, promoted to `Object`.
  iapply DartSemantics.wp_propertyGet_field (fs := [("_f", ℓf)]) (w := .bool true)
    (S := SimpleType.bool) hd rfl (by decide)
  isplitr
  · iexact Ho
  isplitr
  · iapply HasDynamicType.bool
  isplitl [Hf]
  · iexact Hf
  inext
  iintro Hf
  wp_pures
  iapply HΦ
  iframe Hl
  iexact Hf

/-- The same spec, proved with the `wp_load` tactic for the reads. -/
example (ℓ ℓo ℓf : Loc) (hd : P.dispatch "C" "_f" = some (.field "_f")) :
    {{ ℓ ↦ (.val (.obj ℓo) : Cell) ∗ ℓo ↦{.discard} (.object "C" int [("_f", ℓf)] : Cell) ∗
        ℓf ↦ (.val (.bool true) : Cell) }}
      (LoweredExpr.block (τ := SimpleType)
        [.nullCheck (.propertyGet (.varAt x ObjectQ ℓ) f ObjectQ),
          .propertyGet (.varAt x ObjectQ ℓ) f Object])
    {{ RET .normal .null; ℓ ↦ (.val (.obj ℓo) : Cell) ∗ ℓf ↦ (.val (.bool true) : Cell) }} := by
  iintro %Φ ⟨Hl, #Ho, Hf⟩ HΦ
  wp_pures
  wp_load Hl
  wp_load Hf
  wp_pures
  wp_load Hl
  wp_load Hf
  wp_pures
  iapply HΦ
  iframe Hl
  iexact Hf

/--
`x is int ? x : null`, where parameter `x` refers to an object of type `int`, evaluates to `x`,
read in the first branch with `x` promoted to `int`.
-/
example (ℓ ℓo : Loc) (fs : List (String × Loc)) :
    {{ ℓ ↦ (.val (.obj ℓo) : Cell) ∗ ℓo ↦{.discard} (.object "C" int fs : Cell) }}
      (LoweredExpr.cond (τ := SimpleType) (.is (.varAt x ObjectQ ℓ) int) (.varAt x int ℓ) .null
        ObjectQ)
    {{ RET .normal (.obj ℓo); ℓ ↦ (.val (.obj ℓo) : Cell) }} := by
  iintro %Φ ⟨Hl, #Ho⟩ HΦ
  wp_pures
  wp_load Hl
  -- The is-expression's run-time check.
  iapply DartSemantics.wp_is (S := int) (b := true) rfl
  isplitr
  · iapply HasDynamicType.obj
    iexact Ho
  inext
  wp_pures
  wp_load Hl
  iapply HΦ
  iexact Hl

end DartSemantics.Tests.Specs

namespace DartSemantics.Tests.Specs.Generic

open DartLang Iris Iris.BI Iris.ProgramLogic

variable {τ : Type} [DartRuntimeTypeRepr τ]
variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF] [SemanticParams τ]

include hlc

/--
Reading a variable of static type `T` whose value has dynamic type `S`, for an arbitrary type
representation, where `decide` can't prove `S ≤ T`: `wp_load` leaves that goal for afterwards.
-/
example (x : DartLang.Variable (τ := τ)) (S T : τ) (hST : S ≤ T) (ℓ : Loc)
    (v : DartLang.Value (τ := τ)) :
    {{ ℓ ↦ (.val v : DartSemantics.Cell (τ := τ)) ∗ HasDynamicType v S }}
      (LoweredExpr.varAt x T ℓ)
    {{ RET .normal v; ℓ ↦ (.val v : DartSemantics.Cell (τ := τ)) }} := by
  iintro %Φ ⟨Hl, #Hty⟩ HΦ
  wp_load Hl
  · iapply HΦ
    iexact Hl
  · exact hST

end DartSemantics.Tests.Specs.Generic
