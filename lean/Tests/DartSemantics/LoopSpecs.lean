module
import DartSemantics
import DartLang.SimpleTypes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A loop proved correct with the program logic

A top-level function with a `while` loop, on `SimpleType`:

```dart
int sumTo(int n) {
  var s = 0;
  var i = 0;
  while (i < n) { i = i + 1; s = s + i; }
  return s;
}
```

Its specification (`sumTo_spec`): in integer mode `checked`, called with an `n` such that
`0 ≤ n ≤ 2³¹`, `sumTo(n)` returns `n * (n + 1) / 2`. The loop is proved with the loop invariant
rule (the `wp_loop_inv` tactic), using the invariant `0 ≤ i ≤ n` and `s = i * (i + 1) / 2`. Each
of the loop's additions has a side condition, that its result is in 64-bit range, since in mode
`checked` an addition that overflows would get stuck; that's where the bound on `n` is needed.
Finally, adequacy turns the specification into an ordinary Lean theorem about running `sumTo(10)`
(`sumTo_ten`).
-/

namespace DartSemantics.Tests.LoopSpecs

open DartLang SimpleType Iris Iris.BI Iris.ProgramLogic

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Variable" => Variable (τ := SimpleType)
local notation "Value" => Value (τ := SimpleType)
local notation "Outcome" => Outcome (τ := SimpleType)
local notation "Cell" => Cell (τ := SimpleType)

/-- The formal parameter `int n`. -/
def n : Variable := { name := "n", type := int }
/-- The local variable `s`, of type `int`. -/
def s : Variable := { name := "s", type := int }
/-- The local variable `i`, of type `int`. -/
def i : Variable := { name := "i", type := int }

/-
The three variables are different. Resolving one of them to its cell leaves the others alone;
`simp` uses these facts to see that.
-/

theorem s_ne_n : s ≠ n := by simp [s, n]
theorem i_ne_n : i ≠ n := by simp [i, n]
theorem i_ne_s : i ≠ s := by simp [i, s]

/--
The declaration of `sumTo`. The `while` loop is a loop inside a labeled statement `L`, which a
`break` out of `L` ends, and its body is inside a labeled statement `C`, which `continue` would
break out of (see `LoweredExpr.loop`). The integer operators' modes are left unfilled (`none`):
calling `sumTo` fills them in with its integer mode.
-/
def sumToDecl : FunctionDecl (τ := SimpleType) :=
  ⟨[n], .block [
    .declare s int false, .variableSet s (.int 0),
    .declare i int false, .variableSet i (.int 0),
    .labeled "L" (.loop (.cond (.intBin .lt none (.var i int) (.var n int))
      (.labeled "C" (.block [
        .variableSet i (.intBin .add none (.var i int) (.int 1)),
        .variableSet s (.intBin .add none (.var s int) (.var i int))]))
      (.brk "L") Null)),
    .ret (.var s int)]⟩

/-
The specification's precondition and postcondition are pure (`⌜…⌝`). They're `abbrev`s, so that
proof mode can see that they're pure, and introduce them with `%`.
-/

/-- The precondition of `sumTo`: it's called with one integer argument `n`, `0 ≤ n ≤ 2³¹`. -/
abbrev sumToPre {GF : BundledGFunctors} (vs : List Value) : IProp GF :=
  iprop(⌜∃ n, vs = [.int n] ∧ 0 ≤ n ∧ n ≤ 2 ^ 31⌝)

/-- The postcondition of `sumTo`: called with `n`, it returns `n * (n + 1) / 2`. -/
abbrev sumToPost {GF : BundledGFunctors} (vs : List Value) (o : Outcome) : IProp GF :=
  iprop(⌜∀ n, vs = [.int n] → o = .normal (.int (n * (n + 1) / 2))⌝)

/-- A number between `0` and `2⁶²` is in 64-bit range. -/
theorem inRange {x : Int} (h₀ : 0 ≤ x) (h₁ : x ≤ 2 ^ 62) : -2 ^ 63 ≤ x ∧ x < 2 ^ 63 := by
  constructor <;> norm_num at h₁ ⊢ <;> omega

/--
The arithmetic behind the loop's invariant, for an iteration that starts with `i = i₀`, where
`0 ≤ i₀ < n ≤ 2³¹` (`h₀`, `hlt` and `hn`), and `s = i₀ * (i₀ + 1) / 2`:
- `i₀ + 1` is in 64-bit range;
- so is `s + (i₀ + 1)`; and
- `s + (i₀ + 1)` is `(i₀ + 1) * (i₀ + 1 + 1) / 2`, so the invariant holds again.
-/
theorem step_arith {i₀ n₀ : Int} (h₀ : 0 ≤ i₀) (hlt : i₀ < n₀) (hn : n₀ ≤ 2 ^ 31) :
    (-2 ^ 63 ≤ i₀ + 1 ∧ i₀ + 1 < 2 ^ 63) ∧
      (-2 ^ 63 ≤ i₀ * (i₀ + 1) / 2 + (i₀ + 1) ∧ i₀ * (i₀ + 1) / 2 + (i₀ + 1) < 2 ^ 63) ∧
      i₀ * (i₀ + 1) / 2 + (i₀ + 1) = (i₀ + 1) * (i₀ + 1 + 1) / 2 := by
  have hp₀ : 0 ≤ i₀ * (i₀ + 1) := by positivity
  have hp₁ : i₀ * (i₀ + 1) ≤ 2 ^ 31 * 2 ^ 31 := by nlinarith
  have hd₀ : 0 ≤ i₀ * (i₀ + 1) / 2 := Int.ediv_nonneg hp₀ (by norm_num)
  have hd₁ : i₀ * (i₀ + 1) / 2 ≤ i₀ * (i₀ + 1) := Int.ediv_le_self _ hp₀
  refine ⟨inRange (by omega) (by norm_num at hn ⊢; omega),
    inRange (by omega) (by norm_num at hp₁ hn ⊢; omega), ?_⟩
  -- `(i₀ + 1) * (i₀ + 2) = i₀ * (i₀ + 1) + (i₀ + 1) * 2`, and dividing by `2` distributes over
  -- adding a multiple of `2`.
  rw [show (i₀ + 1) * (i₀ + 1 + 1) = i₀ * (i₀ + 1) + (i₀ + 1) * 2 by ring,
    Int.add_mul_ediv_right _ _ (by norm_num)]

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS SimpleType hlc GF]
variable [P : SemanticParams SimpleType]

include hlc

-- The proof steps through the whole body, which takes more than the default budget of
-- `maxHeartbeats` (Lean's limit on the work a single declaration may take to elaborate).
set_option maxHeartbeats 1000000 in
/--
`sumTo` meets its specification (`FunSpec "sumTo" sumToPre sumToPost`), if the function table
declares it as `sumToDecl` (`hf`), and its integer mode is `checked` (`hmode`).
-/
theorem sumTo_spec (hf : P.functions "sumTo" = some sumToDecl)
    (hmode : P.intModeOf "sumTo" = .checked) :
    ⊢@{IProp GF} FunSpec "sumTo" sumToPre sumToPost := by
  refine FunSpec.intro hf (fun vs => ?_) fun vs T ℓs => ?_
  · -- There's one argument per formal parameter.
    iintro %⟨n₀, hn, -⟩
    ipureintro
    simp [hn, sumToDecl]
  · iintro ⟨-, %⟨n₀, hn, h₀, hn₀⟩, Hls⟩
    subst hn
    -- One cell is allocated, for `n`; `PointsToVals` is `False` for any other number of cells.
    rcases ℓs with _ | ⟨ℓn, _ | ⟨ℓ', ℓs⟩⟩
    · simp only [PointsToVals]
      iexfalso
      iexact Hls
    · simp only [PointsToVals, sumToDecl, hmode]
      dart_bind_params
      -- Binding `n` resolves only `n`: the local variables are different variables.
      simp only [s_ne_n, i_ne_n, ite_false]
      icases Hls with ⟨Hn, -⟩
      -- Step into the body of the call.
      wp_pures
      -- `var s = 0; var i = 0;`
      wp_alloc ℓs Hs
      simp only [i_ne_s, ite_false]
      wp_pures
      wp_store Hs
      wp_pures
      wp_alloc ℓi Hi
      wp_pures
      wp_store Hi
      wp_pures
      -- The loop, with its invariant.
      wp_loop_inv iprop(∃ i₀ s₀ : Int,
          ℓi ↦ (.val (.int i₀) : Cell) ∗
          ℓs ↦ (.val (.int s₀) : Cell) ∗ ℓn ↦ (.val (.int n₀) : Cell) ∗
          ⌜0 ≤ i₀ ∧ i₀ ≤ n₀ ∧ s₀ = i₀ * (i₀ + 1) / 2⌝)
      · -- The invariant holds before the loop: `i` and `s` are `0`.
        iexists 0, 0
        iframe Hi
        iframe Hs
        iframe Hn
        ipureintro
        exact ⟨le_refl _, h₀, rfl⟩
      · -- Each iteration: read `i < n`.
        iintro ⟨%i₀, %s₀, Hi, Hs, Hn, %⟨hi₀, hin, hs₀⟩⟩
        subst hs₀
        wp_pures
        wp_load Hi
        wp_pures
        wp_load Hn
        wp_pures
        by_cases hlt : i₀ < n₀
        · -- `i < n`: run the body, `i = i + 1; s = s + i;`.
          obtain ⟨hr₁, hr₂, hinv⟩ := step_arith hi₀ hlt hn₀
          simp only [decide_eq_true hlt]
          wp_pures
          wp_load Hi
          wp_pures
          wp_int_checked
          · exact hr₁
          wp_store Hi
          wp_pures
          wp_load Hs
          wp_pures
          wp_load Hi
          wp_int_checked
          · exact hr₂
          wp_store Hs
          wp_pures
          -- The invariant holds again.
          iexists i₀ + 1, i₀ * (i₀ + 1) / 2 + (i₀ + 1)
          iframe Hi
          iframe Hs
          iframe Hn
          ipureintro
          exact ⟨by omega, by omega, hinv⟩
        · -- `i ≥ n`, so `i = n`: break out of the loop, and return `s`.
          have hi : i₀ = n₀ := by omega
          subst hi
          simp only [decide_eq_false hlt]
          wp_pures
          wp_load Hs
          wp_pures
          ipureintro
          intro n' hn'
          simp_all
    · simp only [PointsToVals]
      icases Hls with ⟨-, Hf⟩
      iexfalso
      iexact Hf

end Specs

/--
**`sumTo(10)` is safe and returns `55`**, for every choice of `SemanticParams` whose function table
declares `sumTo` as `sumToDecl` (`hf`), with integer mode `checked` (`hmode`): running it from the
empty state never gets stuck (`.NotStuck`), and if it completes, it completes normally with `55`
(`o = .normal (.int 55)`).
-/
theorem sumTo_ten [P : SemanticParams SimpleType] (hf : P.functions "sumTo" = some sumToDecl)
    (hmode : P.intModeOf "sumTo" = .checked) :
    adequate .NotStuck (LoweredExpr.call "sumTo" [.int 10] int) State.empty
      (fun o _ => o = .normal (.int 55)) := by
  refine adequacy (GF := DartS SimpleType) _ _ _ ?_
  intro inst
  iintro -
  ihave #Hspec := sumTo_spec (GF := DartS SimpleType) hf hmode
  -- Evaluate the argument, `10`, and then use `sumTo`'s specification.
  wp_pures
  wp_call_spec Hspec
  isplitr
  · ipureintro
    exact ⟨10, rfl, by norm_num, by norm_num⟩
  iintro %o %ho
  ipureintro
  exact ho 10 rfl

end DartSemantics.Tests.LoopSpecs
