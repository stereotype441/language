module
import DartSemantics
import DartLang.SimpleTypes

/-!
# A let expression proved correct with the program logic

A top-level function with a postfix increment whose value is used, on `SimpleType`:

```dart
int f(int x) {
  var y = x++;
  return y + x;
}
```

The CFE lowers `x++` to a let expression, `let final t = x in (x = t + 1, t)`
(`LoweredExpr.letIn`): its value is `x`'s old value, which flows out of the let expression into
`y`, and it assigns `x` inside the let expression's body.

Its specification (`f_spec`): in integer mode `checked`, called with an `x` such that
`0 ≤ x ≤ 2⁶¹`, `f(x)` returns `2 * x + 1`. Each addition has a side condition, that its result is
in 64-bit range; that's where the bound on `x` is needed. Adequacy then turns the specification
into an ordinary Lean theorem about running `f(20)` (`f_twenty`).
-/

namespace DartSemantics.Tests.LetSpecs

open DartLang SimpleType Iris Iris.BI Iris.ProgramLogic

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Variable" => Variable (τ := SimpleType)
local notation "Value" => Value (τ := SimpleType)
local notation "Outcome" => Outcome (τ := SimpleType)
local notation "Cell" => Cell (τ := SimpleType)

/-- The formal parameter `int x`. -/
def x : Variable := { name := "x", type := int }
/-- The local variable `y`, of type `int`. -/
def y : Variable := { name := "y", type := int }
/-- The let variable `t` of the lowering of `x++`, of type `int`. -/
def t : Variable := { name := "t", type := int, isFinal := true }

/-
The three variables are different. Resolving one of them to its cell leaves the others alone;
`simp` uses these facts to see that.
-/

theorem y_ne_x : y ≠ x := by simp [y, x]
theorem t_ne_x : t ≠ x := by simp [t, x]
theorem t_ne_y : t ≠ y := by simp [t, y]

/--
The declaration of `f`. The integer operators' modes are left unfilled (`none`): calling `f` fills
them in with its integer mode.
-/
def fDecl : FunctionDecl (τ := SimpleType) :=
  ⟨[x], .block [
    .declare y int false,
    .variableSet y (.letIn t (.var x int)
      (.seq (.variableSet x (.intBin .add none (.var t int) (.int 1))) (.var t int))),
    .ret (.intBin .add none (.var y int) (.var x int))]⟩

/-
The specification's precondition and postcondition are pure (`⌜…⌝`). They're `abbrev`s, so that
proof mode can see that they're pure, and introduce them with `%`.
-/

/-- The precondition of `f`: it's called with one integer argument `x`, `0 ≤ x ≤ 2⁶¹`. -/
abbrev fPre {GF : BundledGFunctors} (vs : List Value) : IProp GF :=
  iprop(⌜∃ x, vs = [.int x] ∧ 0 ≤ x ∧ x ≤ 2 ^ 61⌝)

/-- The postcondition of `f`: called with `x`, it returns `2 * x + 1`. -/
abbrev fPost {GF : BundledGFunctors} (vs : List Value) (o : Outcome) : IProp GF :=
  iprop(⌜∀ x, vs = [.int x] → o = .normal (.int (2 * x + 1))⌝)

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS SimpleType hlc GF]
variable [P : SemanticParams SimpleType]

include hlc

-- The proof steps through the whole body, which takes more than the default budget of
-- `maxHeartbeats` (Lean's limit on the work a single declaration may take to elaborate).
set_option maxHeartbeats 1000000 in
/--
`f` meets its specification (`FunSpec "f" fPre fPost`), if the function table declares it as
`fDecl` (`hf`), and its integer mode is `checked` (`hmode`).
-/
theorem f_spec (hf : P.functions "f" = some fDecl) (hmode : P.intModeOf "f" = .checked) :
    ⊢@{IProp GF} FunSpec "f" fPre fPost := by
  refine FunSpec.intro hf (fun vs => ?_) fun vs T ℓs => ?_
  · -- There's one argument per formal parameter.
    iintro %⟨x₀, hx, -⟩
    ipureintro
    simp [hx, fDecl]
  · iintro ⟨-, %⟨x₀, hx, h₀, hx₀⟩, Hls⟩
    subst hx
    -- One cell is allocated, for `x`; `PointsToVals` is `False` for any other number of cells.
    rcases ℓs with _ | ⟨ℓx, _ | ⟨ℓ', ℓs⟩⟩
    · simp only [PointsToVals]
      iexfalso
      iexact Hls
    · simp only [PointsToVals, fDecl, hmode]
      dart_bind_params
      -- Binding `x` resolves only `x`: `y` and `t` are different variables.
      simp only [y_ne_x, t_ne_x, ite_false]
      icases Hls with ⟨Hx, -⟩
      refine DartSemantics.tac_wp_frame (τ := SimpleType) ?_
      -- `var y = …;`
      wp_alloc ℓy Hy
      simp only [t_ne_y, ite_false]
      wp_pures
      -- `x++`: read `x`, and bind `t` to its value.
      wp_load Hx
      wp_let ℓt Ht
      -- `x = t + 1`
      wp_pures
      wp_load Ht
      wp_pures
      wp_int_checked
      · constructor <;> omega
      wp_store Hx
      wp_pures
      -- The let expression's value, `t`, is assigned to `y`.
      wp_load Ht
      wp_store Hy
      wp_pures
      -- `return y + x;`
      wp_load Hy
      wp_pures
      wp_load Hx
      wp_int_checked
      · constructor <;> omega
      wp_pures
      ipureintro
      intro x' hx'
      simp only [List.cons.injEq, Value.int.injEq, and_true] at hx'
      subst hx'
      congr 2
      omega
    · simp only [PointsToVals]
      icases Hls with ⟨-, Hf⟩
      iexfalso
      iexact Hf

end Specs

/--
**`f(20)` is safe and returns `41`**, for every choice of `SemanticParams` whose function table
declares `f` as `fDecl` (`hf`), with integer mode `checked` (`hmode`): running it from the empty
state never gets stuck (`.NotStuck`), and if it completes, it completes normally with `41`
(`o = .normal (.int 41)`).
-/
theorem f_twenty [P : SemanticParams SimpleType] (hf : P.functions "f" = some fDecl)
    (hmode : P.intModeOf "f" = .checked) :
    adequate .NotStuck (LoweredExpr.call "f" [.int 20] int) State.empty
      (fun o _ => o = .normal (.int 41)) := by
  refine adequacy (GF := DartS SimpleType) _ _ _ ?_
  intro inst
  iintro -
  ihave #Hspec := f_spec (GF := DartS SimpleType) hf hmode
  -- Evaluate the argument, `20`, and then use `f`'s specification.
  wp_pures
  wp_call_spec Hspec
  isplitr
  · ipureintro
    exact ⟨20, rfl, by decide, by decide⟩
  iintro %o %ho
  ipureintro
  exact ho 20 rfl

end DartSemantics.Tests.LetSpecs
