module
import DartSemantics
import DartLang.SimpleTypes

/-!
# A program with calls, proved correct with the program logic

A program of two top-level functions, on `SimpleType`:

```dart
bool not(bool b) { if (b) return false; return true; }
bool doubleNot(bool b) { return not(not(b)); }
```

Each function gets a specification (`FunSpec`), proved for every choice of `SemanticParams` whose
function table declares the two functions as above: `not` returns the negation of its argument, and
`doubleNot` returns its argument. The proof for `doubleNot` uses the specification of `not` for both
of its calls, rather than stepping through `not`'s body again. Finally, adequacy turns the
specification of `doubleNot` into an ordinary Lean theorem about running `doubleNot(true)`: it never
gets stuck, and if it completes, it returns `true`.

A specification is proved with `FunSpec.intro`, which provides the specification itself for the
body's own calls (by Löb induction), so the same pattern works for recursive functions; these two
don't need it.
-/

namespace DartSemantics.Tests.CallSpecs

open DartLang SimpleType Iris Iris.BI Iris.ProgramLogic

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Variable" => Variable (τ := SimpleType)
local notation "Value" => Value (τ := SimpleType)
local notation "Outcome" => Outcome (τ := SimpleType)

/-- The formal parameter `bool b`. -/
def b : Variable := { name := "b", type := bool }

/-- `bool not(bool b) { if (b) return false; return true; }` -/
def notDecl : FunctionDecl (τ := SimpleType) :=
  ⟨[b], .block [.cond (.var b bool) (.ret (.bool false)) .null Null, .ret (.bool true)]⟩

/-- `bool doubleNot(bool b) { return not(not(b)); }` -/
def doubleNotDecl : FunctionDecl (τ := SimpleType) :=
  ⟨[b], .ret (.call "not" [.call "not" [.var b bool] bool] bool)⟩

/-
The specifications' preconditions and postconditions are pure (`⌜…⌝`). They're `abbrev`s, so that
proof mode can see that they're pure, and introduce them with `%`.
-/

/-- The precondition of both functions: they're called with one boolean argument. -/
abbrev boolArg {GF : BundledGFunctors} (vs : List Value) : IProp GF :=
  iprop(⌜∃ b, vs = [.bool b]⌝)

/-- The postcondition of `not`: called with `b`, it returns `!b`. -/
abbrev notPost {GF : BundledGFunctors} (vs : List Value) (o : Outcome) : IProp GF :=
  iprop(⌜∀ b, vs = [.bool b] → o = .normal (.bool !b)⌝)

/-- The postcondition of `doubleNot`: called with `b`, it returns `b`. -/
abbrev doubleNotPost {GF : BundledGFunctors} (vs : List Value) (o : Outcome) : IProp GF :=
  iprop(⌜∀ b, vs = [.bool b] → o = .normal (.bool b)⌝)

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS SimpleType hlc GF]
variable [P : SemanticParams SimpleType]

include hlc

/--
`not` meets its specification (`FunSpec "not" boolArg notPost`), if the function table declares it
as `notDecl` (`hnot`).
-/
theorem not_spec (hnot : P.functions "not" = some notDecl) :
    ⊢@{IProp GF} FunSpec "not" boolArg notPost := by
  refine FunSpec.intro hnot (fun vs => ?_) fun vs T ℓs => ?_
  · -- There's one argument per formal parameter.
    iintro %⟨b₀, hb⟩
    ipureintro
    simp [hb, notDecl]
  · iintro ⟨-, %⟨b₀, hb⟩, Hls⟩
    subst hb
    -- One cell is allocated, for `b`; `PointsToVals` is `False` for any other number of cells.
    rcases ℓs with _ | ⟨ℓ, _ | ⟨ℓ', ℓs⟩⟩
    · simp only [PointsToVals]
      iexfalso
      iexact Hls
    · simp only [PointsToVals, notDecl]
      dart_bind_params
      icases Hls with ⟨Hl, -⟩
      -- Step to the read of `b` in the condition, and read it.
      wp_pures
      wp_load Hl
      -- Each value of `b` takes a different branch, and then returns.
      cases b₀ <;> wp_pures <;> ipureintro <;> intro b' hb' <;> simp_all
    · simp only [PointsToVals]
      icases Hls with ⟨-, Hf⟩
      iexfalso
      iexact Hf

/--
`doubleNot` meets its specification (`FunSpec "doubleNot" boolArg doubleNotPost`), if the function
table declares `not` as `notDecl` (`hnot`) and `doubleNot` as `doubleNotDecl` (`hdoubleNot`). Its
two calls of `not` use `not`'s specification (`not_spec`).
-/
theorem doubleNot_spec (hnot : P.functions "not" = some notDecl)
    (hdoubleNot : P.functions "doubleNot" = some doubleNotDecl) :
    ⊢@{IProp GF} FunSpec "doubleNot" boolArg doubleNotPost := by
  refine FunSpec.intro hdoubleNot (fun vs => ?_) fun vs T ℓs => ?_
  · iintro %⟨b₀, hb⟩
    ipureintro
    simp [hb, doubleNotDecl]
  · iintro ⟨-, %⟨b₀, hb⟩, Hls⟩
    subst hb
    ihave #Hnot := not_spec (GF := GF) hnot
    rcases ℓs with _ | ⟨ℓ, _ | ⟨ℓ', ℓs⟩⟩
    · simp only [PointsToVals]
      iexfalso
      iexact Hls
    · simp only [PointsToVals, doubleNotDecl]
      dart_bind_params
      icases Hls with ⟨Hl, -⟩
      -- Evaluate the inner call's argument, `b`.
      wp_pures
      wp_load Hl
      -- The inner call, `not(b)`, returns `!b`.
      wp_call_spec Hnot
      isplitr
      · ipureintro
        exact ⟨b₀, rfl⟩
      iintro %o %ho
      obtain rfl := ho b₀ rfl
      wp_pures
      -- The outer call, `not(!b)`, returns `!!b`, which is `b`.
      wp_call_spec Hnot
      isplitr
      · ipureintro
        exact ⟨!b₀, rfl⟩
      iintro %o' %ho'
      obtain rfl := ho' (!b₀) rfl
      -- `return` it.
      wp_pures
      ipureintro
      intro b' hb'
      simp_all
    · simp only [PointsToVals]
      icases Hls with ⟨-, Hf⟩
      iexfalso
      iexact Hf

end Specs

/--
**`doubleNot(true)` is safe and correct**, for every choice of `SemanticParams` whose function
table declares `not` as `notDecl` (`hnot`) and `doubleNot` as `doubleNotDecl` (`hdoubleNot`):
running it from the empty state never gets stuck (`.NotStuck`), and if it completes, it completes
normally with `true` (`o = .normal (.bool true)`).
-/
theorem doubleNot_true [P : SemanticParams SimpleType] (hnot : P.functions "not" = some notDecl)
    (hdoubleNot : P.functions "doubleNot" = some doubleNotDecl) :
    adequate .NotStuck (LoweredExpr.call "doubleNot" [.bool true] bool) State.empty
      (fun o _ => o = .normal (.bool true)) := by
  refine adequacy (GF := DartS SimpleType) _ _ _ ?_
  intro inst
  iintro -
  ihave #HdoubleNot := doubleNot_spec (GF := DartS SimpleType) hnot hdoubleNot
  -- Evaluate the argument, `true`, and then use `doubleNot`'s specification.
  wp_pures
  wp_call_spec HdoubleNot
  isplitr
  · ipureintro
    exact ⟨true, rfl⟩
  iintro %o %ho
  ipureintro
  exact ho true rfl

end DartSemantics.Tests.CallSpecs
