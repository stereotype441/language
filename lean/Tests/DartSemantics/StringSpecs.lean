module
import DartSemantics
import DartLang.SimpleTypes

/-!
# A program with strings, proved correct with the program logic

A top-level function that builds a string by interpolation, on `SimpleType`:

```dart
String describe(int n) => "n = $n";
```

`describe` gets a specification (`FunSpec`), proved for every choice of `SemanticParams` whose
function table declares it as above: called with `n`, it returns a new string (`Fresh`) holding
`"n = "` followed by `n`'s decimal form. Adequacy then turns it into ordinary Lean theorems about
running some expressions that use it:
- `Expect.equals(describe(42), "n = 42")` passes: the two strings are equal, although they're
  different objects;
- `identical("ab", "ab")` is `true`: a constant has one canonical object (`IsConst.agree`);
- `identical(describe(1), describe(1))` is `false`, since each call returns a new string
  (`Fresh.ne`), although `describe(1) == describe(1)` is `true`.
-/

namespace DartSemantics.Tests.StringSpecs

open DartLang Iris Iris.BI Iris.ProgramLogic

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Variable" => Variable (τ := SimpleType)
local notation "Value" => Value (τ := SimpleType)
local notation "Outcome" => Outcome (τ := SimpleType)
local notation "Cell" => Cell (τ := SimpleType)

/-- The formal parameter `int n`. -/
def n : Variable := { name := "n", type := .int }

/-- `String describe(int n) => "n = $n";` -/
def describeDecl : FunctionDecl (τ := SimpleType) :=
  ⟨[n], .ret (.concat [.constant (.string (DartString.ofString "n = ")), .var n .int])⟩

/-- The code units of the string that `describe(k)` returns: `"n = "`, then `k`'s decimal form. -/
def describeStr (k : Int) : List UInt16 :=
  DartString.ofString "n = " ++ DartString.ofString (toString k)

/-
The specification's precondition and postcondition are `abbrev`s, so that proof mode can see their
structure, and introduce them with patterns.
-/

/-- The precondition of `describe`: it's called with one integer argument. -/
abbrev intArg {GF : BundledGFunctors} (vs : List Value) : IProp GF :=
  iprop(⌜∃ k, vs = [.int k]⌝)

/--
The postcondition of `describe`: called with `k`, it returns a new string (`Fresh`) holding
`describeStr k`.
-/
abbrev describePost {hlc : HasLC} {GF : BundledGFunctors} [DartGS SimpleType hlc GF]
    (vs : List Value) (o : Outcome) : IProp GF :=
  iprop(∃ k ℓ, ⌜vs = [.int k] ∧ o = .normal (.obj ℓ)⌝ ∗
    ℓ ↦{.discard} (.string (describeStr k) : Cell) ∗ Fresh SimpleType ℓ)

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS SimpleType hlc GF]
variable [P : SemanticParams SimpleType]

include hlc

/--
`describe` meets its specification (`FunSpec "describe" intArg describePost`), if the function
table declares it as `describeDecl` (`hdescribe`).
-/
theorem describe_spec (hdescribe : P.functions "describe" = some describeDecl) :
    ⊢@{IProp GF} FunSpec "describe" intArg describePost := by
  refine FunSpec.intro hdescribe (fun vs => ?_) fun vs T ℓs => ?_
  · -- There's one argument per formal parameter.
    iintro %⟨k, hk⟩
    ipureintro
    simp [hk, describeDecl]
  · iintro ⟨-, %⟨k, hk⟩, Hls⟩
    subst hk
    -- One cell is allocated, for `n`; `PointsToVals` is `False` for any other number of cells.
    rcases ℓs with _ | ⟨ℓ, _ | ⟨ℓ', ℓs⟩⟩
    · simp only [PointsToVals]
      iexfalso
      iexact Hls
    · simp only [PointsToVals, describeDecl]
      dart_bind_params
      icases Hls with ⟨Hl, -⟩
      -- Evaluate the constant `"n = "` to its canonical object.
      wp_pures
      wp_const ℓ₀ Hl₀ Hc₀
      -- Read `n`, and concatenate the parts' string forms.
      wp_pures
      wp_load Hl
      wp_concat [DartString.ofString "n = ", DartString.ofString (toString k)] ℓ₁ Hl₁ Hf₁
      -- `return` the new string.
      wp_pures
      iexists k, ℓ₁
      isplitr
      · ipureintro
        exact ⟨rfl, rfl⟩
      isplitr
      · simp only [describeStr, List.flatten_cons, List.flatten_nil, List.append_nil]
        iexact Hl₁
      · iexact Hf₁
    · simp only [PointsToVals]
      icases Hls with ⟨-, Hf⟩
      iexfalso
      iexact Hf

end Specs

/-
Proving that two strings are equal means computing their code units. Strings in Lean are
UTF-8 byte arrays whose definitions aren't exposed to proofs in this module, so the computation
goes through lemmas: converting a concatenation of Lean strings converts each one
(`ofString_append`), and the decimal form of `42` is `"42"` (`toString_42`).
-/

/-- Converting the concatenation of Lean strings `a` and `b` concatenates their code units. -/
theorem ofString_append (a b : String) :
    DartString.ofString (a ++ b) = DartString.ofString a ++ DartString.ofString b := by
  simp [DartString.ofString, String.toList_append, List.flatMap_append]

/-- The decimal form of the integer `42` is `"42"`. -/
theorem toString_42 : toString (42 : Int) = "42" := by
  have h₄ : Nat.digitChar 4 = '4' := Nat.digitChar_eq_four.2 rfl
  have h₂ : Nat.digitChar 2 = '2' := Nat.digitChar_eq_two.2 rfl
  simp [Int.repr_eq_ite, Nat.repr_of_ge, Nat.repr_of_lt, h₄, h₂]

/--
**`Expect.equals(describe(42), "n = 42")` passes**, for every choice of `SemanticParams` whose
function table declares `describe` as `describeDecl` (`hdescribe`): running it from the empty state
never gets stuck (`.NotStuck`), and if it completes, it completes normally
(`o = .normal .null`).
-/
theorem expect_describe_42 [P : SemanticParams SimpleType]
    (hdescribe : P.functions "describe" = some describeDecl) :
    adequate .NotStuck
      (LoweredExpr.checkEq (.call "describe" [.int 42] SimpleType.String)
        (.constant (.string (DartString.ofString "n = 42"))))
      (State.empty (τ := SimpleType)) (fun (o : Outcome) _ => o = .normal .null) := by
  refine adequacy (GF := DartS SimpleType) _ _ _ ?_
  intro inst
  iintro -
  ihave #Hd := describe_spec (GF := DartS SimpleType) hdescribe
  -- Evaluate the argument, `42`, and then use `describe`'s specification.
  wp_pures
  wp_call_spec Hd
  isplitr
  · ipureintro
    exact ⟨42, rfl⟩
  iintro %o ⟨%k, %ℓ, %⟨hvs, rfl⟩, #Hl, -⟩
  obtain rfl : k = 42 := by simpa [tidy_splitVals_val, tidy_splitVals_nil] using hvs.symm
  -- Evaluate the constant `"n = 42"`.
  wp_pures
  wp_const ℓ' Hl' Hc'
  -- The two strings have the same code units.
  have h : describeStr 42 = DartString.ofString "n = 42" := by
    rw [describeStr, toString_42, ← ofString_append]
    rfl
  rw [h]
  iapply wp_checkEq_string_pass
  isplitr
  · iexact Hl
  isplitr
  · iexact Hl'
  inext
  ipureintro
  rfl

/--
**`identical("ab", "ab")` is `true`**: running it from the empty state never gets stuck, and if it
completes, it completes normally with `true`. The two evaluations of the constant give its
canonical object (`IsConst.agree`).
-/
theorem identical_constants [SemanticParams SimpleType] :
    adequate .NotStuck
      (LoweredExpr.identical (τ := SimpleType) (.constant (.string (DartString.ofString "ab")))
        (.constant (.string (DartString.ofString "ab"))))
      (State.empty (τ := SimpleType)) (fun (o : Outcome) _ => o = .normal (.bool true)) := by
  refine adequacy (GF := DartS SimpleType) _ _ _ ?_
  intro inst
  iintro -
  wp_pures
  wp_const ℓ₁ Hl₁ Hc₁
  wp_pures
  wp_const ℓ₂ Hl₂ Hc₂
  ihave %heq : ⌜ℓ₁ = ℓ₂⌝ $$ [Hc₁ Hc₂]
  · iapply IsConst.agree
    isplitl
    · iexact Hc₁
    · iexact Hc₂
  subst heq
  wp_pures
  ipureintro
  simp

/--
**`identical(describe(1), describe(1))` is `false`**, for every choice of `SemanticParams` whose
function table declares `describe` as `describeDecl` (`hdescribe`): running it from the empty state
never gets stuck, and if it completes, it completes normally with `false`. Each call returns a new
string (`Fresh.ne`).
-/
theorem not_identical_describe [P : SemanticParams SimpleType]
    (hdescribe : P.functions "describe" = some describeDecl) :
    adequate .NotStuck
      (LoweredExpr.identical (.call "describe" [.int 1] SimpleType.String)
        (.call "describe" [.int 1] SimpleType.String))
      (State.empty (τ := SimpleType)) (fun (o : Outcome) _ => o = .normal (.bool false)) := by
  refine adequacy (GF := DartS SimpleType) _ _ _ ?_
  intro inst
  iintro -
  ihave #Hd := describe_spec (GF := DartS SimpleType) hdescribe
  wp_pures
  wp_call_spec Hd
  isplitr
  · ipureintro
    exact ⟨1, rfl⟩
  iintro %o₁ ⟨%k₁, %ℓ₁, %⟨-, rfl⟩, -, Hf₁⟩
  wp_pures
  wp_call_spec Hd
  isplitr
  · ipureintro
    exact ⟨1, rfl⟩
  iintro %o₂ ⟨%k₂, %ℓ₂, %⟨-, rfl⟩, -, Hf₂⟩
  ihave %hne := Fresh.ne $$ [$Hf₁ $Hf₂]
  wp_pures
  ipureintro
  simp [hne]

/--
**`describe(1) == describe(1)` is `true`**, for every choice of `SemanticParams` whose function
table declares `describe` as `describeDecl` (`hdescribe`): running it from the empty state never
gets stuck, and if it completes, it completes normally with `true`. The two strings are different
objects (see `not_identical_describe`), with the same code units.
-/
theorem eq_describe [P : SemanticParams SimpleType]
    (hdescribe : P.functions "describe" = some describeDecl) :
    adequate .NotStuck
      (LoweredExpr.primEq (.call "describe" [.int 1] SimpleType.String)
        (.call "describe" [.int 1] SimpleType.String))
      (State.empty (τ := SimpleType)) (fun (o : Outcome) _ => o = .normal (.bool true)) := by
  refine adequacy (GF := DartS SimpleType) _ _ _ ?_
  intro inst
  iintro -
  ihave #Hd := describe_spec (GF := DartS SimpleType) hdescribe
  wp_pures
  wp_call_spec Hd
  isplitr
  · ipureintro
    exact ⟨1, rfl⟩
  iintro %o₁ ⟨%k₁, %ℓ₁, %⟨hvs₁, rfl⟩, #Hl₁, -⟩
  obtain rfl : k₁ = 1 := by simpa [tidy_splitVals_val, tidy_splitVals_nil] using hvs₁.symm
  wp_pures
  wp_call_spec Hd
  isplitr
  · ipureintro
    exact ⟨1, rfl⟩
  iintro %o₂ ⟨%k₂, %ℓ₂, %⟨hvs₂, rfl⟩, #Hl₂, -⟩
  obtain rfl : k₂ = 1 := by simpa [tidy_splitVals_val, tidy_splitVals_nil] using hvs₂.symm
  wp_pures
  iapply wp_primEq_string
  isplitr
  · iexact Hl₁
  isplitr
  · iexact Hl₂
  inext
  ipureintro
  simp

end DartSemantics.Tests.StringSpecs
