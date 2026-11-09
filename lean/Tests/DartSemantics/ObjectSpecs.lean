module
import DartSemantics
import DartLang.SimpleTypes

/-!
# Programs with objects proved correct with the program logic

Classes, on `SimpleType`. The main example is a counter object, used in a loop:

```dart
class Counter {
  int _n;
  Counter() : _n = 0;
  void inc() { _n = _n + 1; }
  int get value => _n;
}

int countTo(int k) {
  var c = Counter();
  var i = 0;
  while (i < k) { c.inc(); i = i + 1; }
  return c.value;
}
```

Its specification (`countTo_spec`): in integer mode `checked`, called with a `k` such that
`0 ≤ k ≤ 2⁶²`, `countTo(k)` returns `k`. The proof uses specifications of `inc` and `value`
(`inc_spec` and `value_spec`, which are `MemberSpec`s), for an object whose instance variable `_n`
is at a given location `ℓf` and holds a given integer `n`: calling `inc` takes the ownership of
`ℓf` and gives it back incremented (separation logic's frame rule keeps everything else as it
was), and reading `value` gives `n`. The object's header (a persistent points-to for its own
cell) says which class it is, and so which members its names dispatch to. The loop's invariant is
that `i` and `_n` hold the same `i₀`, with `0 ≤ i₀ ≤ k`. Adequacy then turns the specification into
an ordinary Lean theorem about running `countTo(5)` (`countTo_five`).

A second, smaller example (`g_spec`) shows dynamic dispatch on an overriding method:

```dart
class A { int f() => 1; }
class B extends A { int f() => 2; }
int g(A a) => a.f();
```

`g` applied to a `B` returns `2`. Reading `a`, of static type `A`, passes its promotion check since
`B` is a subtype of `A` (see `SimpleType.Class`).
-/

namespace DartSemantics.Tests.ObjectSpecs

open DartLang SimpleType Iris Iris.BI Iris.ProgramLogic

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Variable" => Variable (τ := SimpleType)
local notation "Property" => Property (τ := SimpleType)
local notation "Value" => Value (τ := SimpleType)
local notation "Outcome" => Outcome (τ := SimpleType)
local notation "Cell" => Cell (τ := SimpleType)

/-! ## The counter -/

/-- The class type of `Counter`. -/
abbrev tCounter : SimpleType := .Class "Counter" []

/-- `this`, in the members of `Counter`. -/
def thisC : Variable := { name := "this", type := tCounter }
/-- The formal parameter `int k` of `countTo`. -/
def k : Variable := { name := "k", type := int }
/-- The local variable `c` of `countTo`, of type `Counter`. -/
def c : Variable := { name := "c", type := tCounter }
/-- The local variable `i` of `countTo`, of type `int`. -/
def i : Variable := { name := "i", type := int }

/-
The variables are different. Resolving one of them to its cell leaves the others alone; `simp` uses
these facts to see that.
-/

theorem c_ne_k : c ≠ k := by simp [c, k]
theorem i_ne_k : i ≠ k := by simp [i, k]
theorem i_ne_c : i ≠ c := by simp [i, c]

/-- The instance variable `_n` of `Counter`, read through its implicit getter. -/
def pn : Property := ⟨"_n", int, false⟩
/-- The getter `value` of `Counter`. -/
def pvalue : Property := ⟨"value", int, false⟩

/--
The dispatch table of `Counter`: the implicit getter and setter of `_n` (whose key, unique among
the instance variables of `Counter`'s instances, is `"Counter::_n"`), and the members `inc` and
`value`, which `Counter` provides.
-/
def counterDispatch : String → Option Member
  | "_n" | "_n=" => some (.field "Counter::_n")
  | "inc" => some (.proc "Counter.inc" "Counter")
  | "value" => some (.proc "Counter.value" "Counter")
  | _ => none

/-- The declaration of `Counter`, a direct subclass of `Object`, with one instance variable. -/
def counterDecl : ClassDecl (τ := SimpleType) :=
  ⟨tCounter, ["Counter::_n"], counterDispatch, none⟩

/-- The declaration of `Counter`'s constructor, whose initializer list initializes `_n` to `0`. -/
def counterNewDecl : ConstructorDecl (τ := SimpleType) :=
  ⟨"Counter", thisC, [], [.initField (.var thisC tCounter) "Counter::_n" (.int 0)], .block []⟩

/-- The declaration of `inc`. The integer operator's mode is filled in when `inc` runs. -/
def incDecl : MemberDecl (τ := SimpleType) :=
  ⟨thisC, [], .block [.propertySet (.var thisC tCounter) "_n"
    (.intBin .add none (.propertyGet (.var thisC tCounter) pn int) (.int 1))]⟩

/-- The declaration of the getter `value`. -/
def valueDecl : MemberDecl (τ := SimpleType) :=
  ⟨thisC, [], .ret (.propertyGet (.var thisC tCounter) pn int)⟩

/--
The declaration of `countTo`. As in `LoopSpecs.lean`, the `while` loop is a loop inside a labeled
statement `L`, with its body inside a labeled statement `C`.
-/
def countToDecl : FunctionDecl (τ := SimpleType) :=
  ⟨[k], .block [
    .declare c tCounter false, .variableSet c (.new "Counter.new" [] tCounter),
    .declare i int false, .variableSet i (.int 0),
    .labeled "L" (.loop (.cond (.intBin .lt none (.var i int) (.var k int))
      (.labeled "C" (.block [
        .methodCall (.var c tCounter) "inc" [] Null,
        .variableSet i (.intBin .add none (.var i int) (.int 1))]))
      (.brk "L") Null)),
    .ret (.propertyGet (.var c tCounter) pvalue int)]⟩

/-- A number between `0` and `2⁶²` is in 64-bit range. -/
theorem inRange {x : Int} (h₀ : 0 ≤ x) (h₁ : x ≤ 2 ^ 62) : -2 ^ 63 ≤ x ∧ x < 2 ^ 63 := by
  constructor <;> omega

/-- The precondition of `countTo`: it's called with one integer argument `k`, `0 ≤ k ≤ 2⁶²`. -/
abbrev countToPre {GF : BundledGFunctors} (vs : List Value) : IProp GF :=
  iprop(⌜∃ k, vs = [.int k] ∧ 0 ≤ k ∧ k ≤ 2 ^ 62⌝)

/-- The postcondition of `countTo`: called with `k`, it returns `k`. -/
abbrev countToPost {GF : BundledGFunctors} (vs : List Value) (o : Outcome) : IProp GF :=
  iprop(⌜∀ k, vs = [.int k] → o = .normal (.int k)⌝)

/-! ## The overriding method -/

/-- The class type of `A`. -/
abbrev tA : SimpleType := .Class "A" []
/-- The class type of `B`, a subclass of `A`. -/
abbrev tB : SimpleType := .Class "B" ["A"]

/-- `this`, in the members of `B`. -/
def thisB : Variable := { name := "this", type := tB }
/-- The formal parameter `A a` of `g`. -/
def a : Variable := { name := "a", type := tA }

/-- The declaration of `B`'s `f`, which returns `2`. -/
def bfDecl : MemberDecl (τ := SimpleType) := ⟨thisB, [], .ret (.int 2)⟩

/-- The dispatch table of `B`: its own `f`, which overrides `A`'s. -/
def bDispatch : String → Option Member
  | "f" => some (.proc "B.f" "B")
  | _ => none

/-- The declaration of `B`, a direct subclass of `A`, with no instance variables. -/
def bDecl : ClassDecl (τ := SimpleType) := ⟨tB, [], bDispatch, some "A"⟩

/-- The declaration of `g`, whose body is `return a.f();`. -/
def gDecl : FunctionDecl (τ := SimpleType) :=
  ⟨[a], .ret (.methodCall (.var a tA) "f" [] int)⟩

section Specs

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS SimpleType hlc GF]
variable [P : SemanticParams SimpleType]

include hlc

/--
The precondition of `inc`, for a `Counter` whose instance variable `_n` is at `ℓf` and holds `n`:
the receiver is a `Counter` at some `ℓ` (whose header is `ℓ ↦{.discard} .object "Counter" …`), its
instance variable `_n` is at `ℓf` and holds `n`, which is owned, and `n + 1` is in 64-bit range.
-/
abbrev incPre (ℓf : Loc) (n : Int) (vs : List Value) : IProp GF :=
  iprop(∃ ℓ, ⌜vs = [.obj ℓ] ∧ -2 ^ 63 ≤ n + 1 ∧ n + 1 < 2 ^ 63⌝ ∗
    ℓ ↦{.discard} (.object "Counter" tCounter [("Counter::_n", ℓf)] : Cell) ∗
    ℓf ↦ (.val (.int n) : Cell))

/-- The postcondition of `inc`: it completes normally, and `_n` (at `ℓf`) now holds `n + 1`. -/
abbrev incPost (ℓf : Loc) (n : Int) (_vs : List Value) (o : Outcome) : IProp GF :=
  iprop(⌜o = .normal .null⌝ ∗ ℓf ↦ (.val (.int (n + 1)) : Cell))

/--
The precondition of the getter `value`, for a `Counter` whose instance variable `_n` is at `ℓf` and
holds `n`: the receiver is a `Counter` at some `ℓ`, whose instance variable `_n` is at `ℓf` and
holds `n`, which is owned.
-/
abbrev valuePre (ℓf : Loc) (n : Int) (vs : List Value) : IProp GF :=
  iprop(∃ ℓ, ⌜vs = [.obj ℓ]⌝ ∗
    ℓ ↦{.discard} (.object "Counter" tCounter [("Counter::_n", ℓf)] : Cell) ∗
    ℓf ↦ (.val (.int n) : Cell))

/--
The postcondition of `value`: it completes normally with `n` (the getter's `return` becomes the
completion of the running call), and `_n` (at `ℓf`) still holds `n`.
-/
abbrev valuePost (ℓf : Loc) (n : Int) (_vs : List Value) (o : Outcome) : IProp GF :=
  iprop(⌜o = .normal (.int n)⌝ ∗ ℓf ↦ (.val (.int n) : Cell))

/--
`inc` meets its specification, for each location `ℓf` and integer `n`, if the member table declares
it as `incDecl` (`hinc`), the class table declares `Counter` as `counterDecl` (`hcls`), and `inc`'s
integer mode is `checked` (`hmode`).
-/
theorem inc_spec (hinc : P.members "Counter.inc" = some incDecl)
    (hcls : P.classes "Counter" = some counterDecl)
    (hmode : P.intModeOf "Counter.inc" = .checked) (ℓf : Loc) (n : Int) :
    ⊢@{IProp GF} MemberSpec "Counter.inc" "Counter" (incPre ℓf n) (incPost ℓf n) := by
  have hget : P.dispatch "Counter" "_n" = some (.field "Counter::_n") := by
    simp [SemanticParams.dispatch, hcls, counterDecl, counterDispatch]
  have hset : P.dispatch "Counter" ("_n" ++ "=") = some (.field "Counter::_n") := by
    simp [SemanticParams.dispatch, hcls, counterDecl, counterDispatch]
  refine MemberSpec.intro hinc fun vs ℓs T => ?_
  iintro ⟨-, ⟨%ℓ, %⟨hvs, hr₁, hr₂⟩, #Ho, Hf⟩, Hls⟩
  subst hvs
  -- One cell is allocated, for `this`; `PointsToVals` is `False` for any other number of cells.
  rcases ℓs with _ | ⟨ℓt, _ | ⟨ℓ', ℓs⟩⟩
  · simp only [PointsToVals]
    iexfalso
    iexact Hls
  · simp only [PointsToVals, incDecl]
    dart_bind_params
    simp only [hmode]
    icases Hls with ⟨Ht, -⟩
    -- `this._n = this._n + 1;`
    wp_pures
    wp_load Ht
    wp_pures
    wp_load Ht
    wp_load Hf
    wp_pures
    wp_int_checked
    · exact ⟨hr₁, hr₂⟩
    iapply wp_propertySet_field (c := .val (.int n)) (fs := [("Counter::_n", ℓf)]) (ℓf := ℓf)
      hset rfl rfl
    isplitr
    · iexact Ho
    isplitl [Hf]
    · inext
      iexact Hf
    inext
    iintro Hf
    wp_pures
    isplitr
    · ipureintro
      rfl
    · iexact Hf
  · simp only [PointsToVals]
    icases Hls with ⟨-, Hf⟩
    iexfalso
    iexact Hf

omit P in
/-- The ownership of the cells at `ℓs`, holding just `v`, is that of one cell, holding `v`. -/
theorem pointsToVals_one {ℓs : List Loc} {v : Value} :
    PointsToVals (GF := GF) ℓs [v] ⊢ ∃ ℓ, ⌜ℓs = [ℓ]⌝ ∗ ℓ ↦ (.val v : Cell) := by
  rcases ℓs with _ | ⟨ℓ, _ | ⟨ℓ', ℓs⟩⟩
  · simp only [PointsToVals]
    iintro H
    iexfalso
    iexact H
  · simp only [PointsToVals]
    iintro ⟨H, -⟩
    iexists ℓ
    isplitr
    · ipureintro
      rfl
    · iexact H
  · simp only [PointsToVals]
    iintro ⟨-, H⟩
    iexfalso
    iexact H

/--
The getter `value` meets its specification, for each location `ℓf` and integer `n`, if the member
table declares it as `valueDecl` (`hval`), and the class table declares `Counter` as `counterDecl`
(`hcls`).
-/
theorem value_spec (hval : P.members "Counter.value" = some valueDecl)
    (hcls : P.classes "Counter" = some counterDecl) (ℓf : Loc) (n : Int) :
    ⊢@{IProp GF} MemberSpec "Counter.value" "Counter" (valuePre ℓf n) (valuePost ℓf n) := by
  have hget : P.dispatch "Counter" "_n" = some (.field "Counter::_n") := by
    simp [SemanticParams.dispatch, hcls, counterDecl, counterDispatch]
  refine MemberSpec.intro hval fun vs ℓs T => ?_
  iintro ⟨-, ⟨%ℓ, %hvs, #Ho, Hf⟩, Hls⟩
  subst hvs
  icases pointsToVals_one $$ Hls with ⟨%ℓt, %hℓs, Ht⟩
  subst hℓs
  simp only [valueDecl]
  dart_bind_params
  -- `return this._n;`
  wp_pures
  wp_load Ht
  wp_load Hf
  wp_pures
  isplitr
  · ipureintro
    rfl
  · iexact Hf

-- The proof steps through the whole body, which takes more than the default budget of
-- `maxHeartbeats` (Lean's limit on the work a single declaration may take to elaborate).
set_option maxHeartbeats 1000000 in
/--
`countTo` meets its specification (`FunSpec "countTo" countToPre countToPost`), if the program's
tables declare `countTo` as `countToDecl` (`hf`), `Counter` as `counterDecl` (`hcls`), its
constructor as `counterNewDecl` (`hnew`), and its members as `incDecl` (`hinc`) and `valueDecl`
(`hval`), and the integer modes of `countTo` (`hmode`) and `inc` (`hmodeInc`) are `checked`.
-/
theorem countTo_spec (hf : P.functions "countTo" = some countToDecl)
    (hcls : P.classes "Counter" = some counterDecl)
    (hnew : P.constructors "Counter.new" = some counterNewDecl)
    (hinc : P.members "Counter.inc" = some incDecl)
    (hval : P.members "Counter.value" = some valueDecl)
    (hmode : P.intModeOf "countTo" = .checked) (hmodeInc : P.intModeOf "Counter.inc" = .checked) :
    ⊢@{IProp GF} FunSpec "countTo" countToPre countToPost := by
  have hdinc : P.dispatch "Counter" "inc" = some (.proc "Counter.inc" "Counter") := by
    simp [SemanticParams.dispatch, hcls, counterDecl, counterDispatch]
  have hdval : P.dispatch "Counter" pvalue.name = some (.proc "Counter.value" "Counter") := by
    simp [SemanticParams.dispatch, hcls, counterDecl, counterDispatch, pvalue]
  refine FunSpec.intro hf (fun vs => ?_) fun vs T ℓs => ?_
  · -- There's one argument per formal parameter.
    iintro %⟨k₀, hk, -⟩
    ipureintro
    simp [hk, countToDecl]
  iintro ⟨-, %⟨k₀, hk, h₀, hk₀⟩, Hls⟩
  subst hk
  icases pointsToVals_one $$ Hls with ⟨%ℓk, %hℓs, Hk⟩
  subst hℓs
  simp only [countToDecl, hmode]
  dart_bind_params
  -- Binding `k` resolves only `k`: the local variables are different variables.
  simp only [c_ne_k, i_ne_k, ite_false]
  refine DartSemantics.tac_wp_frame (τ := SimpleType) ?_
  -- `var c = Counter();`: allocate the object, whose instance variable `_n` starts out
  -- uninitialized, and run the constructor, which initializes `_n` to `0`.
  wp_alloc ℓc Hc
  simp only [i_ne_c, ite_false]
  wp_pures
  wp_new hnew hcls
  iintro %ℓ %ℓs %hlen #Ho Hu
  simp only [counterDecl, List.length_cons, List.length_nil] at hlen
  obtain ⟨ℓf, rfl⟩ := List.length_eq_one_iff.1 hlen
  simp only [counterDecl, List.zip_cons_cons, List.zip_nil_left, PointsToUninit]
  icases Hu with ⟨Hf, -⟩
  wp_pures
  wp_ctor_run hnew
  iintro %ℓs' Hls'
  icases pointsToVals_one $$ Hls' with ⟨%ℓt, %hℓs', Ht⟩
  subst hℓs'
  simp only [counterNewDecl, List.cons_append, List.nil_append]
  dart_bind_params
  wp_pures
  wp_load Ht
  wp_pures
  iapply wp_initField (c := .uninit) (fs := [("Counter::_n", ℓf)]) (ℓf := ℓf) rfl
    rfl
  isplitr
  · iexact Ho
  isplitl [Hf]
  · inext
    iexact Hf
  inext
  iintro Hf
  wp_pures
  wp_store Hc
  wp_pures
  -- `var i = 0;`
  wp_alloc ℓi Hi
  wp_pures
  wp_store Hi
  wp_pures
  -- The loop, with its invariant: `i` and `c._n` hold the same `i₀`, with `0 ≤ i₀ ≤ k`.
  refine DartSemantics.tac_wp_loop_inv (τ := SimpleType) iprop(∃ i₀ : Int,
      ℓi ↦ (.val (.int i₀) : Cell) ∗ ℓf ↦ (.val (.int i₀) : Cell) ∗
      ℓc ↦ (.val (.obj ℓ) : Cell) ∗ ℓk ↦ (.val (.int k₀) : Cell) ∗
      ℓ ↦{.discard} (.object "Counter" tCounter [("Counter::_n", ℓf)] : Cell) ∗
      ⌜0 ≤ i₀ ∧ i₀ ≤ k₀⌝) ?_ ?_
  · -- The invariant holds before the loop: `i` and `c._n` are `0`.
    iexists 0
    iframe Hi
    iframe Hf
    iframe Hc
    iframe Hk
    isplitr
    · iexact Ho
    · ipureintro
      exact ⟨Int.le_refl 0, h₀⟩
  · -- Each iteration: read `i < k`.
    iintro ⟨%i₀, Hi, Hf, Hc, Hk, #Ho, %⟨hi₀, hik⟩⟩
    wp_pures
    wp_load Hi
    wp_pures
    wp_load Hk
    wp_pures
    by_cases hlt : i₀ < k₀
    · -- `i < k`: run the body, `c.inc(); i = i + 1;`.
      simp only [decide_eq_true hlt]
      wp_pures
      wp_load Hc
      ihave #Hinc := inc_spec (GF := GF) hinc hcls hmodeInc ℓf i₀
      wp_method_spec Hinc hdinc hinc
      isplitl [Hf]
      · iexists ℓ
        isplitr
        · ipureintro
          exact ⟨rfl, by omega, by omega⟩
        isplitr
        · iexact Ho
        · iexact Hf
      inext
      iintro %o ⟨%ho, Hf⟩
      subst ho
      wp_pures
      wp_load Hi
      wp_pures
      wp_int_checked
      · exact inRange (by omega) (by omega)
      wp_store Hi
      wp_pures
      -- The invariant holds again.
      inext
      iexists i₀ + 1
      iframe Hi
      iframe Hf
      iframe Hc
      iframe Hk
      isplitr
      · iexact Ho
      · ipureintro
        omega
    · -- `i ≥ k`, so `i = k`: break out of the loop, and return `c.value`.
      have hi : i₀ = k₀ := by omega
      subst hi
      simp only [decide_eq_false hlt]
      wp_pures
      wp_load Hc
      ihave #Hval := value_spec (GF := GF) hval hcls ℓf i₀
      iapply MemberSpec.wp_propertyGet hdval hval rfl
      isplitr
      · iexact Ho
      isplitr
      · inext
        iexact Hval
      isplitl [Hf]
      · iexists ℓ
        isplitr
        · ipureintro
          rfl
        isplitr
        · iexact Ho
        · iexact Hf
      inext
      iintro %o ⟨%ho, -⟩
      subst ho
      dart_wp_tidy
      -- The getter's result passes its promotion check, and is returned.
      iapply wp_checkPromotion (S := int) (by decide)
      isplitr
      · iapply HasDynamicType.int
      inext
      wp_pures
      ipureintro
      intro k' hk'
      simp_all

/-! ## Dispatch on an overriding method -/

/--
The precondition of `g`: it's called with one argument, a `B` (whose header is
`ℓ ↦{.discard} .object "B" tB fs`, for some instance variables `fs`).
-/
abbrev gPre (vs : List Value) : IProp GF :=
  iprop(∃ ℓ fs, ⌜vs = [.obj ℓ]⌝ ∗ ℓ ↦{.discard} (.object "B" tB fs : Cell))

/-- The postcondition of `g`: it returns `2`. -/
abbrev gPost (_vs : List Value) (o : Outcome) : IProp GF :=
  iprop(⌜o = .normal (.int 2)⌝)

/--
`g` meets its specification (`FunSpec "g" gPre gPost`), if the program's tables declare `g` as
`gDecl` (`hg`), `B` as `bDecl` (`hcls`), and `B`'s `f` as `bfDecl` (`hbf`).
-/
theorem g_spec (hg : P.functions "g" = some gDecl) (hcls : P.classes "B" = some bDecl)
    (hbf : P.members "B.f" = some bfDecl) :
    ⊢@{IProp GF} FunSpec "g" gPre gPost := by
  have hd : P.dispatch "B" "f" = some (.proc "B.f" "B") := by
    simp [SemanticParams.dispatch, hcls, bDecl, bDispatch]
  refine FunSpec.intro hg (fun vs => ?_) fun vs T ℓs => ?_
  · -- There's one argument per formal parameter.
    iintro ⟨%ℓ, %fs, %hvs, -⟩
    ipureintro
    simp [hvs, gDecl]
  iintro ⟨-, ⟨%ℓ, %fs, %hvs, #Hh⟩, Hls⟩
  subst hvs
  icases pointsToVals_one $$ Hls with ⟨%ℓa, %hℓs, Ha⟩
  subst hℓs
  simp only [gDecl]
  dart_bind_params
  refine DartSemantics.tac_wp_frame (τ := SimpleType) ?_
  -- `return a.f();`: reading `a` passes its promotion check, since `B` is a subtype of `A`; then
  -- `f` dispatches to `B`'s `f`.
  wp_pures
  wp_load Ha
  wp_method hd hbf
  iintro %ℓs Hls
  icases pointsToVals_one $$ Hls with ⟨%ℓt, %hℓs, -⟩
  subst hℓs
  simp only [bfDecl]
  dart_bind_params
  wp_pures
  ipureintro
  rfl

end Specs

/--
**`countTo(5)` is safe and returns `5`**, for every choice of `SemanticParams` whose tables declare
`countTo` as `countToDecl` (`hf`), `Counter` as `counterDecl` (`hcls`), its constructor as
`counterNewDecl` (`hnew`), and its members as `incDecl` (`hinc`) and `valueDecl` (`hval`), with
integer mode `checked` for `countTo` (`hmode`) and `inc` (`hmodeInc`): running it from the empty
state never gets stuck (`.NotStuck`), and if it completes, it completes normally with `5`.
-/
theorem countTo_five [P : SemanticParams SimpleType] (hf : P.functions "countTo" = some countToDecl)
    (hcls : P.classes "Counter" = some counterDecl)
    (hnew : P.constructors "Counter.new" = some counterNewDecl)
    (hinc : P.members "Counter.inc" = some incDecl)
    (hval : P.members "Counter.value" = some valueDecl)
    (hmode : P.intModeOf "countTo" = .checked) (hmodeInc : P.intModeOf "Counter.inc" = .checked) :
    adequate .NotStuck (LoweredExpr.call "countTo" [.int 5] int) State.empty
      (fun o _ => o = .normal (.int 5)) := by
  refine adequacy (GF := DartS SimpleType) _ _ _ ?_
  intro inst
  iintro -
  ihave #Hspec := countTo_spec (GF := DartS SimpleType) hf hcls hnew hinc hval hmode hmodeInc
  -- Evaluate the argument, `5`, and then use `countTo`'s specification.
  wp_pures
  wp_call_spec Hspec
  isplitr
  · ipureintro
    exact ⟨5, rfl, by decide, by decide⟩
  iintro %o %ho
  ipureintro
  exact ho 5 rfl

end DartSemantics.Tests.ObjectSpecs
