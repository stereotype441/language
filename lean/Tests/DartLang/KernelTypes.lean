module
import DartSemantics
import DartLang.KernelTypes
meta import DartSemantics
meta import DartLang.KernelTypes

/-!
# Tests of `KernelType`

`KernelType` obeys the laws that the typing rules assume (`TypeLaws`), for every class hierarchy.
A sample hierarchy (`sample`) checks individual subtype answers, how types are printed, and that
the interpreter can run programs on `KernelType`.
-/

namespace DartLang.Tests.KernelTypes

open DartLang DartSemantics KernelType

/-- `KernelType H` obeys the laws that the typing rules assume, for every class hierarchy `H`. -/
theorem typeLaws (H : ClassHierarchy) : TypeLaws (KernelType H) where
  not_null_le_bool := by simp [DartTypeRepr.Null, DartTypeRepr.bool, isSubtype, isNullable]
  le_nonNull {S T} hS hST := by
    have hN : (DartTypeRepr.Null : KernelType H) = Null := rfl
    have hNN : (DartTypeRepr.NonNull : KernelType H → KernelType H) = NonNull := rfl
    cases S <;> cases T <;> simp_all [isSubtype, isNullable, NonNull]

/--
A sample class hierarchy:

- `bool` (`0`) and `int` (`1`), the reserved classes, where `int` extends `num`;
- `num` (`2`) and `String` (`3`); and
- `A` (`4`), `B extends A` (`5`) and `C extends B` (`6`).
-/
def sample : ClassHierarchy where
  names := ["bool", "int", "num", "String", "A", "B", "C"]
  supers := [[], [2], [], [], [], [4], [5, 4]]
  wf := by decide

local notation "T" => KernelType sample

/-- `int` in the sample hierarchy. -/
def int : T := .interface 1 false
/-- `num` in the sample hierarchy. -/
def num : T := .interface 2 false
/-- `String` in the sample hierarchy. -/
def string : T := .interface 3 false
/-- Class `A` in the sample hierarchy. -/
def A : T := .interface 4 false
/-- Class `B` in the sample hierarchy. -/
def B : T := .interface 5 false
/-- Class `C` in the sample hierarchy. -/
def C : T := .interface 6 false

/-- The nullable form of a type in the sample hierarchy that has one. -/
def q : T → T
  | .Object _ => .Object true
  | .interface c _ => .interface c true
  | .List U _ => .List U true
  | .Map K V _ => .Map K V true
  | U => U

/-!
## Subtyping

Each example checks one subtype answer in the sample hierarchy, by evaluating `isSubtype`.
-/

example : int ≤ num := by decide
example : int ≤ q num := by decide
example : ¬ q int ≤ num := by decide
example : ¬ num ≤ int := by decide
example : C ≤ A := by decide
example : ¬ A ≤ C := by decide
example : ¬ string ≤ A := by decide
example : (.Null : T) ≤ q C := by decide
example : ¬ (.Null : T) ≤ C := by decide
example : (.Never : T) ≤ C := by decide
example : C ≤ .Object false := by decide
example : q C ≤ .Object true := by decide
example : ¬ q C ≤ .Object false := by decide
example : (.Object true : T) ≤ .dynamic := by decide
example : (.dynamic : T) ≤ .void := by decide
example : ¬ (.dynamic : T) ≤ .Object false := by decide
example : ¬ (.void : T) ≤ q A := by decide
example : (.List int false : T) ≤ .List (q num) true := by decide
example : ¬ (.List num false : T) ≤ .List int false := by decide
example : (.List int false : T) ≤ .Object false := by decide
example : ¬ (.List int false : T) ≤ A := by decide
example : (.Map string C false : T) ≤ .Map string A false := by decide
example : ¬ (.Map string A false : T) ≤ .Map string C false := by decide

/-! ## Printing -/

#guard toString (q C) = "C?"
#guard toString (.Map string (.List (q int) false) true : T) = "Map<String, List<int?>>?"
#guard toString (.Object true : T) = "Object?"

/-! ## Running programs -/

local notation "Variable" => Variable (τ := T)
local notation "LoweredExpr" => LoweredExpr (τ := T)
local notation "Value" => Value (τ := T)
local notation "State" => State (τ := T)

/-- A variable of type `Object?`. -/
def x : Variable := { name := "x", type := .Object true }

/--
The semantics with promotion checks, for a program with no functions, classes, members or
constructors. (The programs below start from a state in which the object they use exists, and
don't access its members.)
-/
@[instance_reducible]
def verify : SemanticParams T :=
  ⟨.verify, fun _ => none, fun _ => none, fun _ => none, fun _ => none, fun _ => .wrap64⟩

/-- A state in which `x` (at location 1) refers to an object (at location 0) of class `B`. -/
def σx : State := ⟨#[.object "B" B [], .val (.obj ⟨0⟩)]⟩

/-- A summary of the result of a run, without the final state or the redex of a stuck run. -/
def summary : Interp.RunResult (τ := T) → Std.Format
  | .done o _ => "done: " ++ repr o
  | .stuck e _ _ => "stuck at: " ++ repr e
  | .outOfFuel e _ => "out of fuel at: " ++ repr e

/-- Run `m` with promotion checks, with `x` bound to location 1 of `σx`. -/
def runWithX (m : LoweredExpr) : Std.Format :=
  summary (Interp.run (P := verify) 100 (m.bindVariables [(x, ⟨1⟩)]) σx)

-- `x is A`: `x` refers to a `B`, which is a subtype of `A`.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runWithX (.is (.var x (.Object true)) A)

-- `x is C`: a `B` isn't a `C`.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool false) -/
#guard_msgs in
#eval runWithX (.is (.var x (.Object true)) C)

-- `{ x as A; x }`: the cast succeeds, and the read of `x`, promoted to `A`, passes its promotion
-- check.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX (.block [.as (.var x (.Object true)) A, .var x A])

-- `x as String` throws.
/-- info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError)) -/
#guard_msgs in
#eval runWithX (.as (.var x (.Object true)) string)

end DartLang.Tests.KernelTypes
