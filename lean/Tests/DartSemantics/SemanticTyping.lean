module
import DartSemantics
import Tests.DartSemantics.Corollaries
import DartLang.SimpleTypes
-- `SimpleType.NonNull` isn't exposed, so its definition is only visible with `import all`.
import all DartLang.SimpleTypes

/-!
# Tests of semantic typing

`SimpleType` obeys the laws that the typing rules assume (`TypeLaws`), so the safety theorem
and its corollaries apply to it. The corollaries are instantiated at `SimpleType` with promotion
checks verified, and `castThenRead` also with them trusted. Instantiating them checks that their
assumptions can be met by a real type representation, so that they aren't vacuous.
-/

namespace DartSemantics.Tests.SemanticTyping

open DartLang SimpleType Iris.ProgramLogic

local notation "Variable" => Variable (τ := SimpleType)
local notation "Property" => Property (τ := SimpleType)
local notation "Value" => Value (τ := SimpleType)
local notation "State" => State (τ := SimpleType)

/-- `SimpleType` obeys the laws that the typing rules assume. -/
theorem typeLaws : TypeLaws SimpleType where
  not_null_le_bool := by decide
  le_nonNull {S T} hS hST := by
    have hN : (DartTypeRepr.Null : SimpleType) = Null := rfl
    cases S <;> cases T <;> simp_all [LE.le, isSubtype, DartTypeRepr.NonNull, NonNull]

/--
A placeholder implementation of user-code getters (`SemanticParams.getterImpl`), needed only to
build the `SemanticParams` instances below: every such getter returns null. The programs tested
here read only properties backed by instance variables, so the choice doesn't matter.
-/
def getterImpl : Property → Value → State → Option Value
  | _, _, _ => some .null

/-- The semantics with promotion checks. -/
@[instance_reducible]
def verify : SemanticParams SimpleType := ⟨.verify, getterImpl⟩

/-- The semantics without promotion checks. -/
@[instance_reducible]
def trust : SemanticParams SimpleType := ⟨.trust, getterImpl⟩

def x : Variable := { name := "x", type := ObjectQ }

/-- A promotable property whose static type is `Object?`. -/
def f : Property := ⟨"_f", ObjectQ, true⟩

section Verify

attribute [local instance] verify

/--
With promotion checks, `{ x as int; x }` is safe whenever `x` holds a value that satisfies
`Object?`: the second read of `x`, promoted to `int`, passes its promotion check.
-/
example (σ : State) (bindings : List (Variable × Loc)) (hb : BindingsOk σ bindings)
    (h : FactHolds σ bindings (.var x ObjectQ)) :
    adequate .NotStuck ((castThenRead x ObjectQ int).bindVariables bindings) σ
      (fun o _ => OutcomeOk Null o) :=
  castThenRead_safe (GF := DartS SimpleType) le_rfl σ bindings hb h

/--
With promotion checks, `{ x._f!; x._f }` is safe whenever `x` refers to an object whose instance
variable `_f` holds a value that satisfies `Object?`: the second read of `x._f`, promoted to
`Object`, passes its promotion check.
-/
example (σ : State) (bindings : List (Variable × Loc)) (hb : BindingsOk σ bindings)
    (hx : FactHolds σ bindings (.var x Object))
    (hf : FactHolds σ bindings (.field x "_f" ObjectQ)) :
    adequate .NotStuck ((nullCheckThenRead x ObjectQ f ObjectQ).bindVariables bindings) σ
      (fun o _ => OutcomeOk Null o) :=
  nullCheckThenRead_safe (GF := DartS SimpleType) (U := Object) typeLaws (by decide) σ bindings
    hb hx hf

def y : Variable := { name := "y", type := ObjectQ }

/--
With promotion checks, `{ x as int; x = y; x }` is safe whenever `x` and `y` hold values that
satisfy `Object?`: the last read of `x` is demoted to `Object?` by the assignment, and passes its
promotion check.
-/
example (σ : State) (bindings : List (Variable × Loc)) (hb : BindingsOk σ bindings)
    (hx : FactHolds σ bindings (.var x ObjectQ)) (hy : FactHolds σ bindings (.var y ObjectQ)) :
    adequate .NotStuck ((castAssignRead x ObjectQ int y ObjectQ).bindVariables bindings) σ
      (fun o _ => OutcomeOk Null o) :=
  castAssignRead_safe (GF := DartS SimpleType) rfl le_rfl le_rfl σ bindings hb hx hy

/-- A `final` local variable, with type `Object?`. -/
def z : Variable := { name := "z", type := ObjectQ, isFinal := true }

/--
With promotion checks, `{ final Object? z; z = y; z }` is safe whenever `y` holds a value that
satisfies `Object?`: `z` starts out unassigned, so assigning it once doesn't get stuck.
-/
example (σ : State) (bindings : List (Variable × Loc)) (hb : BindingsOk σ bindings)
    (hy : FactHolds σ bindings (.var y ObjectQ)) :
    adequate .NotStuck ((finalInitRead z ObjectQ y ObjectQ).bindVariables bindings) σ
      (fun o _ => OutcomeOk Null o) :=
  finalInitRead_safe (GF := DartS SimpleType) (by simp [y, z]) le_rfl σ bindings hb hy

end Verify

section Trust

attribute [local instance] trust

/-- Without promotion checks, `{ x as int; x }` is safe too. -/
example (σ : State) (bindings : List (Variable × Loc)) (hb : BindingsOk σ bindings)
    (h : FactHolds σ bindings (.var x ObjectQ)) :
    adequate .NotStuck ((castThenRead x ObjectQ int).bindVariables bindings) σ
      (fun o _ => OutcomeOk Null o) :=
  castThenRead_safe (GF := DartS SimpleType) le_rfl σ bindings hb h

end Trust

end DartSemantics.Tests.SemanticTyping
