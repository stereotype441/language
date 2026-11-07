module
import DartLang.SimpleTypes

/-!
# Tests of the run-time view of `SimpleType`
-/

namespace DartLang

example : RtSubChecker.check 0 SimpleType.Null SimpleType.ObjectQ = some (true, 0) := by
  decide

example : RtSubChecker.check 0 SimpleType.Null SimpleType.Object = some (false, 0) := by
  decide

example : RtSub SimpleType.Null SimpleType.ObjectQ true :=
  RtSubChecker.check_sound
    (by decide : RtSubChecker.check 0 SimpleType.Null SimpleType.ObjectQ = some (true, 0))

example : RtSub SimpleType.Null SimpleType.Object false :=
  RtSubChecker.check_sound
    (by decide : RtSubChecker.check 0 SimpleType.Null SimpleType.Object = some (false, 0))

/-! `void` is a top type: every type is a subtype of it, and it's a subtype of exactly the top
types. -/

example : SimpleType.int.isSubtype .void = true := by decide
example : SimpleType.Null.isSubtype .void = true := by decide
example : (SimpleType.List .int).isSubtype .void = true := by decide
example : SimpleType.void.isSubtype .void = true := by decide
example : SimpleType.void.isSubtype .ObjectQ = true := by decide
example : SimpleType.void.isSubtype .dynamic = true := by decide
example : SimpleType.ObjectQ.isSubtype .void = true := by decide
example : SimpleType.dynamic.isSubtype .void = true := by decide
example : SimpleType.void.isSubtype .Object = false := by decide
example : SimpleType.void.isSubtype .Null = false := by decide
example : SimpleType.void.isSubtype .int = false := by decide
example : SimpleType.NonNull .void = .void := rfl

/-- At run time, `void` gives the same answers as `Object?`. -/
example : RtSubChecker.check 0 SimpleType.Null SimpleType.void = some (true, 0) := by
  decide

/-! Class types: with `class A {}`, `class B extends A {}` and `class C {}`, `B` is a subtype of
`A` (and of `Object` and the top types), but not the other way around, and `C` is unrelated to
both. `Never` is a subtype of every class type, and `Null` of none (class types are
non-nullable). -/

/-- The class type `A`, a direct subclass of `Object`. -/
abbrev tA : SimpleType := .Class "A" []
/-- The class type `B`, a subclass of `A`. -/
abbrev tB : SimpleType := .Class "B" ["A"]
/-- The class type `C`, a direct subclass of `Object`. -/
abbrev tC : SimpleType := .Class "C" []

example : tA.isSubtype tA = true := by decide
example : tB.isSubtype tA = true := by decide
example : tA.isSubtype tB = false := by decide
example : tC.isSubtype tA = false := by decide
example : tB.isSubtype tC = false := by decide
example : tB.isSubtype .Object = true := by decide
example : tB.isSubtype .ObjectQ = true := by decide
example : tB.isSubtype .void = true := by decide
example : tB.isSubtype .Null = false := by decide
example : SimpleType.Object.isSubtype tA = false := by decide
example : SimpleType.Null.isSubtype tA = false := by decide
example : SimpleType.Never.isSubtype tA = true := by decide
example : SimpleType.int.isSubtype tA = false := by decide

/-- A subclass of `B` is a subtype of `A`, through `B`'s supertypes. -/
example : (SimpleType.Class "D" ["B", "A"]).isSubtype tA = true := by decide

/-- A class type isn't a subtype of a class type with the same key but different supertypes. -/
example : (SimpleType.Class "B" []).isSubtype tB = false := by decide

end DartLang
