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

end DartLang
