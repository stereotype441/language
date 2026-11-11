module
import DartSemantics
import DartLang.SimpleTypes

/-!
# Tests of printing constructors in leading-dot form

`DartLang.PrettyPrint` makes Lean display the constructors of the semantics' types in leading-dot
form (`.val (.int 0)` rather than `LoweredExpr.val (Value.int 0)`), unless the option
`dart.pp.dotCtors` is off. These tests pin down the printed form of some terms, with the option on
and off, and of a goal in proof mode.

Each test is a `#guard_msgs in` command: it checks that the messages that the command after it
produces (here, the output of `#check` or `trace_state`) are exactly the ones in its doc comment.
`(whitespace := lax)` makes the comparison treat any run of whitespace as a single space, so that
long expected messages can be broken over several lines.

The local notations below make `LoweredExpr`, `Value` and `Cell` tokens, as in the other files, so
Lean quotes them with `«…»` wherever it prints them as names.
-/

namespace DartSemantics.Tests.PrettyPrint

open DartLang SimpleType Iris Iris.BI Iris.ProgramLogic

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Value" => Value (τ := SimpleType)
local notation "Cell" => Cell (τ := SimpleType)

/-!
A nested `LoweredExpr`, with a list of statements and a constructor without arguments
(`Value.null`). The outermost `LoweredExpr.seq` is displayed with Lean's field notation
(`m₁.seq m₂`), as before; its arguments are in leading-dot form.
-/

/-- info: (.val (.int 0)).seq (.block [.labeled "L" (.val .null), .brk "L"]) : «LoweredExpr» -/
#guard_msgs in
#check (LoweredExpr.seq (.val (.int 0)) (.block [.labeled "L" (.val .null), .brk "L"]) :
  LoweredExpr)

/-! The same term, with the option off: constructors are displayed with their full names. -/

/--
info: («LoweredExpr».val («Value».int 0)).seq
  («LoweredExpr».block
    [«LoweredExpr».labeled "L" («LoweredExpr».val «Value».null), «LoweredExpr».brk "L"]) :
  «LoweredExpr»
-/
#guard_msgs (whitespace := lax) in
set_option dart.pp.dotCtors false in
#check (LoweredExpr.seq (.val (.int 0)) (.block [.labeled "L" (.val .null), .brk "L"]) :
  LoweredExpr)

/-! `Cell`'s constructors, which `DartSemantics.State` registers. -/

/--
info: fun ℓ => (.object "C" int [("C::f", ℓ)], .val (.int 0), .uninit) :
  (ℓ : Loc) → «Cell» × «Cell» × «Cell»
-/
#guard_msgs (whitespace := lax) in
#check fun ℓ : Loc => (Cell.object "C" int [("C::f", ℓ)], Cell.val (.int 0), (Cell.uninit : Cell))

/-!
A partial application of a constructor keeps its full name, and a full one is in leading-dot form
(here with field notation off, so that the full application isn't displayed as
`m.seq (.val .null)`).
-/

/--
info: fun m => («LoweredExpr».seq m, .seq m (.val .null)) :
  «LoweredExpr» → («LoweredExpr» → «LoweredExpr») × «LoweredExpr»
-/
#guard_msgs (whitespace := lax) in
set_option pp.fieldNotation false in
#check fun m : LoweredExpr => (LoweredExpr.seq m, LoweredExpr.seq m (.val .null))

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS SimpleType hlc GF]
variable [P : SemanticParams SimpleType]

include hlc

/-!
A goal in proof mode, as the InfoView shows it (`trace_state` prints the goal as a message): the
points-to's cell, the expression and the postcondition are in leading-dot form.
-/

/--
trace: hlc : HasLC
GF : BundledGFunctors
inst✝ : DartGS SimpleType hlc GF
P : SemanticParams SimpleType
ℓ : Loc
⊢
  ∗H : ℓ ↦ .val (.int 0)
  ⊢ WP ((.val .null).seq (.val (.int 1))) {{ o, ⌜o = .normal (.int 1)⌝ }}
-/
#guard_msgs (whitespace := lax) in
example (ℓ : Loc) : ℓ ↦ (.val (.int 0) : Cell) ⊢@{IProp GF}
    WP (LoweredExpr.seq (τ := SimpleType) (.val .null) (.val (.int 1))) {{ o,
      ⌜o = DartLang.Outcome.normal (τ := SimpleType) (.int 1)⌝ }} := by
  iintro H
  trace_state
  wp_pures
  ipureintro
  trivial

end DartSemantics.Tests.PrettyPrint
