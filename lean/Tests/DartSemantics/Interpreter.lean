module
import DartSemantics
import DartLang.SimpleTypes
meta import DartSemantics
meta import DartLang.SimpleTypes

/-!
# Tests of the interpreter

Runs programs on `SimpleType`. The programs include `LoweredExpr`s of the kind flow analysis
produces (some run with their local variable `x` replaced by a parameter, so that it can hold
something other than the null object), literals, calls of top-level functions (see `functions`),
objects and their construction (see `classes`), loops and breaks, integer arithmetic in each integer
mode, programs for each way a program can fail (throwing, and getting stuck), the redex at which a
stuck program is reported to be stuck, and programs that run out of fuel.

A block's value is the null object, so a program that is a block completes normally with the null
object, unless it throws or gets stuck.
-/

namespace DartSemantics.Tests.Interpreter

open DartLang SimpleType

local notation "LoweredExpr" => LoweredExpr (τ := SimpleType)
local notation "Variable" => Variable (τ := SimpleType)
local notation "Property" => Property (τ := SimpleType)
local notation "Value" => Value (τ := SimpleType)
local notation "State" => State (τ := SimpleType)

def x : Variable := { name := "x", type := ObjectQ }
def y : Variable := { name := "y", type := Object }
def b : Variable := { name := "b", type := bool }
def c : Variable := { name := "c", type := bool }
def n : Variable := { name := "n", type := int }
def i : Variable := { name := "i", type := int }
def s : Variable := { name := "s", type := int }

/--
`int f(int n) { var s = 0; for (var i = 0; i < n; i = i + 1) { body } return s; }`, for the
loop tests in `functions`.
-/
def sumLoop (body : List LoweredExpr) : FunctionDecl (τ := SimpleType) :=
  ⟨[n], .block [.declare s int false, .variableSet s (.int 0), .declare i int false,
    .variableSet i (.int 0),
    .labeled "L" (.loop (.cond (.intBin .lt none (.var i int) (.var n int))
      (.seq (.labeled "C" (.block body)) (.variableSet i (.intBin .add none (.var i int) (.int 1))))
      (.brk "L") Null)),
    .ret (.var s int)]⟩

/-- `s = s + i;`, for `sumLoop`. -/
def addI : LoweredExpr := .variableSet s (.intBin .add none (.var s int) (.var i int))

/-- `{ bool b = true; bool c = false; body; return c; }`, for the loop tests in `functions`. -/
def withBC (body : LoweredExpr) : LoweredExpr :=
  .block [.declare b bool false, .variableSet b (.bool true), .declare c bool false,
    .variableSet c (.bool false), body, .ret (.var c bool)]

/--
The top-level functions of the programs tested here:
- `bool not(bool b) { if (b) return false; return true; }`;
- `bool alwaysTrue(bool b) { if (b) return alwaysTrue(false); return true; }`, which is recursive;
- `Null noReturn(int n) { n; }`, which falls off the end of its body;
- `int nested() { { return 2; 3; } }`, which returns from inside a nested block;
- `Null fail() { null!; }`, which throws;
- `int first(int n, bool b) { return n; }`, which has two parameters;
- `bool whileOnce()`, `bool doOnce()` and `bool skip()`, which loop (see their definitions);
- `int nestedBreak() { outer: { inner: { break outer; } return 1; } return 2; }`;
- `bool innerBreak() { while (true) { while (true) { break; } break; } return true; }`;
- `int returnFromLoop() { while (true) { return 3; } }`;
- `Null breakOut() { break L; }`, whose break has no labeled statement to break out of (which Dart
  rejects);
- `int wrapAdd(int n) { return n + 1; }`, and `checkedAdd` and `unboundedAdd`, the same in other
  integer modes (see `intModeOf`); and
- `int sumBelow(int n)`, which sums the integers from `0` to `n - 1` with a `for` loop, and
  `int sumSkipping(int n)`, which does the same, but skips `0` and `1` with a `continue` (see
  `sumLoop`).
-/
def functions : String → Option (FunctionDecl (τ := SimpleType))
  | "not" => some ⟨[b],
      .block [.cond (.var b bool) (.ret (.bool false)) .null Null, .ret (.bool true)]⟩
  | "alwaysTrue" => some ⟨[b],
      .block [.cond (.var b bool) (.ret (.call "alwaysTrue" [.bool false] bool)) .null Null,
        .ret (.bool true)]⟩
  | "noReturn" => some ⟨[n], .block [.var n int]⟩
  | "nested" => some ⟨[], .block [.block [.ret (.int 2), .int 3]]⟩
  | "fail" => some ⟨[], .block [.nullCheck .null]⟩
  | "first" => some ⟨[n, b], .ret (.var n int)⟩
  -- `while (b) { b = false; c = true; }`: the body runs once.
  | "whileOnce" => some ⟨[], withBC (.labeled "L" (.loop (.cond (.var b bool)
      (.labeled "C" (.block [.variableSet b (.bool false), .variableSet c (.bool true)]))
      (.brk "L") Null)))⟩
  -- `b = false; do { c = true; } while (b);`: the body runs once, although `b` is `false`.
  | "doOnce" => some ⟨[], withBC (.block [.variableSet b (.bool false),
      .labeled "L" (.loop (.seq (.labeled "C" (.block [.variableSet c (.bool true)]))
        (.cond (.var b bool) .null (.brk "L") Null)))])⟩
  -- `while (b) { b = false; continue; c = true; }`: `continue` skips the rest of the body.
  | "skip" => some ⟨[], withBC (.labeled "L" (.loop (.cond (.var b bool)
      (.labeled "C" (.block [.variableSet b (.bool false), .brk "C", .variableSet c (.bool true)]))
      (.brk "L") Null)))⟩
  | "nestedBreak" => some ⟨[], .block [
      .labeled "outer" (.block [.labeled "inner" (.block [.brk "outer"]), .ret (.int 1)]),
      .ret (.int 2)]⟩
  | "innerBreak" => some ⟨[], .block [
      .labeled "L1" (.loop (.cond (.bool true)
        (.labeled "C1" (.block [
          .labeled "L2" (.loop (.cond (.bool true) (.labeled "C2" (.block [.brk "L2"])) (.brk "L2")
            Null)),
          .brk "L1"]))
        (.brk "L1") Null)),
      .ret (.bool true)]⟩
  | "returnFromLoop" => some ⟨[], .block [
      .labeled "L" (.loop (.cond (.bool true) (.labeled "C" (.block [.ret (.int 3)])) (.brk "L")
        Null))]⟩
  | "breakOut" => some ⟨[], .block [.brk "L"]⟩
  | "wrapAdd" | "checkedAdd" | "unboundedAdd" =>
    some ⟨[n], .ret (.intBin .add none (.var n int) (.int 1))⟩
  | "sumBelow" => some (sumLoop [addI])
  | "sumSkipping" =>
    some (sumLoop [.cond (.intBin .lt none (.var i int) (.int 2)) (.brk "C") .null Null, addI])
  | _ => none

/-- The integer mode of each function in `functions`: `checked`, except as their names say. -/
def intModeOf : String → IntMode
  | "wrapAdd" => .wrap64
  | "unboundedAdd" => .unbounded
  | _ => .checked

/-! ### Classes -/

/-- The class type of class `Log`. -/
abbrev tLog : SimpleType := .Class "Log" []
/-- The class type of class `S`. -/
abbrev tS : SimpleType := .Class "S" []
/-- The class type of class `C`, a subclass of `S`. -/
abbrev tC : SimpleType := .Class "C" ["S"]
/-- The class type of class `R`. -/
abbrev tR : SimpleType := .Class "R" []
/-- The class type of class `D`. -/
abbrev tD : SimpleType := .Class "D" []
/-- The class type of class `U`. -/
abbrev tU : SimpleType := .Class "U" []
/-- The class type of class `A`. -/
abbrev tA : SimpleType := .Class "A" []
/-- The class type of class `B`, a subclass of `A`. -/
abbrev tB : SimpleType := .Class "B" ["A"]
/-- The class type of class `C2`, a subclass of `B`. -/
abbrev tC2 : SimpleType := .Class "C2" ["B", "A"]
/-- The class type of class `P1`, a subclass of `A`. -/
abbrev tP1 : SimpleType := .Class "P1" ["A"]
/-- The class type of class `P2`, a subclass of `B`. -/
abbrev tP2 : SimpleType := .Class "P2" ["B", "A"]
/-- The class type of class `G`. -/
abbrev tG : SimpleType := .Class "G" []
/-- The class type of class `H`, a subclass of `G`. -/
abbrev tH : SimpleType := .Class "H" ["G"]
/-- The class type of class `G2`. -/
abbrev tG2 : SimpleType := .Class "G2" []
/-- The class type of class `H2`, a subclass of `G2`. -/
abbrev tH2 : SimpleType := .Class "H2" ["G2"]
/-- The class type of class `E`. -/
abbrev tE : SimpleType := .Class "E" []
/-- The class type of class `Obj`. -/
abbrev tObj : SimpleType := .Class "Obj" []
/-- The class type of class `V`. -/
abbrev tV : SimpleType := .Class "V" []
/-- The class type of class `W`, a subclass of `V`. -/
abbrev tW : SimpleType := .Class "W" ["V"]

/-- `this`, in the members of the class whose class type is `T`. -/
def thisOf (T : SimpleType) : Variable := { name := "this", type := T }
/-- A parameter `l` of type `Log`. -/
def l : Variable := { name := "l", type := tLog }
/-- A parameter `v` of type `int`. -/
def pv : Variable := { name := "v", type := int }
/-- A parameter `other` of type `Object?`. -/
def other : Variable := { name := "other", type := ObjectQ }

/-- The property `n` of class `Log`. -/
def pn : Property := ⟨"n", int, false⟩
/-- The property `x` of classes `D`, `U`, `G` and `H`. -/
def px : Property := ⟨"x", int, false⟩
/-- The property `y` of classes `G2` and `H2`. -/
def py : Property := ⟨"y", int, false⟩
/-- The instance variable `_y` of classes `G2` and `H2`. -/
def p_y : Property := ⟨"_y", int, false⟩

/--
`l.n = l.n * 10 + k`: appends digit `k` to the log `l`, so that the order in which these run can
be read from `l.n`.
-/
def logStep (k : Int) : LoweredExpr :=
  .propertySet (.var l tLog) "n"
    (.intBin .add none (.intBin .mul none (.propertyGet (.var l tLog) pn int) (.int 10)) (.int k))

/--
The dispatch table of a class whose only members are the implicit getters and setters of the
instance variables `names` (each keyed by its own name).
-/
def fieldDispatch (names : List String) (name : String) : Option Member :=
  if name ∈ names then some (.field name)
  else (names.find? (· ++ "=" == name)).map .field

/--
The classes of the programs tested here:
- `class Log { int n; Log() : n = 0; }`, a log of digits (see `logStep`);
- `class S { int a; S(Log l) : a = logStep(2) { logStep(3); } }`;
- `class C extends S { int c; C(Log l) : c = logStep(1), super(l) { logStep(4); } }`, so that
  `C(l)` appends `1234` to `l`, in Dart's order of construction;
- `class R { R(Log l) { logStep(1); return; logStep(2); } }`, whose constructor returns early;
- `class D { int x = 1; D() : x = 2; }`, whose instance variable is initialized twice; and
- `class U { int x; U() { x; } }`, whose constructor reads `x` before it's initialized (which Dart
  rejects); and
- `X`, the class of the object in `σx`, which has an instance variable `_f` and a getter
  `Object? get h => null;`. To test run-time type checks on objects, its instances' dynamic type is
  `int` (which no real class can have).

and, for instance members (see `members`):
- `class A { int f() => 1; int callF() => f(); }`;
- `class B extends A { int f() => super.f() + 10; int bf() => super.f(); }`;
- `class C2 extends B { int f() => 100; }`;
- `class P1 extends A with M {}` and `class P2 extends B with M {}`, where
  `mixin M on A { int m() => super.f(); }`: one member body, provided by two classes with different
  superclasses, so that its `super` call reaches a different member in each;
- `class G { int x; G() : x = 5; }`;
- `class H extends G { int get x => 7; int superX() => super.x;
  void setSuperX(int v) { super.x = v; } }`, whose getter overrides an instance variable;
- `class G2 { int _y; G2() : _y = 0; int get y => _y + 100; set y(int v) { _y = v; } }`;
- `class H2 extends G2 { int get y => 0; int superY() => super.y;
  void setSuperY(int v) { super.y = v; } }`;
- `class E { bool operator ==(Object? other) => true; }`;
- `class Obj { bool operator ==(Object? other) => identical(this, other); }`, like `Object`; and
- `class V { int x = 1; int readX() => x; }` and `class W extends V { int x = 2;
  int get sup => super.x; void setSup(int v) { super.x = v; } }`, whose instance variable `x`
  shadows `V`'s: a `W` has two instance variables named `x`, with keys `"V::x"` and `"W::x"`.
-/
def classes : String → Option (ClassDecl (τ := SimpleType))
  | "Log" => some ⟨tLog, ["n"], fieldDispatch ["n"], none⟩
  | "S" => some ⟨tS, ["a"], fieldDispatch ["a"], none⟩
  | "C" => some ⟨tC, ["a", "c"], fieldDispatch ["a", "c"], some "S"⟩
  | "R" => some ⟨tR, [], fieldDispatch [], none⟩
  | "D" => some ⟨tD, ["x"], fieldDispatch ["x"], none⟩
  | "U" => some ⟨tU, ["x"], fieldDispatch ["x"], none⟩
  | "X" => some ⟨int, ["_f"],
      fun name => if name = "h" then some (.proc "X.h" "X") else fieldDispatch ["_f"] name, none⟩
  | "A" => some ⟨tA, [], fun
      | "f" => some (.proc "A.f" "A") | "callF" => some (.proc "A.callF" "A") | _ => none, none⟩
  | "B" => some ⟨tB, [], fun
      | "f" => some (.proc "B.f" "B") | "callF" => some (.proc "A.callF" "A")
      | "bf" => some (.proc "B.bf" "B") | _ => none, some "A"⟩
  | "C2" => some ⟨tC2, [], fun
      | "f" => some (.proc "C2.f" "C2") | "callF" => some (.proc "A.callF" "A")
      | "bf" => some (.proc "B.bf" "B") | _ => none, some "B"⟩
  | "P1" => some ⟨tP1, [], fun
      | "f" => some (.proc "A.f" "A") | "callF" => some (.proc "A.callF" "A")
      | "m" => some (.proc "M.m" "P1") | _ => none, some "A"⟩
  | "P2" => some ⟨tP2, [], fun
      | "f" => some (.proc "B.f" "B") | "callF" => some (.proc "A.callF" "A")
      | "bf" => some (.proc "B.bf" "B") | "m" => some (.proc "M.m" "P2") | _ => none, some "B"⟩
  | "G" => some ⟨tG, ["x"], fieldDispatch ["x"], none⟩
  | "H" => some ⟨tH, ["x"], fun
      | "x" => some (.proc "H.x" "H") | "x=" => some (.field "x")
      | "superX" => some (.proc "H.superX" "H") | "setSuperX" => some (.proc "H.setSuperX" "H")
      | _ => none, some "G"⟩
  | "G2" => some ⟨tG2, ["_y"], fun
      | "y" => some (.proc "G2.y" "G2") | "y=" => some (.proc "G2.y=" "G2")
      | name => fieldDispatch ["_y"] name, none⟩
  | "H2" => some ⟨tH2, ["_y"], fun
      | "y" => some (.proc "H2.y" "H2") | "y=" => some (.proc "G2.y=" "G2")
      | "superY" => some (.proc "H2.superY" "H2")
      | "setSuperY" => some (.proc "H2.setSuperY" "H2")
      | name => fieldDispatch ["_y"] name, some "G2"⟩
  | "E" => some ⟨tE, [], fun | "==" => some (.proc "E.==" "E") | _ => none, none⟩
  | "Obj" => some ⟨tObj, [], fun | "==" => some (.proc "Obj.==" "Obj") | _ => none, none⟩
  | "V" => some ⟨tV, ["V::x"], fun
      | "x" | "x=" => some (.field "V::x") | "readX" => some (.proc "V.readX" "V") | _ => none,
      none⟩
  | "W" => some ⟨tW, ["V::x", "W::x"], fun
      | "x" | "x=" => some (.field "W::x") | "readX" => some (.proc "V.readX" "V")
      | "sup" => some (.proc "W.sup" "W") | "setSup" => some (.proc "W.setSup" "W") | _ => none,
      some "V"⟩
  | _ => none

/-- The methods, getters and setters of the classes in `classes`. -/
def members : String → Option (MemberDecl (τ := SimpleType))
  | "X.h" => some ⟨thisOf int, [], .ret .null⟩
  | "A.f" => some ⟨thisOf tA, [], .ret (.int 1)⟩
  | "A.callF" => some ⟨thisOf tA, [], .ret (.methodCall (.var (thisOf tA) tA) "f" [] int)⟩
  | "B.f" => some ⟨thisOf tB, [],
      .ret (.intBin .add none (.superCall (.var (thisOf tB) tB) "f" none [] int) (.int 10))⟩
  | "B.bf" => some ⟨thisOf tB, [], .ret (.superCall (.var (thisOf tB) tB) "f" none [] int)⟩
  | "C2.f" => some ⟨thisOf tC2, [], .ret (.int 100)⟩
  | "M.m" => some ⟨thisOf tA, [], .ret (.superCall (.var (thisOf tA) tA) "f" none [] int)⟩
  | "H.x" => some ⟨thisOf tH, [], .ret (.int 7)⟩
  | "H.superX" => some ⟨thisOf tH, [], .ret (.superGet (.var (thisOf tH) tH) "x" none int)⟩
  | "H.setSuperX" => some ⟨thisOf tH, [pv], .superSet (.var (thisOf tH) tH) "x" none (.var pv int)⟩
  | "G2.y" => some ⟨thisOf tG2, [],
      .ret (.intBin .add none (.propertyGet (.var (thisOf tG2) tG2) p_y int) (.int 100))⟩
  | "G2.y=" => some ⟨thisOf tG2, [pv], .propertySet (.var (thisOf tG2) tG2) "_y" (.var pv int)⟩
  | "H2.y" => some ⟨thisOf tH2, [], .ret (.int 0)⟩
  | "H2.superY" => some ⟨thisOf tH2, [], .ret (.superGet (.var (thisOf tH2) tH2) "y" none int)⟩
  | "H2.setSuperY" => some ⟨thisOf tH2, [pv],
      .superSet (.var (thisOf tH2) tH2) "y" none (.var pv int)⟩
  | "E.==" => some ⟨thisOf tE, [other], .ret (.bool true)⟩
  | "Obj.==" => some ⟨thisOf tObj, [other],
      .ret (.identical (.var (thisOf tObj) tObj) (.var other ObjectQ))⟩
  | "V.readX" => some ⟨thisOf tV, [], .ret (.propertyGet (.var (thisOf tV) tV) px int)⟩
  | "W.sup" => some ⟨thisOf tW, [], .ret (.superGet (.var (thisOf tW) tW) "x" none int)⟩
  | "W.setSup" => some ⟨thisOf tW, [pv], .superSet (.var (thisOf tW) tW) "x" none (.var pv int)⟩
  | _ => none

/-- The constructors of the classes in `classes`, named `<class>.new`. -/
def constructors : String → Option (ConstructorDecl (τ := SimpleType))
  | "Log.new" => some ⟨"Log", thisOf tLog, [], [.initField (.var (thisOf tLog) tLog) "n" (.int 0)],
      .block []⟩
  | "S.new" => some ⟨"S", thisOf tS, [l], [.initField (.var (thisOf tS) tS) "a" (logStep 2)],
      logStep 3⟩
  | "C.new" => some ⟨"C", thisOf tC, [l], [.initField (.var (thisOf tC) tC) "c" (logStep 1),
      .initCtor (.var (thisOf tC) tC) "S.new" [.var l tLog]], logStep 4⟩
  | "R.new" => some ⟨"R", thisOf tR, [l], [], .block [logStep 1, .ret .null, logStep 2]⟩
  | "D.new" => some ⟨"D", thisOf tD, [], [.initField (.var (thisOf tD) tD) "x" (.int 1),
      .initField (.var (thisOf tD) tD) "x" (.int 2)], .block []⟩
  | "U.new" => some ⟨"U", thisOf tU, [], [], .propertyGet (.var (thisOf tU) tU) px int⟩
  | "A.new" => some ⟨"A", thisOf tA, [], [], .block []⟩
  | "B.new" => some ⟨"B", thisOf tB, [], [], .block []⟩
  | "C2.new" => some ⟨"C2", thisOf tC2, [], [], .block []⟩
  | "P1.new" => some ⟨"P1", thisOf tP1, [], [], .block []⟩
  | "P2.new" => some ⟨"P2", thisOf tP2, [], [], .block []⟩
  | "G.new" => some ⟨"G", thisOf tG, [], [.initField (.var (thisOf tG) tG) "x" (.int 5)], .block []⟩
  | "H.new" => some ⟨"H", thisOf tH, [], [.initCtor (.var (thisOf tH) tH) "G.new" []], .block []⟩
  | "G2.new" => some ⟨"G2", thisOf tG2, [], [.initField (.var (thisOf tG2) tG2) "_y" (.int 0)],
      .block []⟩
  | "H2.new" => some ⟨"H2", thisOf tH2, [], [.initCtor (.var (thisOf tH2) tH2) "G2.new" []],
      .block []⟩
  | "E.new" => some ⟨"E", thisOf tE, [], [], .block []⟩
  | "Obj.new" => some ⟨"Obj", thisOf tObj, [], [], .block []⟩
  | "V.new" => some ⟨"V", thisOf tV, [], [.initField (.var (thisOf tV) tV) "V::x" (.int 1)],
      .block []⟩
  | "W.new" => some ⟨"W", thisOf tW, [], [.initField (.var (thisOf tW) tW) "W::x" (.int 2),
      .initCtor (.var (thisOf tW) tW) "V.new" []], .block []⟩
  | _ => none

/-- The semantics with promotion checks. -/
@[instance_reducible]
def verify : SemanticParams SimpleType :=
  ⟨.verify, functions, classes, members, constructors, intModeOf⟩

/-- The semantics without promotion checks. -/
@[instance_reducible]
def trust : SemanticParams SimpleType :=
  ⟨.trust, functions, classes, members, constructors, intModeOf⟩

/-- A promotable property, backed by an instance variable of the object in `σx`. -/
def f : Property := ⟨"_f", ObjectQ, true⟩

/--
A property with the same name as `f` that flow analysis doesn't consider promotable. Whether a
property is promotable doesn't affect the semantics, so reading it reads the same instance
variable.
-/
def f' : Property := ⟨"_f", ObjectQ, false⟩

/-- A property of the object in `σx` whose getter is user code. -/
def h : Property := ⟨"h", ObjectQ, false⟩

/--
A state for running a program with parameter `x`: `x` (at location 2) refers to an object (at
location 0) of class `X`, whose instance variable `_f` (at location 1) holds `true`.
-/
def σx : State :=
  ⟨#[.object "X" int [("_f", ⟨1⟩)], .val (.bool true), .val (.obj ⟨0⟩)]⟩

/-- A summary of the result of a run, without the final state or the redex of a stuck run. -/
def summary : Interp.RunResult (τ := SimpleType) → Std.Format
  | .done o _ => "done: " ++ repr o
  | .stuck e _ _ => "stuck at: " ++ repr e
  | .outOfFuel e _ => "out of fuel at: " ++ repr e

/-- The redex at which a run got stuck, if it did. -/
def stuckRedex : Interp.RunResult (τ := SimpleType) → Std.Format
  | .stuck _ redex _ => "stuck at redex: " ++ repr redex
  | _ => "not stuck"

/-- Run `m`, with parameter `x` bound to location 2 of `σx`. -/
def runWithX (P : SemanticParams SimpleType) (m : LoweredExpr) : Std.Format :=
  summary (Interp.run (P := P) 100 (m.bindVariables [(x, ⟨2⟩)]) σx)

/-- Run `m` from the empty state. -/
def runClosed (P : SemanticParams SimpleType) (m : LoweredExpr) : Std.Format :=
  summary (Interp.run (P := P) 100 m State.empty)

/-! ## Programs that flow analysis produces -/

-- `{ Object? x; x!; x }`: `x` is the null object, so `x!` throws.
/-- info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError)) -/
#guard_msgs in
#eval runClosed verify
  (.block [.declare x ObjectQ true, .nullCheck (.var x ObjectQ), .var x Object])

-- `{ x!; x }`, where parameter `x` refers to an `int` (see `runWithX`), so `x!` succeeds, and the
-- promotion of `x` to `Object` is sound.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify (.block [.nullCheck (.var x ObjectQ), .var x Object])

-- `{ Object? x; x as Object; x }`: `x` is the null object, so the cast throws.
/-- info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError)) -/
#guard_msgs in
#eval runClosed verify
  (.block [.declare x ObjectQ true, .as (.var x ObjectQ) Object, .var x Object])

-- `{ x as Object; x }`, where parameter `x` refers to an `int` (see `runWithX`), so the cast
-- succeeds.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify (.block [.as (.var x ObjectQ) Object, .var x Object])

-- `{ null }`
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runClosed verify (.block [.null])

-- `{ x! as int; x }`, where parameter `x` refers to an `int` (see `runWithX`), so the null check
-- and the cast succeed.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify (.block [.as (.nullCheck (.var x ObjectQ)) int, .var x Object])

-- `{ (x as Object) as int; x }`, where parameter `x` refers to an `int` (see `runWithX`), so both
-- casts succeed.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify (.block [.as (.as (.var x ObjectQ) Object) int, .var x Object])

-- `{ x._f!; x._f }`, where parameter `x` refers to an object whose `_f` holds `true` (see
-- `runWithX`), so `x._f!` succeeds, and the promotion of the second `x._f` to `Object` is sound.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify
  (.block [.nullCheck (.propertyGet (.var x ObjectQ) f ObjectQ),
    .propertyGet (.var x ObjectQ) f Object])

/-! ## Other programs that complete normally -/

-- `x._f`, promoted to `Object`, where parameter `x` refers to an object whose `_f` holds `true`
-- (see `runWithX`), so the promotion is sound.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runWithX verify (.propertyGet (.var x ObjectQ) f Object)

-- `x.h`, where the class of the object that parameter `x` refers to dispatches `h` to a getter
-- (see `runWithX`), so the read runs the getter, which is user code (and returns the null object).
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify (.propertyGet (.var x ObjectQ) h ObjectQ)

-- `x._f`, where flow analysis doesn't consider `_f` promotable, still reads the instance variable
-- `_f` of the object that parameter `x` refers to, which holds `true` (see `runWithX`).
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runWithX verify (.propertyGet (.var x ObjectQ) f' ObjectQ)

-- `x is int ? x : null`, where the first branch's `x` is promoted to `int`. Parameter `x` refers
-- to an `int` (see `runWithX`), so the first branch runs, and the promotion is sound.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.obj { n := 0 }) -/
#guard_msgs in
#eval runWithX verify (.cond (.is (.var x ObjectQ) int) (.var x int) .null ObjectQ)

-- `x is bool ? x : null`, where the first branch's `x` is promoted to `bool`. Parameter `x`
-- refers to an `int` (see `runWithX`), so the second branch runs.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify (.cond (.is (.var x ObjectQ) bool) (.var x bool) .null ObjectQ)

-- `{ Object? x; } x!`: a declaration in a nested block doesn't shadow `x` after the block. So
-- `x!` reads parameter `x`, which refers to an `int` (see `runWithX`), not the null object.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.obj { n := 0 }) -/
#guard_msgs in
#eval runWithX verify (.seq (.block [.declare x ObjectQ true]) (.nullCheck (.var x ObjectQ)))

/-! ## Literals -/

-- `true`
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runClosed verify (.bool true)

-- `-3`
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int (-3)) -/
#guard_msgs in
#eval runClosed verify (.int (-3))

-- `false ? 1 : 2`
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 2) -/
#guard_msgs in
#eval runClosed verify (.cond (.bool false) (.int 1) (.int 2) int)

-- `(7 as Object) as int`: an integer's dynamic type is `int`, so both casts succeed.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 7) -/
#guard_msgs in
#eval runClosed verify (.as (.as (.int 7) Object) int)

-- `7 as bool` fails.
/--
info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError))
-/
#guard_msgs in
#eval runClosed verify (.as (.int 7) bool)

-- `(7 as void) as int`: every value satisfies `void`, and the cast doesn't change the value.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 7) -/
#guard_msgs in
#eval runClosed verify (.as (.as (.int 7) void) int)

/-! ## Assignments -/

-- `x = null` evaluates to the value assigned.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify (.variableSet x .null)

-- `{ Object y; y = x; y as int }`: assigning to `y` initializes it, so reading it doesn't get
-- stuck. Parameter `x` refers to an `int` (see `runWithX`), so the cast succeeds.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify
  (.block [.declare y Object false, .variableSet y (.var x ObjectQ), .as (.var y Object) int])

-- `x = null; x!`: after the assignment, `x` holds the null object, so `x!` throws, although
-- parameter `x` started out referring to an `int` (see `runWithX`).
/-- info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError)) -/
#guard_msgs in
#eval runWithX verify (.seq (.variableSet x .null) (.nullCheck (.var x ObjectQ)))

-- `x = null!`: the exception propagates out of the assignment.
/-- info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError)) -/
#guard_msgs in
#eval runWithX verify (.variableSet x (.nullCheck .null))

-- `{ x as int; x = null; x }`, where the last read of `x` is (wrongly) still promoted to `int`:
-- flow analysis must demote `x` when it's assigned. With promotion checks, the read gets stuck.
/--
info: stuck at: DartLang.LoweredExpr.seq
  (DartLang.LoweredExpr.varAt
    { name := "x", type := DartLang.SimpleType.ObjectQ, isFinal := false }
    (DartLang.SimpleType.int)
    { n := 2 })
  (DartLang.LoweredExpr.block [])
-/
#guard_msgs (whitespace := lax) in
#eval runWithX verify (.block [.as (.var x ObjectQ) int, .variableSet x .null, .var x int])

-- The same program, without promotion checks, completes.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX trust (.block [.as (.var x ObjectQ) int, .variableSet x .null, .var x int])

-- An assignment to an object's own cell (which flow analysis never produces) gets stuck.
/--
info: stuck at: DartLang.LoweredExpr.variableSetAt
  { name := "x", type := DartLang.SimpleType.ObjectQ, isFinal := false }
  { n := 0 }
  (DartLang.LoweredExpr.val (DartLang.Value.null))
-/
#guard_msgs in
#eval runWithX verify (.variableSetAt x ⟨0⟩ (.val .null))

/-! ## `final` local variables -/

/-- A `final` local variable `z`, with type `Object?`. -/
def z : Variable := { name := "z", type := ObjectQ, isFinal := true }

-- `{ final Object? z; z = x; z as int }`: a `final` variable can be assigned once.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runWithX verify
  (.block [.declare z ObjectQ false, .variableSet z (.var x ObjectQ), .as (.var z ObjectQ) int])

-- `{ final Object? z; z }`: a `final` variable starts out unassigned, even if its type is nullable
-- (flow analysis sets `startsNull` to `false`), so reading it before it's assigned gets stuck.
/--
info: stuck at: DartLang.LoweredExpr.seq
  (DartLang.LoweredExpr.varAt
    { name := "z", type := DartLang.SimpleType.ObjectQ, isFinal := true }
    (DartLang.SimpleType.ObjectQ)
    { n := 3 })
  (DartLang.LoweredExpr.block [])
-/
#guard_msgs in
#eval runWithX verify (.block [.declare z ObjectQ false, .var z ObjectQ])

-- `{ final Object? z; z = null; z = null }` (which flow analysis rejects): assigning to a `final`
-- variable that has already been assigned gets stuck.
/--
info: stuck at: DartLang.LoweredExpr.seq
  (DartLang.LoweredExpr.variableSetAt
    { name := "z", type := DartLang.SimpleType.ObjectQ, isFinal := true }
    { n := 3 }
    (DartLang.LoweredExpr.val (DartLang.Value.null)))
  (DartLang.LoweredExpr.block [])
-/
#guard_msgs in
#eval runWithX verify
  (.block [.declare z ObjectQ false, .variableSet z .null, .variableSet z .null])

/-! ## Calls and returns (see `functions`) -/

-- `not(true)`
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool false) -/
#guard_msgs in
#eval runClosed verify (.call "not" [.bool true] bool)

-- `not(not(true))`
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runClosed verify (.call "not" [.call "not" [.bool true] bool] bool)

-- `alwaysTrue(true)` calls itself once.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runClosed verify (.call "alwaysTrue" [.bool true] bool)

-- `noReturn(1)` falls off the end of its body, so it returns the null object.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.null) -/
#guard_msgs in
#eval runClosed verify (.call "noReturn" [.int 1] Null)

-- `nested()` returns from inside a nested block, so the rest of the block doesn't run.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 2) -/
#guard_msgs in
#eval runClosed verify (.call "nested" [] int)

-- `first(7, false)` returns its first parameter.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 7) -/
#guard_msgs in
#eval runClosed verify (.call "first" [.int 7, .bool false] int)

-- `fail()`: the exception propagates out of the call.
/--
info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError))
-/
#guard_msgs in
#eval runClosed verify (.seq (.call "fail" [] Null) (.int 1))

-- `first(1, null!)`: an exception thrown by an argument propagates out of the call.
/--
info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError))
-/
#guard_msgs in
#eval runClosed verify (.call "first" [.int 1, .nullCheck .null] int)

-- `return 1;` outside any call returns from the whole program.
/-- info: done: DartLang.Outcome.returning (DartLang.Value.int 1) -/
#guard_msgs in
#eval runClosed verify (.block [.ret (.int 1), .int 2])

-- A call of a function that isn't declared gets stuck, once its arguments have been evaluated.
/--
info: stuck at redex: DartLang.LoweredExpr.call
  "undeclared"
  [DartLang.LoweredExpr.val (DartLang.Value.bool true)]
  (DartLang.SimpleType.Null)
-/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100 (.call "undeclared" [.bool true] Null)
  State.empty)

-- A call with the wrong number of arguments gets stuck.
/--
info: stuck at redex: DartLang.LoweredExpr.call "not" [] (DartLang.SimpleType.bool)
-/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100 (.call "not" [] bool) State.empty)

/-! ## Loops and breaks (see `functions`) -/

-- A `while` loop whose body runs once.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runClosed verify (.call "whileOnce" [] bool)

-- A `do` loop's body runs once even if its condition is `false`.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runClosed verify (.call "doOnce" [] bool)

-- `continue` skips the rest of the loop's body.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool false) -/
#guard_msgs in
#eval runClosed verify (.call "skip" [] bool)

-- A break out of an outer labeled statement skips the rest of it.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 2) -/
#guard_msgs in
#eval runClosed verify (.call "nestedBreak" [] int)

-- A break out of an inner loop continues the outer loop's body, which then breaks out of it.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runClosed verify (.call "innerBreak" [] bool)

-- A return propagates out of a loop.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 3) -/
#guard_msgs in
#eval runClosed verify (.call "returnFromLoop" [] int)

-- A break with no labeled statement to break out of gets stuck at the body of the running call.
/--
info: stuck at redex: DartLang.LoweredExpr.frame
  (DartLang.LoweredExpr.breaking "L")
  (DartLang.SimpleType.Null)
-/
#guard_msgs (whitespace := lax) in
#eval stuckRedex (Interp.run (P := verify) 100 (.call "breakOut" [] Null) State.empty)

-- A loop that never breaks runs until the interpreter's fuel runs out.
/--
info: out of fuel at: DartLang.LoweredExpr.seq
  (DartLang.LoweredExpr.null)
  (DartLang.LoweredExpr.loop (DartLang.LoweredExpr.null))
-/
#guard_msgs in
#eval runClosed verify (.loop .null)

/-! ## Integer arithmetic and comparisons -/

/-- The largest 64-bit integer, `2⁶³ - 1`. -/
def maxInt : Int := 2 ^ 63 - 1

/-- Whether running `m` from the empty state gets stuck (`stuck`), or else the run's summary. -/
def stuckOrSummary (m : LoweredExpr) : Std.Format :=
  match Interp.run (P := verify) 100 m State.empty with
  | .stuck _ _ _ => "stuck"
  | r => summary r

-- `maxInt + 1` wraps around in `wrap64` mode, gets stuck in `checked` mode, and is exact in
-- `unbounded` mode.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.int (-9223372036854775808)), stuck,
  done: DartLang.Outcome.normal (DartLang.Value.int 9223372036854775808)]
-/
#guard_msgs (whitespace := lax) in
#eval [stuckOrSummary (.intBin .add (some .wrap64) (.int maxInt) (.int 1)),
  stuckOrSummary (.intBin .add (some .checked) (.int maxInt) (.int 1)),
  stuckOrSummary (.intBin .add (some .unbounded) (.int maxInt) (.int 1))]

-- Arithmetic that stays in range is the same in every mode.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.int (-6)),
  done: DartLang.Outcome.normal (DartLang.Value.int (-6)),
  done: DartLang.Outcome.normal (DartLang.Value.int (-6))]
-/
#guard_msgs (whitespace := lax) in
#eval [stuckOrSummary (.intBin .mul (some .wrap64) (.int 2) (.intBin .sub (some .wrap64) (.int 2)
    (.int 5))),
  stuckOrSummary (.intBin .mul (some .checked) (.int 2) (.intBin .sub (some .checked) (.int 2)
    (.int 5))),
  stuckOrSummary (.intBin .mul (some .unbounded) (.int 2) (.intBin .sub (some .unbounded) (.int 2)
    (.int 5)))]

-- `2⁶² * 4` wraps around to `0` in `wrap64` mode.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 0) -/
#guard_msgs in
#eval stuckOrSummary (.intBin .mul (some .wrap64) (.int (2 ^ 62)) (.int 4))

-- `-(-2⁶³)` wraps around to `-2⁶³` in `wrap64` mode, and gets stuck in `checked` mode.
/-- info: [done: DartLang.Outcome.normal (DartLang.Value.int (-9223372036854775808)), stuck] -/
#guard_msgs in
#eval [stuckOrSummary (.intNeg (some .wrap64) (.int (-2 ^ 63))),
  stuckOrSummary (.intNeg (some .checked) (.int (-2 ^ 63)))]

-- Comparisons: `1 < 2`, `2 <= 2`, `1 > 2` and `1 >= 2`.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.bool true),
  done: DartLang.Outcome.normal (DartLang.Value.bool true),
  done: DartLang.Outcome.normal (DartLang.Value.bool false),
  done: DartLang.Outcome.normal (DartLang.Value.bool false)]
-/
#guard_msgs (whitespace := lax) in
#eval [stuckOrSummary (.intBin .lt (some .checked) (.int 1) (.int 2)),
  stuckOrSummary (.intBin .le (some .checked) (.int 2) (.int 2)),
  stuckOrSummary (.intBin .gt (some .checked) (.int 1) (.int 2)),
  stuckOrSummary (.intBin .ge (some .checked) (.int 1) (.int 2))]

-- An operator whose integer mode hasn't been filled in (outside any call) gets stuck.
/--
info: stuck at redex: DartLang.LoweredExpr.intBin
  (DartLang.IntBinOp.add)
  none
  (DartLang.LoweredExpr.val (DartLang.Value.int 1))
  (DartLang.LoweredExpr.val (DartLang.Value.int 2))
-/
#guard_msgs (whitespace := lax) in
#eval stuckRedex (Interp.run (P := verify) 100 (.intBin .add none (.int 1) (.int 2)) State.empty)

-- A call fills in the integer mode of its function: `maxInt + 1` in `wrapAdd`, `checkedAdd` and
-- `unboundedAdd`.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.int (-9223372036854775808)), stuck,
  done: DartLang.Outcome.normal (DartLang.Value.int 9223372036854775808)]
-/
#guard_msgs (whitespace := lax) in
#eval [stuckOrSummary (.call "wrapAdd" [.int maxInt] int),
  stuckOrSummary (.call "checkedAdd" [.int maxInt] int),
  stuckOrSummary (.call "unboundedAdd" [.int maxInt] int)]

-- `for` loops: `sumBelow(5)` is `0 + 1 + 2 + 3 + 4`, and `sumSkipping(5)` skips `0` and `1`.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.int 10),
  done: DartLang.Outcome.normal (DartLang.Value.int 9)]
-/
#guard_msgs (whitespace := lax) in
#eval [summary (Interp.run (P := verify) 1000 (.call "sumBelow" [.int 5] int) State.empty),
  summary (Interp.run (P := verify) 1000 (.call "sumSkipping" [.int 5] int) State.empty)]

/-! ## Equality of the null object, booleans and integers -/

-- `null == null`, `true == false`, `3 == 3`, `3 == 4` and `0 == null`.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.bool true),
  done: DartLang.Outcome.normal (DartLang.Value.bool false),
  done: DartLang.Outcome.normal (DartLang.Value.bool true),
  done: DartLang.Outcome.normal (DartLang.Value.bool false),
  done: DartLang.Outcome.normal (DartLang.Value.bool false)]
-/
#guard_msgs (whitespace := lax) in
#eval [runClosed verify (.primEq .null .null), runClosed verify (.primEq (.bool true) (.bool false)),
  runClosed verify (.primEq (.int 3) (.int 3)), runClosed verify (.primEq (.int 3) (.int 4)),
  runClosed verify (.primEq (.int 0) .null)]

-- `null! == 1`: an exception thrown by an operand propagates.
/--
info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError))
-/
#guard_msgs in
#eval runClosed verify (.primEq (.nullCheck .null) (.int 1))

-- `x == x`, where parameter `x` refers to an object (see `runWithX`), gets stuck: `==` on objects
-- runs user code.
/--
info: stuck at: DartLang.LoweredExpr.primEq
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 0 }))
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 0 }))
-/
#guard_msgs (whitespace := lax) in
#eval runWithX verify (.primEq (.var x ObjectQ) (.var x ObjectQ))

/-! ## Intrinsic checks for `Expect` assertions -/

/--
Whether running `m` from the empty state completes normally with the null object (`passes`), or
throws because an intrinsic check failed (`fails`); otherwise, the summary of the run.
-/
def checkResult (m : LoweredExpr) : Std.Format :=
  match Interp.run (P := verify) 100 m State.empty with
  | .done (.normal .null) _ => "passes"
  | .done (.throwing (.error .expectFailed)) _ => "fails"
  | r => summary r

-- Each kind of check, on a value it holds of, passes.
/-- info: [passes, passes, passes, passes] -/
#guard_msgs in
#eval [checkResult (.check .isTrue (.bool true)), checkResult (.check .isFalse (.bool false)),
  checkResult (.check .isNull .null), checkResult (.check .isNotNull (.int 0))]

-- Each kind of check, on a value it doesn't hold of, fails.
/-- info: [fails, fails, fails, fails] -/
#guard_msgs in
#eval [checkResult (.check .isTrue (.bool false)), checkResult (.check .isFalse .null),
  checkResult (.check .isNull (.int 0)), checkResult (.check .isNotNull .null)]

-- `Expect.equals` on equal integers, booleans and null objects passes, and on different ones
-- (including values of different types) fails.
/-- info: [passes, passes, passes, fails, fails, fails] -/
#guard_msgs in
#eval [checkResult (.checkEq (.int 3) (.int 3)), checkResult (.checkEq (.bool true) (.bool true)),
  checkResult (.checkEq .null .null), checkResult (.checkEq (.int 3) (.int 4)),
  checkResult (.checkEq (.bool true) (.bool false)), checkResult (.checkEq (.int 0) .null)]

-- `Expect.equals(first(7, true), 7)`: the operands are evaluated left to right.
/-- info: passes -/
#guard_msgs in
#eval checkResult (.checkEq (.call "first" [.int 7, .bool true] int) (.int 7))

-- `Expect.isTrue(null!)`: an exception thrown by the operand propagates.
/--
info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError))
-/
#guard_msgs in
#eval checkResult (.check .isTrue (.nullCheck .null))

-- `Expect.equals` on objects (here, the object that parameter `x` refers to; see `runWithX`) gets
-- stuck: `==` on objects runs user code, which isn't supported yet.
/--
info: stuck at: DartLang.LoweredExpr.checkEq
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 0 }))
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 0 }))
-/
#guard_msgs in
#eval runWithX verify (.checkEq (.var x ObjectQ) (.var x ObjectQ))

/-! ## Programs that throw -/

-- `null!`
/-- info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError)) -/
#guard_msgs in
#eval runClosed verify (.nullCheck .null)

-- `x as bool`, where parameter `x` refers to an `int` (see `runWithX`), so the cast fails.
/-- info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError)) -/
#guard_msgs in
#eval runWithX verify (.as (.var x ObjectQ) bool)

-- `{ null!; x }`: the exception propagates out of the rest of the block, so `x` is never read.
/-- info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError)) -/
#guard_msgs in
#eval runWithX verify (.block [.nullCheck .null, .var x ObjectQ])

-- `{ Object? x; x! }`: the declared `x` (which is null) shadows the parameter `x`.
/-- info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError)) -/
#guard_msgs in
#eval runWithX verify (.block [.declare x ObjectQ true, .nullCheck (.var x ObjectQ)])

/-! ## Programs that get stuck -/

-- `{ Object y; y }` reads `y` before it is assigned.
/--
info: stuck at: DartLang.LoweredExpr.seq
  (DartLang.LoweredExpr.varAt
    { name := "y", type := DartLang.SimpleType.Object, isFinal := false }
    (DartLang.SimpleType.Object)
    { n := 0 })
  (DartLang.LoweredExpr.block [])
-/
#guard_msgs in
#eval runClosed verify (.block [.declare y Object false, .var y Object])

-- `x`, wrongly promoted to `bool`: parameter `x` refers to an `int` (see `runWithX`), so the
-- promotion check fails.
/--
info: stuck at: DartLang.LoweredExpr.varAt
  { name := "x", type := DartLang.SimpleType.ObjectQ, isFinal := false }
  (DartLang.SimpleType.bool)
  { n := 2 }
-/
#guard_msgs in
#eval runWithX verify (.var x bool)

-- The same program runs without promotion checks.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.obj { n := 0 }) -/
#guard_msgs in
#eval runWithX trust (.var x bool)

-- `x._f`, wrongly promoted to `int`: the object that parameter `x` refers to has `true` in its
-- `_f` (see `runWithX`), so the promotion check fails.
/--
info: stuck at: DartLang.LoweredExpr.propertyGet
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 0 }))
  { name := "_f", type := DartLang.SimpleType.ObjectQ, isPromotable := true }
  (DartLang.SimpleType.int)
-/
#guard_msgs in
#eval runWithX verify (.propertyGet (.var x ObjectQ) f int)

-- The same program runs without promotion checks.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.bool true) -/
#guard_msgs in
#eval runWithX trust (.propertyGet (.var x ObjectQ) f int)

-- `x.h`, typed as `int`: the class of the object that parameter `x` refers to dispatches `h` to a
-- getter (see `runWithX`), so the read runs the getter, which returns the null object, and that
-- fails the promotion check.
/--
info: stuck at: DartLang.LoweredExpr.checkPromotion
  (DartLang.SimpleType.int)
  (DartLang.LoweredExpr.val (DartLang.Value.null))
-/
#guard_msgs (whitespace := lax) in
#eval runWithX verify (.propertyGet (.var x ObjectQ) h int)

-- A variable that isn't bound to a cell can't be read.
/--
info: stuck at: DartLang.LoweredExpr.var
  { name := "x", type := DartLang.SimpleType.ObjectQ, isFinal := false }
  (DartLang.SimpleType.ObjectQ)
-/
#guard_msgs in
#eval runClosed verify (.var x ObjectQ)

-- A construct that the translator doesn't support gets stuck, inside a null check.
/--
info: stuck at redex: DartLang.LoweredExpr.unsupported "Switch" (DartLang.SimpleType.ObjectQ)
-/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100
  (.block [.null, .nullCheck (.unsupported "Switch" ObjectQ)]) State.empty)

/-! ## The redex of a stuck program -/

-- `{ x!; x }`, with `x` not bound to a cell: the run gets stuck inside the null check, at the read
-- of `x`.
/--
info: stuck at redex: DartLang.LoweredExpr.var
  { name := "x", type := DartLang.SimpleType.ObjectQ, isFinal := false }
  (DartLang.SimpleType.ObjectQ)
-/
#guard_msgs in
#eval stuckRedex
  (Interp.run (P := verify) 100 (.block [.nullCheck (.var x ObjectQ), .var x Object]) State.empty)

-- `{ Object y; y }` reads `y` before it is assigned: the run gets stuck at the read of `y`,
-- resolved to its cell.
/--
info: stuck at redex: DartLang.LoweredExpr.varAt
  { name := "y", type := DartLang.SimpleType.Object, isFinal := false }
  (DartLang.SimpleType.Object)
  { n := 0 }
-/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100 (.block [.declare y Object false, .var y Object])
  State.empty)

-- `x._f`, wrongly promoted to `int` (see `runWithX`): the run gets stuck at the property read,
-- once its receiver has been evaluated.
/--
info: stuck at redex: DartLang.LoweredExpr.propertyGet
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 0 }))
  { name := "_f", type := DartLang.SimpleType.ObjectQ, isPromotable := true }
  (DartLang.SimpleType.int)
-/
#guard_msgs in
#eval stuckRedex
  (Interp.run (P := verify) 100 ((LoweredExpr.propertyGet (.var x ObjectQ) f int).bindVariables
    [(x, ⟨2⟩)]) σx)

-- A program that completes isn't stuck.
/-- info: not stuck -/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100 (.nullCheck .null) State.empty)

/-! ## Objects and constructors (see `classes` and `constructors`) -/

-- `{ Log l = Log(); C(l); return l.n; }`: constructing a `C` runs `C`'s initializers, then `S`'s
-- initializers, then `S`'s body, then `C`'s body.
/-- info: done: DartLang.Outcome.returning (DartLang.Value.int 1234) -/
#guard_msgs in
#eval runClosed verify (.block [.declare l tLog false, .variableSet l (.new "Log.new" [] tLog),
  .new "C.new" [.var l tLog] tC, .ret (.propertyGet (.var l tLog) pn int)])

-- `{ Log l = Log(); R(l); return l.n; }`: `return;` in `R`'s constructor ends it early.
/-- info: done: DartLang.Outcome.returning (DartLang.Value.int 1) -/
#guard_msgs in
#eval runClosed verify (.block [.declare l tLog false, .variableSet l (.new "Log.new" [] tLog),
  .new "R.new" [.var l tLog] tR, .ret (.propertyGet (.var l tLog) pn int)])

-- `D().x`: the initializer list's initializer of `x` runs after its declaration's, and overwrites
-- it.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 2) -/
#guard_msgs in
#eval runClosed verify (.propertyGet (.new "D.new" [] tD) px int)

-- `D().x = 3`: an assignment to an instance variable, through its implicit setter, evaluates to the
-- value assigned.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 3) -/
#guard_msgs in
#eval runClosed verify (.propertySet (.new "D.new" [] tD) "x" (.int 3))

-- `{ Log l = Log(); l.n = 5; return l.n; }`
/-- info: done: DartLang.Outcome.returning (DartLang.Value.int 5) -/
#guard_msgs in
#eval runClosed verify (.block [.declare l tLog false, .variableSet l (.new "Log.new" [] tLog),
  .propertySet (.var l tLog) "n" (.int 5), .ret (.propertyGet (.var l tLog) pn int)])

-- `C(null!)`: an exception thrown by an argument propagates out of the instance creation.
/--
info: done: DartLang.Outcome.throwing (DartLang.Value.error (DartLang.DynamicError.typeError))
-/
#guard_msgs in
#eval runClosed verify (.new "C.new" [.nullCheck .null] tC)

-- `U()`: `U`'s constructor reads `x` before it's initialized, which gets stuck.
/--
info: stuck at redex: DartLang.LoweredExpr.propertyGet
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 1 }))
  { name := "x", type := DartLang.SimpleType.int, isPromotable := false }
  (DartLang.SimpleType.int)
-/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100 (.new "U.new" [] tU) State.empty)

-- `D().y = 1`: `D` has no setter `y=`, so the assignment gets stuck.
/--
info: stuck at redex: DartLang.LoweredExpr.propertySet
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 1 }))
  "y"
  (DartLang.LoweredExpr.val (DartLang.Value.int 1))
-/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100 (.propertySet (.new "D.new" [] tD) "y" (.int 1))
  State.empty)

/-! ## Instance members (see `classes` and `members`) -/

/-- A local variable `h` of type `H`. -/
def vh : Variable := { name := "h", type := tH }
/-- A local variable `g` of type `G2`. -/
def vg : Variable := { name := "g", type := tG2 }
/-- A local variable `h2` of type `H2`. -/
def vh2 : Variable := { name := "h2", type := tH2 }
/-- A local variable `a` of type `A`. -/
def va : Variable := { name := "a", type := tA }
/-- A local variable `w` of type `W`. -/
def vw : Variable := { name := "w", type := tW }
/-- A local variable `o` of type `Obj`. -/
def vo : Variable := { name := "o", type := tObj }

-- `[A().callF(), B().callF()]`: `callF` calls `f`, which dispatches on the receiver's class, so
-- `B`'s override runs for a `B` (and calls `A`'s `f` with `super.f()`).
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.int 1),
 done: DartLang.Outcome.normal (DartLang.Value.int 11)]
-/
#guard_msgs (whitespace := lax) in
#eval [runClosed verify (.methodCall (.new "A.new" [] tA) "callF" [] int),
  runClosed verify (.methodCall (.new "B.new" [] tB) "callF" [] int)]

-- `C2().bf()`: `super.f()` in `B`'s `bf` calls `A`'s `f`, the one in the superclass of `B` (the
-- class that provides `bf`), not `C2`'s or `B`'s.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 1) -/
#guard_msgs in
#eval runClosed verify (.methodCall (.new "C2.new" [] tC2) "bf" [] int)

-- `[P1().m(), P2().m()]`: the same member body `m`, provided by `P1` and by `P2`, calls `A`'s `f`
-- and `B`'s `f` respectively with `super.f()`.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.int 1),
 done: DartLang.Outcome.normal (DartLang.Value.int 11)]
-/
#guard_msgs (whitespace := lax) in
#eval [runClosed verify (.methodCall (.new "P1.new" [] tP1) "m" [] int),
  runClosed verify (.methodCall (.new "P2.new" [] tP2) "m" [] int)]

-- `[H().x, H().superX()]`: `H`'s getter `x` overrides `G`'s instance variable `x`, which
-- `super.x` reads.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.int 7),
 done: DartLang.Outcome.normal (DartLang.Value.int 5)]
-/
#guard_msgs (whitespace := lax) in
#eval [runClosed verify (.propertyGet (.new "H.new" [] tH) px int),
  runClosed verify (.methodCall (.new "H.new" [] tH) "superX" [] int)]

-- `{ H h = H(); h.setSuperX(9); return h.superX(); }`: `super.x = 9` assigns `G`'s instance
-- variable.
/-- info: done: DartLang.Outcome.returning (DartLang.Value.int 9) -/
#guard_msgs in
#eval runClosed verify (.block [.declare vh tH false, .variableSet vh (.new "H.new" [] tH),
  .methodCall (.var vh tH) "setSuperX" [.int 9] Null,
  .ret (.methodCall (.var vh tH) "superX" [] int)])

-- `{ G2 g = G2(); g.y = 4; return g.y; }`: the setter `y=` and the getter `y` run.
/-- info: done: DartLang.Outcome.returning (DartLang.Value.int 104) -/
#guard_msgs in
#eval runClosed verify (.block [.declare vg tG2 false, .variableSet vg (.new "G2.new" [] tG2),
  .propertySet (.var vg tG2) "y" (.int 4), .ret (.propertyGet (.var vg tG2) py int)])

-- `G2().y = 4`: an assignment through a setter evaluates to the value assigned.
/-- info: done: DartLang.Outcome.normal (DartLang.Value.int 4) -/
#guard_msgs in
#eval runClosed verify (.propertySet (.new "G2.new" [] tG2) "y" (.int 4))

-- `[H2().y, { H2 h2 = H2(); h2.setSuperY(4); return h2.superY(); }]`: `super.y = 4` and `super.y`
-- run `G2`'s setter and getter, not `H2`'s getter.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.int 0),
 done: DartLang.Outcome.returning (DartLang.Value.int 104)]
-/
#guard_msgs (whitespace := lax) in
#eval [runClosed verify (.propertyGet (.new "H2.new" [] tH2) py int),
  runClosed verify (.block [.declare vh2 tH2 false, .variableSet vh2 (.new "H2.new" [] tH2),
    .methodCall (.var vh2 tH2) "setSuperY" [.int 4] Null,
    .ret (.methodCall (.var vh2 tH2) "superY" [] int)])]

-- `[W().x, W().sup, W().readX(), V().readX()]`: `W`'s instance variable `x` shadows `V`'s, so a
-- `W` has two cells for them. `x` reads `W`'s, even from `V`'s method `readX` (since the getter
-- is virtual), and `super.x` reads `V`'s.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.int 2),
 done: DartLang.Outcome.normal (DartLang.Value.int 1),
 done: DartLang.Outcome.normal (DartLang.Value.int 2),
 done: DartLang.Outcome.normal (DartLang.Value.int 1)]
-/
#guard_msgs (whitespace := lax) in
#eval [runClosed verify (.propertyGet (.new "W.new" [] tW) px int),
  runClosed verify (.propertyGet (.new "W.new" [] tW) ⟨"sup", int, false⟩ int),
  runClosed verify (.methodCall (.new "W.new" [] tW) "readX" [] int),
  runClosed verify (.methodCall (.new "V.new" [] tV) "readX" [] int)]

-- `[{ W w = W(); w.setSup(9); return w.sup; }, { W w = W(); w.setSup(9); return w.x; }]`:
-- `super.x = 9` assigns `V`'s instance variable, and leaves `W`'s alone.
/--
info: [done: DartLang.Outcome.returning (DartLang.Value.int 9),
 done: DartLang.Outcome.returning (DartLang.Value.int 2)]
-/
#guard_msgs (whitespace := lax) in
#eval [runClosed verify (.block [.declare vw tW false, .variableSet vw (.new "W.new" [] tW),
    .methodCall (.var vw tW) "setSup" [.int 9] Null,
    .ret (.propertyGet (.var vw tW) ⟨"sup", int, false⟩ int)]),
  runClosed verify (.block [.declare vw tW false, .variableSet vw (.new "W.new" [] tW),
    .methodCall (.var vw tW) "setSup" [.int 9] Null, .ret (.propertyGet (.var vw tW) px int)])]

-- `[identical(A(), A()), { A a = A(); return identical(a, a); }, identical(1, 1),
-- identical(null, A())]`
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.bool false),
 done: DartLang.Outcome.returning (DartLang.Value.bool true),
 done: DartLang.Outcome.normal (DartLang.Value.bool true),
 done: DartLang.Outcome.normal (DartLang.Value.bool false)]
-/
#guard_msgs (whitespace := lax) in
#eval [runClosed verify (.identical (.new "A.new" [] tA) (.new "A.new" [] tA)),
  runClosed verify (.block [.declare va tA false, .variableSet va (.new "A.new" [] tA),
    .ret (.identical (.var va tA) (.var va tA))]),
  runClosed verify (.identical (.int 1) (.int 1)),
  runClosed verify (.identical .null (.new "A.new" [] tA))]

-- `[E() == E(), Obj() == Obj(), { Obj o = Obj(); return o == o; }]`: `==` on objects calls the
-- receiver's `operator ==`.
/--
info: [done: DartLang.Outcome.normal (DartLang.Value.bool true),
 done: DartLang.Outcome.normal (DartLang.Value.bool false),
 done: DartLang.Outcome.returning (DartLang.Value.bool true)]
-/
#guard_msgs (whitespace := lax) in
#eval [runClosed verify (.methodCall (.new "E.new" [] tE) "==" [.new "E.new" [] tE] bool),
  runClosed verify (.methodCall (.new "Obj.new" [] tObj) "==" [.new "Obj.new" [] tObj] bool),
  runClosed verify (.block [.declare vo tObj false, .variableSet vo (.new "Obj.new" [] tObj),
    .ret (.methodCall (.var vo tObj) "==" [.var vo tObj] bool)])]

-- `super.f()` outside a member body: its slot isn't filled in, so it gets stuck.
/--
info: stuck at redex: DartLang.LoweredExpr.superCall
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 0 }))
  "f"
  none
  []
  (DartLang.SimpleType.int)
-/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100 (.superCall (.new "A.new" [] tA) "f" none [] int)
  State.empty)

-- `1.f()`: a method call on an integer gets stuck.
/--
info: stuck at redex: DartLang.LoweredExpr.methodCall
  (DartLang.LoweredExpr.val (DartLang.Value.int 1))
  "f"
  []
  (DartLang.SimpleType.int)
-/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100 (.methodCall (.int 1) "f" [] int) State.empty)

-- `A().g()`: `A` has no member `g`, so the call gets stuck.
/--
info: stuck at redex: DartLang.LoweredExpr.methodCall
  (DartLang.LoweredExpr.val (DartLang.Value.obj { n := 0 }))
  "g"
  []
  (DartLang.SimpleType.int)
-/
#guard_msgs in
#eval stuckRedex (Interp.run (P := verify) 100 (.methodCall (.new "A.new" [] tA) "g" [] int)
  State.empty)

/-! ## A program that runs out of fuel -/

-- `{ x!; x }`, with parameter `x` as in `runWithX`, given fuel for only one step: the block becomes
-- a sequence, and then the run stops.
/--
info: out of fuel at: DartLang.LoweredExpr.seq
  (DartLang.LoweredExpr.nullCheck
    (DartLang.LoweredExpr.varAt
      { name := "x", type := DartLang.SimpleType.ObjectQ, isFinal := false }
      (DartLang.SimpleType.ObjectQ)
      { n := 2 }))
  (DartLang.LoweredExpr.block
    [DartLang.LoweredExpr.varAt
       { name := "x", type := DartLang.SimpleType.ObjectQ, isFinal := false }
       (DartLang.SimpleType.Object)
       { n := 2 }])
-/
#guard_msgs in
#eval summary
  (Interp.run (P := verify) 1
    ((LoweredExpr.block [.nullCheck (.var x ObjectQ), .var x Object]).bindVariables [(x, ⟨2⟩)])
    σx)

end DartSemantics.Tests.Interpreter
