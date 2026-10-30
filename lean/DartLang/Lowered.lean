module
public import DartLang.Elements
public import DartLang.Loc
public import DartLang.Types

namespace DartLang

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)

/--
The kinds of dynamic error (in the specification's sense) that can occur in the subset of Dart
modeled so far.

This is a placeholder. The language specification says that when a dynamic error occurs, a
corresponding error object is thrown; for a dynamic type error, the thrown object implements
`TypeError`. Once the semantics can allocate objects of core library classes, a dynamic error
will throw such an object, and this type (with `Value.error`) will go away.
-/
public inductive DynamicError where
  /--
  A dynamic type error: a failed type check at run time, such as a null check (`e!`) finding the
  null object, or a failed cast (`e as T`).
  -/
  | typeError
  deriving Repr, BEq, DecidableEq

/-
`Value`, `LoweredExpr` and `EctxItem` are mutually inductive: a value may hold a captured
continuation (a list of evaluation context items), and evaluation context items hold the
expressions still to be evaluated.
-/
mutual

/--
A run-time value: in the specification's terms, an object. The null object, booleans, integers
and error objects are represented directly; other objects live in the heap and are referred to by
location.
-/
public inductive Value where
  /-- The null object. -/
  | null
  /-- The object `true` or `false`. -/
  | bool (b : Bool)
  /--
  An integer: an instance of `int`. Every Dart `int` is represented by its mathematical value, a
  Lean `Int` (which is unbounded). Integer literals are always in 64-bit range; how arithmetic
  stays in range will be decided per member when the semantics has arithmetic.
  -/
  | int (n : Int)
  /-- A reference to the object stored at location `ℓ`. -/
  | obj (ℓ : Loc)
  /-- The object thrown when dynamic error `e` occurs. -/
  | error (e : DynamicError)
  /--
  A captured continuation: the evaluation context items around a suspended computation,
  innermost first. Reserved for constructs that capture continuations (such as `await`); nothing
  creates one yet.
  -/
  | cont (k : List EctxItem)

/--
Lowered, fully type-checked AST form.

Note that we make no distinction between statements and expressions. This is for future
compatibility with the Iris framework.
-/
public inductive LoweredExpr where
  /--
  A reference to local variable or formal parameter `v`, whose static type (after any promotion)
  is `T`.
  -/
  | var (v : Variable) (T : τ)
  /-- An application of the null check operator, `m!`. -/
  | nullCheck (m : LoweredExpr)
  /-- A cast expression, `m as T`. -/
  | as (m : LoweredExpr) (T : τ)
  /-- An is-expression (a type test), `m is T`. -/
  | is (m : LoweredExpr) (T : τ)
  /-- The null literal, `null`. -/
  | null
  /-- A boolean literal, `true` or `false`. -/
  | bool (b : Bool)
  /-- An integer literal. -/
  | int (n : Int)
  /--
  A local variable declaration of `v`, with type `T`. Its scope is the rest of the enclosing
  `block`.

  `startsNull` says whether the variable starts out holding the null object. Otherwise, it starts
  out unassigned, and it is an error to read it before it is assigned. Flow analysis sets
  `startsNull` based on whether `v` is final and whether `T` is nullable, as Dart requires.
  -/
  | declare (v : Variable) (T : τ) (startsNull : Bool)
  /--
  A conditional: evaluates `m₂` if `m₁` evaluates to `true`, and `m₃` otherwise. Its static type
  is `T`.
  -/
  | cond (m₁ m₂ m₃ : LoweredExpr) (T : τ)
  /--
  A block statement, `{ m₁ … mₙ }`, which executes its elements in order. Since `LoweredExpr`
  doesn't distinguish statements from expressions, its value is the null object.
  -/
  | block (exprs : List LoweredExpr)
  /--
  A property extraction, `m.p`: a read of property `p` of the value of `m`, whose static type
  (after any promotion) is `T`.
  -/
  | propertyGet (m : LoweredExpr) (p : Property) (T : τ)
  /--
  An assignment to local variable or formal parameter `v`, `v = m`: evaluates `m`, stores its
  value in `v`, and evaluates to that value. (Kernel calls this a `VariableSet`.) If `v` is
  `final`, it must still be unassigned.
  -/
  | variableSet (v : Variable) (m : LoweredExpr)
  /--
  A placeholder for a construct that the translator from Kernel doesn't support yet, of static
  type `T`. `kind` names the construct (for example, the Kernel node's class), so that a program
  that gets stuck on it says why. It has no head step: running it gets stuck.
  -/
  | unsupported (kind : String) (T : τ)
  /--
  A call of the top-level function whose key is `f`, with arguments `args`, evaluated left to
  right. The static type of the call expression is `T`. The function's declaration is looked up in
  the program's function table (`SemanticParams.functions`). A function's key identifies it
  uniquely in the program (for example, its library's URI together with its name); it isn't
  necessarily the function's name, so functions with the same name in different libraries have
  different keys.

  TODO(paulberry): So far all arguments are positional. Named arguments are meant to be added as a
  separate list giving each argument's name, if any, so that they can be intermixed with positional
  arguments and evaluated in source order; only binding arguments to formal parameters will depend
  on names.
  -/
  | call (f : String) (args : List LoweredExpr) (T : τ)
  /-- A return statement, `return m;`. (`return;` is `ret null`.) -/
  | ret (m : LoweredExpr)
  /-
  The remaining constructors are *run-time-only* forms: flow analysis never produces them. They
  appear only as a program runs.
  -/
  /-- An expression that has completed normally, evaluating to `v`. -/
  | val (v : Value)
  /-- An expression that has thrown exception object `v`, propagating outward. -/
  | throwing (v : Value)
  /--
  An expression that has returned `v` (by a return statement), propagating outward to the body of
  the function that is returning (`frame`).
  -/
  | returning (v : Value)
  /--
  The body `m` of a running call of a function, whose result has static type `T`. It turns a
  return of `v` into completing normally with `v`, and it turns completing normally (falling off
  the end of the body) into completing normally with the null object.
  -/
  | frame (m : LoweredExpr) (T : τ)
  /--
  A reference to local variable or formal parameter `v`, whose static type (after any promotion)
  is `T`, resolved to the heap cell at `ℓ`. Declaring a variable resolves each `var v T` in its
  scope to `varAt v T ℓ`.
  -/
  | varAt (v : Variable) (T : τ) (ℓ : Loc)
  /-- Evaluate `m₁`, discard its value, then evaluate `m₂`. A block runs as a sequence. -/
  | seq (m₁ m₂ : LoweredExpr)
  /--
  An assignment to local variable or formal parameter `v`, resolved to the heap cell at `ℓ`.
  Declaring a variable resolves each `variableSet v m` in its scope to `variableSetAt v ℓ m`.
  -/
  | variableSetAt (v : Variable) (ℓ : Loc) (m : LoweredExpr)

/--
An evaluation context item: an expression with a hole in the position that evaluates next. See
`EctxItem.fill`.
-/
public inductive EctxItem where
  /-- `□!` -/
  | nullCheck
  /-- `□ as T` -/
  | as (T : τ)
  /-- `□ is T` -/
  | is (T : τ)
  /-- `cond(□, m₂, m₃)` (of type `T`) -/
  | cond (m₂ m₃ : LoweredExpr) (T : τ)
  /-- `□.p` (of type `T`) -/
  | propertyGet (p : Property) (T : τ)
  /-- `seq(□, m₂)` -/
  | seq (m₂ : LoweredExpr)
  /-- `v = □`, with `v` resolved to the heap cell at `ℓ` -/
  | variableSetAt (v : Variable) (ℓ : Loc)
  /--
  `f(v₁, …, vₙ, □, m₁, …, mₖ)` (of type `T`): a call whose arguments before the hole have
  evaluated to `vs`, and whose arguments after it, `ms`, are still to be evaluated
  -/
  | call (f : String) (vs : List Value) (ms : List LoweredExpr) (T : τ)
  /-- `return □;` -/
  | ret
  /-- `frame(□)` (of type `T`): the body of a running call -/
  | frame (T : τ)

end

deriving instance Repr for Value, LoweredExpr, EctxItem
deriving instance BEq for Value, LoweredExpr, EctxItem

local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)

/--
A static type for a value, for `LoweredExpr.typeOf`: the most precise type that doesn't depend
on the heap. (An object's class is in the heap, so an object reference just gets `Object`.)
-/
@[expose]
public def Value.typeOf : Value → τ
  | .null => Γ.Null
  | .bool _ => Γ.bool
  | .int _ => Γ.int
  | .obj _ => Γ.Object
  | .error _ => Γ.Object
  | .cont _ => Γ.ObjectQ

/--
The static type of an expression.

For the run-time-only forms, which flow analysis never sees, the types are chosen only to make
this function total, and no proof relies on them. In particular, `throwing`, `returning` and `ret`
would best be typed `Never`, which `DartTypeRepr` doesn't have; they get the top type `Object?`
instead.
-/
@[expose]
public def LoweredExpr.typeOf :
    LoweredExpr → τ
  | var _ T => T
  | nullCheck m => NonNull m.typeOf
  | as _ T => T
  | is _ _ => Γ.bool
  | null => Γ.Null
  | bool _ => Γ.bool
  | int _ => Γ.int
  | declare _ _ _ => Γ.Null
  | cond _ _ _ T => T
  | block _ => Γ.Null
  | propertyGet _ _ T => T
  | variableSet _ m => m.typeOf
  | unsupported _ T => T
  | call _ _ T => T
  | ret _ => Γ.ObjectQ
  | val v => v.typeOf
  | throwing _ => Γ.ObjectQ
  | returning _ => Γ.ObjectQ
  | frame _ T => T
  | varAt _ T _ => T
  | seq _ m₂ => m₂.typeOf
  | variableSetAt _ _ m => m.typeOf

/--
The declaration of a top-level function: its formal parameters `params`, in order, and its body
`body`. The program's function table (`SemanticParams.functions`) maps each function's key (see
`LoweredExpr.call`) to its declaration.
-/
public structure FunctionDecl where
  /-- The function's formal parameters, in order. -/
  params : List Variable
  /-- The function's body, in which the formal parameters are free variables. -/
  body : LoweredExpr

local notation "EctxItem" => EctxItem (τ := τ)

/--
How an expression's evaluation (or a statement's execution) *completes*, in the sense of the
language specification's "Statement Completion" section: normally, evaluating to an object, by
throwing an exception object, or by returning an object. Stack traces aren't modeled.

The specification has two more kinds of completion: breaking and continuing (each with or without
a label). Variants for them will be added here when the semantics supports `break` and `continue`
statements.
-/
public inductive Outcome where
  /-- Completes normally, evaluating to `v`. -/
  | normal (v : Value)
  /-- Throws exception object `v`. -/
  | throwing (v : Value)
  /-- Returns `v` (by a return statement), from the function whose body is running. -/
  | returning (v : Value)
  deriving Repr, BEq

local notation "Outcome" => Outcome (τ := τ)

/-- The expression that has completed with outcome `o`. -/
@[expose]
public def Outcome.toExpr : Outcome → LoweredExpr
  | .normal v => .val v
  | .throwing v => .throwing v
  | .returning v => .returning v

/-- How `m` completed, if it has. -/
@[expose]
public def LoweredExpr.toOutcome? : LoweredExpr → Option Outcome
  | .val v => some (.normal v)
  | .throwing v => some (.throwing v)
  | .returning v => some (.returning v)
  | _ => none

omit Γ in
/-- Converting an outcome `o` to an expression and back gives `o`. -/
public theorem Outcome.toOutcome?_toExpr (o : Outcome) : o.toExpr.toOutcome? = some o := by
  cases o <;> rfl

omit Γ in
/-- An expression `m` that has completed with outcome `o` (`h`) is that outcome as an expression. -/
public theorem LoweredExpr.toExpr_of_toOutcome? {m : LoweredExpr} {o : Outcome}
    (h : m.toOutcome? = some o) : o.toExpr = m := by
  cases m <;> simp only [toOutcome?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

/-- Plug `m` into the hole of context item `Ki`. -/
@[expose]
public def EctxItem.fill : EctxItem → LoweredExpr → LoweredExpr
  | .nullCheck, m => .nullCheck m
  | .as T, m => .as m T
  | .is T, m => .is m T
  | .cond m₂ m₃ T, m => .cond m m₂ m₃ T
  | .propertyGet p T, m => .propertyGet m p T
  | .seq m₂, m => .seq m m₂
  | .variableSetAt v ℓ, m => .variableSetAt v ℓ m
  | .call f vs ms T, m => .call f (vs.map .val ++ m :: ms) T
  | .ret, m => .ret m
  | .frame T, m => .frame m T

/--
Whether context item `Ki` handles a return (`returning`) in its hole, rather than propagating it
outward: only the body of a running call (`frame`) does.
-/
@[expose]
public def EctxItem.handlesReturn : EctxItem → Bool
  | .frame _ => true
  | _ => false

omit Γ in
/-- An expression with a hole plugged (`Ki.fill m`) hasn't completed (`toOutcome? = none`). -/
public theorem EctxItem.toOutcome?_fill (Ki : EctxItem) (m : LoweredExpr) :
    (Ki.fill m).toOutcome? = none := by
  cases Ki <;> rfl

/--
Split a list of expressions (such as a call's arguments) into the values that it starts with, and
the rest, which starts with the first expression that isn't a value (if any).
-/
@[expose]
public def LoweredExpr.splitVals : List LoweredExpr → List Value × List LoweredExpr
  | .val v :: ms => let r := splitVals ms; (v :: r.1, r.2)
  | ms => ([], ms)

omit Γ in
/--
Splitting a list of expressions `ms` into its leading values and the rest loses nothing: the
values, as expressions, followed by the rest, are `ms`
(`(splitVals ms).1.map .val ++ (splitVals ms).2 = ms`).
-/
public theorem LoweredExpr.splitVals_append (ms : List LoweredExpr) :
    (splitVals ms).1.map .val ++ (splitVals ms).2 = ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    cases m <;> simp only [splitVals, List.map_nil, List.nil_append, List.map_cons,
      List.cons_append, ih]

omit Γ in
/--
The values `vs` followed by expressions `ms` that don't start with a value (`h`) split into `vs`
and `ms` (`splitVals (vs.map .val ++ ms) = (vs, ms)`).
-/
public theorem LoweredExpr.splitVals_map_val_append (vs : List Value) {ms : List LoweredExpr}
    (h : ∀ v ms', ms ≠ .val v :: ms') : splitVals (vs.map .val ++ ms) = (vs, ms) := by
  induction vs with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    cases ms with
    | nil => rfl
    | cons m ms =>
      cases m
      case val v => exact absurd rfl (h v ms)
      all_goals rfl
  | cons v vs ih => simp [splitVals, ih]

omit Γ in
/--
A list of values followed by an expression `m` (`vs.map .val ++ m :: ms`) is never a list of values
(`ws.map .val`) unless `m` is itself a value (`∃ v, m = .val v`).
-/
public theorem LoweredExpr.eq_val_of_map_val_append {vs ws : List Value} {m : LoweredExpr}
    {ms : List LoweredExpr} (h : vs.map .val ++ m :: ms = ws.map .val) : ∃ v, m = .val v := by
  have hm : m ∈ ws.map LoweredExpr.val := h ▸ List.mem_append_right _ List.mem_cons_self
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hm
  exact ⟨v, rfl⟩

omit Γ in
/--
A list of expressions splits in at most one way into values followed by an expression that isn't
a value, followed by the rest: if `vs₁.map .val ++ m₁ :: ms₁ = vs₂.map .val ++ m₂ :: ms₂` (`h`),
where neither `m₁` (`h₁`) nor `m₂` (`h₂`) is a value, then the two splits are the same
(`vs₁ = vs₂`, `m₁ = m₂` and `ms₁ = ms₂`).
-/
public theorem LoweredExpr.map_val_append_inj {vs₁ vs₂ : List Value} {m₁ m₂ : LoweredExpr}
    {ms₁ ms₂ : List LoweredExpr} (h₁ : ∀ v, m₁ ≠ .val v) (h₂ : ∀ v, m₂ ≠ .val v)
    (h : vs₁.map .val ++ m₁ :: ms₁ = vs₂.map .val ++ m₂ :: ms₂) :
    vs₁ = vs₂ ∧ m₁ = m₂ ∧ ms₁ = ms₂ := by
  induction vs₁ generalizing vs₂ with
  | nil =>
    cases vs₂ with
    | nil => simpa using h
    | cons v vs₂ =>
      simp only [List.map_nil, List.nil_append, List.map_cons, List.cons_append,
        List.cons.injEq] at h
      exact absurd h.1 (h₁ v)
  | cons v vs₁ ih =>
    cases vs₂ with
    | nil =>
      simp only [List.map_cons, List.cons_append, List.map_nil, List.nil_append,
        List.cons.injEq] at h
      exact absurd h.1.symm (h₂ v)
    | cons w vs₂ =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, LoweredExpr.val.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl, rfl⟩

omit Γ in
/-- Two lists of values are the same as expressions exactly when they're the same lists. -/
@[simp]
public theorem LoweredExpr.map_val_inj {vs₁ vs₂ : List Value} :
    vs₁.map LoweredExpr.val = vs₂.map .val ↔ vs₁ = vs₂ :=
  List.map_inj_right fun _ _ h => LoweredExpr.val.inj h

omit Γ in
/--
The `simp` form of `map_val_append_inj`: if neither `m₁` (`h₁`) nor `m₂` (`h₂`) is a value, then
`vs₁.map .val ++ m₁ :: ms₁ = vs₂.map .val ++ m₂ :: ms₂` exactly when `vs₁ = vs₂`, `m₁ = m₂` and
`ms₁ = ms₂`.
-/
@[simp]
public theorem LoweredExpr.map_val_append_cons_inj {vs₁ vs₂ : List Value} {m₁ m₂ : LoweredExpr}
    {ms₁ ms₂ : List LoweredExpr} (h₁ : ∀ v, m₁ ≠ .val v) (h₂ : ∀ v, m₂ ≠ .val v) :
    vs₁.map .val ++ m₁ :: ms₁ = vs₂.map .val ++ m₂ :: ms₂ ↔ vs₁ = vs₂ ∧ m₁ = m₂ ∧ ms₁ = ms₂ := by
  constructor
  · exact map_val_append_inj h₁ h₂
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

omit Γ in
/--
A list of values (`ws.map .val`) is never values followed by an expression `m` that isn't a value
(`h`), then the rest (`vs.map .val ++ m :: ms`).
-/
@[simp]
public theorem LoweredExpr.map_val_append_cons_ne {vs ws : List Value} {m : LoweredExpr}
    {ms : List LoweredExpr} (h : ∀ v, m ≠ .val v) :
    (vs.map .val ++ m :: ms = ws.map .val) = False := by
  refine eq_false fun he => ?_
  obtain ⟨v, rfl⟩ := eq_val_of_map_val_append he
  exact h v rfl

omit Γ in
/-- The symmetric form of `map_val_append_cons_ne`. -/
@[simp]
public theorem LoweredExpr.map_val_ne_append_cons {vs ws : List Value} {m : LoweredExpr}
    {ms : List LoweredExpr} (h : ∀ v, m ≠ .val v) :
    (ws.map .val = vs.map .val ++ m :: ms) = False := by
  refine eq_false fun he => ?_
  obtain ⟨v, rfl⟩ := eq_val_of_map_val_append he.symm
  exact h v rfl

omit Γ in
/-- A list of values splits into itself and nothing else (`splitVals (vs.map .val) = (vs, [])`). -/
@[simp]
public theorem LoweredExpr.splitVals_map_val (vs : List Value) :
    splitVals (vs.map .val) = (vs, []) := by
  simpa using splitVals_map_val_append vs (ms := []) (by simp)

/--
Plug `m` into the hole of the evaluation context `k`, a list of context items, innermost first.
-/
@[expose]
public def fillCtx (k : List EctxItem) (m : LoweredExpr) : LoweredExpr :=
  k.foldl (fun m Ki => Ki.fill m) m

end DartLang
