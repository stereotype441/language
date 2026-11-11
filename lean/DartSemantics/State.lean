module
public import DartLang.Lowered
public import DartLang.PrettyPrint

/-!
# The run-time state

The state of a running program: for now, just the heap.
-/

namespace DartSemantics

open DartLang

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "Value" => Value (τ := τ)

/--
The contents of a heap cell.

A cell is either the storage for a variable (a local variable, or an instance variable of an
object), or an object's own cell: for an instance of a class, the cell records its class and where
its instance variables are stored; for a string, it holds the string's contents. Keeping instance
variables in cells of their own means that the program logic can reason about each instance
variable separately, with the same points-to assertion as for a local variable.

This type is separate from `Value`: values never refer to cells, only to locations.
-/
public inductive Cell where
  /--
  The storage for a variable whose value is `v`. The variable is either a local variable or an
  instance variable of an object (see `object`).
  -/
  | val (v : Value)
  /--
  A local variable that has been declared but not yet assigned. Only variables that are `final`, or
  whose type isn't nullable, start out this way; the others are initialized to the null object.
  -/
  | uninit
  /--
  An object (an instance of a class), whose class has key `cls` (see `SemanticParams.classes`),
  and whose dynamic type is `dynamicType` (the class's instance type). Its instance variables are
  stored in other cells: `fields` maps the key of each instance variable (see
  `ClassDecl.instanceVariables`) to its cell's location.
  -/
  | object (cls : String) (dynamicType : τ) (fields : List (String × Loc))
  /--
  A string, whose UTF-16 code units are `cu` (exactly a Dart string, which can hold unpaired
  surrogates; see `ConstValue.string`). Its dynamic type is `String`. Strings are immutable: no
  step changes a string's cell.
  -/
  | string (cu : List UInt16)
  deriving Repr, BEq

-- Display `Cell`'s constructors in leading-dot form, such as `.val (.int 0)` (see
-- `DartLang.PrettyPrint`).
pp_dot_ctors Cell

local notation "Cell" => Cell (τ := τ)

omit Γ in
/--
Whether cell `c` is the storage for a variable (holding a value, or uninitialized), rather than an
object's own cell. Only a variable's cell can be assigned.
-/
@[expose]
public def Cell.isVar : Cell → Bool
  | .val _ | .uninit => true
  | .object _ _ _ | .string _ => false

/--
The state of a running program.

This is a structure, rather than just a heap, so that more components can be added as the
semantics grows (for example, the queue of pending tasks that asynchronous code needs).
-/
public structure State where
  /--
  The heap: the cell at location `ℓ` is `heap[ℓ.n]`. Cells are allocated sequentially and never
  freed, so the heap is an array that only grows. Allocating a cell is a `push`, which keeps the
  interpreter fast (provided the state is used linearly; see `Interp.primStep`).
  -/
  heap : Array Cell
  /--
  The canonical object of each constant evaluated so far (see `LoweredExpr.constant`), by its
  structural description, as a list of pairs (most recent first). Only constants whose values are
  objects in the heap are recorded.
  -/
  constants : List (ConstValue × Loc)
  deriving Repr

local notation "State" => State (τ := τ)

/-- The state of a program that hasn't allocated anything. -/
@[expose]
public def State.empty : State := ⟨#[], []⟩

/-- The cell at location `ℓ`, if it has been allocated. -/
@[expose]
public def State.lookup (σ : State) (ℓ : Loc) : Option Cell := σ.heap[ℓ.n]?

/-- The location that the next allocation will use. -/
@[expose]
public def State.fresh (σ : State) : Loc := ⟨σ.heap.size⟩

/-- Allocate a new cell, at location `σ.fresh`, holding `c`. -/
@[expose]
public def State.alloc (σ : State) (c : Cell) : State := { σ with heap := σ.heap.push c }

/--
Replace the cell at location `ℓ` with `c`, if `ℓ` has been allocated (otherwise, leave the state
alone). Like `alloc`, this updates the array in place if the state is used linearly.
-/
@[expose]
public def State.update (σ : State) (ℓ : Loc) (c : Cell) : State :=
  { σ with heap := σ.heap.set! ℓ.n c }

/--
Allocate a new cell for each of `cs`, in order: the locations of the new cells (`.1`, in the
order of `cs`), and the state afterwards (`.2`). (Calling a function uses this to allocate the
cells of its formal parameters.)
-/
@[expose]
public def State.allocAll (σ : State) : List Cell → List Loc × State
  | [] => ([], σ)
  | c :: cs =>
    -- `σ.fresh` is read before `σ` is used by `alloc`, so that the update can be done in place.
    let ℓ := σ.fresh
    let r := (σ.alloc c).allocAll cs
    (ℓ :: r.1, r.2)

omit Γ in
/-- Allocating a cell for each of `cs` gives one location per cell. -/
@[simp]
public theorem State.length_allocAll (σ : State) (cs : List Cell) :
    (σ.allocAll cs).1.length = cs.length := by
  induction cs generalizing σ with
  | nil => rfl
  | cons c cs ih => simp [State.allocAll, ih]

/--
Allocate a new object of the class whose key is `cls`, whose dynamic type is `T`, and whose
instance variables have keys `names`: a cell for each instance variable, uninitialized, and then
the object's own cell. The result is the location of the object's own cell (`.1`) and the state
afterwards (`.2`).
-/
@[expose]
public def State.allocObject (σ : State) (cls : String) (T : τ) (names : List String) :
    Loc × State :=
  let r := σ.allocAll (names.map fun _ => .uninit)
  -- As in `allocAll`, `fresh` is read before the state is used by `alloc`.
  let ℓ := r.2.fresh
  (ℓ, r.2.alloc (.object cls T (names.zip r.1)))

/--
The dynamic type of value `v`, in the specification's sense: the class of the object that `v`
represents.

The dynamic type of an exception object (`Value.error`) isn't defined yet. The specification
leaves its class unspecified, except that it implements `TypeError`, and the type representation
has no type for that yet. Nothing in the subset of Dart modeled so far can inspect an exception
object, since there is no way to catch one. A captured continuation (`Value.cont`) isn't a Dart
object, so it has no dynamic type.
-/
@[expose]
public def State.dynamicType (σ : State) : Value → Option τ
  | .null => some Γ.Null
  | .bool _ => some Γ.bool
  | .int _ => some Γ.int
  | .obj ℓ =>
    match σ.lookup ℓ with
    | some (.object _ T _) => some T
    | some (.string _) => some Γ.String
    | _ => none
  | .error _ => none
  | .cont _ => none

omit Γ in
/-- The code units of the string that value `v` refers to, if it refers to a string. -/
@[expose]
public def State.string? (σ : State) : Value → Option (List UInt16)
  | .obj ℓ =>
    match σ.lookup ℓ with
    | some (.string cu) => some cu
    | _ => none
  | _ => none

omit Γ in
/--
Whether two values are equal, for the intrinsic check `LoweredExpr.checkEq` and for equality
`LoweredExpr.primEq`, if they can be compared without running user code: two strings are equal if
they have the same code units (`String`'s `==`, which can't be overridden, since `String` can't be
extended); a string is unequal to the null object, a boolean or an integer; and otherwise, as
`Value.primEq?` says. Anything else (in particular, an instance of a class, whose `==` runs user
code) can't be compared (`none`).
-/
@[expose]
public def State.primEq? (σ : State) (v₁ v₂ : Value) : Option Bool :=
  match σ.string? v₁, σ.string? v₂ with
  | some cu₁, some cu₂ => some (cu₁ == cu₂)
  | some _, none =>
    match v₂ with
    | .null | .bool _ | .int _ => some false
    | _ => none
  | none, some _ =>
    match v₁ with
    | .null | .bool _ | .int _ => some false
    | _ => none
  | none, none => Value.primEq? v₁ v₂

omit Γ in
/--
The string form of value `v`, as a part of a string concatenation (`LoweredExpr.concat`), if it
has one that doesn't come from user code: a string's code units, `"null"`, `"true"` or `"false"`,
or an integer's decimal form (with a leading `-` if it's negative).
-/
@[expose]
public def State.stringPart? (σ : State) : Value → Option (List UInt16)
  | .null => some (DartString.ofString "null")
  | .bool b => some (DartString.ofString (if b then "true" else "false"))
  | .int n => some (DartString.ofString (toString n))
  | v => σ.string? v

omit Γ in
/--
Allocate the canonical object of constant `c`, whose own cell is `cell` (for a string constant,
the string), recording it in the table of constants: the new object is at `σ.fresh`.
-/
@[expose]
public def State.allocConst (σ : State) (c : ConstValue) (cell : Cell) : State :=
  { σ.alloc cell with constants := (c, σ.fresh) :: σ.constants }

omit Γ in
/--
The value of constant `c` in state `σ`, and the state afterwards (see `LoweredExpr.constant`): the
null object, a boolean or an integer is the value itself (`ConstValue.prim?`), and the state is
unchanged. Any other constant evaluates to its canonical object: the one that the table of
constants records for `c`, if any; otherwise (for a string), a new string object, which is recorded
in the table (`allocConst`). (`none` for a constant that has no value yet, which can't happen for
the kinds of constant so far.)
-/
@[expose]
public def State.constant? (σ : State) (c : ConstValue) : Option (Value × State) :=
  match c.prim? with
  | some v => some (v, σ)
  | none =>
    match σ.constants.lookup c with
    | some ℓ => some (.obj ℓ, σ)
    | none =>
      match c with
      | .string cu => some (.obj σ.fresh, σ.allocConst (.string cu) (.string cu))
      | _ => none

omit Γ in
/--
The key of the class of the object that value `v` refers to, and where its instance variables are
stored (see `Cell.object`), if `v` refers to an object in the heap.
-/
@[expose]
public def State.object? (σ : State) : Value → Option (String × List (String × Loc))
  | .obj ℓ =>
    match σ.lookup ℓ with
    | some (.object k _ fs) => some (k, fs)
    | _ => none
  | _ => none

omit Γ in
/-- A newly allocated cell holds what it was allocated with. -/
@[simp]
public theorem State.lookup_alloc_fresh (σ : State) (c : Cell) :
    (σ.alloc c).lookup σ.fresh = some c := by
  simp [State.lookup, State.alloc, State.fresh]

omit Γ in
/-- Updating an allocated cell (`h`) replaces what it holds with `c`. -/
public theorem State.lookup_update_self {σ : State} {ℓ : Loc} {c₀ : Cell} (h : σ.lookup ℓ = some c₀)
    (c : Cell) : (σ.update ℓ c).lookup ℓ = some c := by
  simp only [State.lookup] at h
  have hlt : ℓ.n < σ.heap.size := by
    by_contra hge
    simp [Array.getElem?_eq_none (Nat.le_of_not_lt hge)] at h
  simp [State.lookup, State.update, hlt]

omit Γ in
/-- Updating the cell at `ℓ` leaves the cell at every other location `ℓ'` (`hne`) alone. -/
public theorem State.lookup_update_ne {σ : State} {ℓ ℓ' : Loc} (hne : ℓ' ≠ ℓ) (c : Cell) :
    (σ.update ℓ c).lookup ℓ' = σ.lookup ℓ' := by
  have hn : ℓ.n ≠ ℓ'.n := fun h => hne (by cases ℓ; cases ℓ'; simp_all)
  simp [State.lookup, State.update, Array.getElem?_setIfInBounds_ne hn]

omit Γ in
/-- Allocating a cell (`σ.alloc c`) doesn't change the table of constants. -/
@[simp]
public theorem State.constants_alloc (σ : State) (c : Cell) :
    (σ.alloc c).constants = σ.constants := rfl

omit Γ in
/-- Updating a cell (`σ.update ℓ c`) doesn't change the table of constants. -/
@[simp]
public theorem State.constants_update (σ : State) (ℓ : Loc) (c : Cell) :
    (σ.update ℓ c).constants = σ.constants := rfl

omit Γ in
/--
Allocating the canonical object of constant `c` (`σ.allocConst c cell`) records it, at
`σ.fresh`, in the table of constants.
-/
@[simp]
public theorem State.constants_allocConst (σ : State) (c : ConstValue) (cell : Cell) :
    (σ.allocConst c cell).constants = (c, σ.fresh) :: σ.constants := rfl

omit Γ in
/-- Allocating cells (`σ.allocAll cs`) doesn't change the table of constants. -/
@[simp]
public theorem State.constants_allocAll (σ : State) (cs : List Cell) :
    (σ.allocAll cs).2.constants = σ.constants := by
  induction cs generalizing σ with
  | nil => rfl
  | cons c cs ih => exact ih (σ.alloc c)

omit Γ in
/-- Allocating an object (`σ.allocObject cls T names`) doesn't change the table of constants. -/
@[simp]
public theorem State.constants_allocObject (σ : State) (cls : String) (T : τ)
    (names : List String) : (σ.allocObject cls T names).2.constants = σ.constants :=
  State.constants_allocAll σ _

/--
Updating the cell at `ℓ` doesn't change any value's dynamic type, if:
- the cell holds `c₀` (`h`), which is a variable's cell (`hc₀`); and
- the new contents `c` are a variable's cell too (`hc`).
-/
public theorem State.dynamicType_update {σ : State} {ℓ : Loc} {c₀ c : Cell}
    (h : σ.lookup ℓ = some c₀) (hc₀ : c₀.isVar = true) (hc : c.isVar = true)
    (v : Value) : (σ.update ℓ c).dynamicType v = σ.dynamicType v := by
  cases v with
  | obj ℓ' =>
    simp only [State.dynamicType]
    by_cases hℓ : ℓ' = ℓ
    · subst hℓ
      rw [State.lookup_update_self h, h]
      cases c₀ <;> cases c <;> simp_all [Cell.isVar]
    · rw [State.lookup_update_ne hℓ]
  | _ => rfl

omit Γ in
/--
Updating the cell at `ℓ` doesn't change which object any value refers to, if:
- the cell holds `c₀` (`h`), which is a variable's cell (`hc₀`); and
- the new contents `c` are a variable's cell too (`hc`).
-/
public theorem State.object?_update {σ : State} {ℓ : Loc} {c₀ c : Cell}
    (h : σ.lookup ℓ = some c₀) (hc₀ : c₀.isVar = true) (hc : c.isVar = true)
    (v : Value) : (σ.update ℓ c).object? v = σ.object? v := by
  cases v with
  | obj ℓ' =>
    simp only [State.object?]
    by_cases hℓ : ℓ' = ℓ
    · subst hℓ
      rw [State.lookup_update_self h, h]
      cases c₀ <;> cases c <;> simp_all [Cell.isVar]
    · rw [State.lookup_update_ne hℓ]
  | _ => rfl

omit Γ in
/--
Values that `Value.primEq?` can compare (`h`), which are the null object, booleans and integers,
compare the same way in every state (`σ.primEq? v₁ v₂ = some b`).
-/
public theorem State.primEq?_of_value {σ : State} {v₁ v₂ : Value} {b : Bool}
    (h : Value.primEq? v₁ v₂ = some b) : σ.primEq? v₁ v₂ = some b := by
  cases v₁ <;> cases v₂ <;> simp_all [Value.primEq?, State.primEq?, State.string?]

end DartSemantics
