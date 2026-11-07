module
public import DartLang.RuntimeTypes
public import DartLang.Types

/-!
# Kernel-like types

A concrete type representation for programs translated from the Dart front end's Kernel
representation, with the classes that such programs declare. It covers `dynamic`, `void`, `Never`,
`Null`, `Object`, *interface types* of classes without type parameters (user classes, and classes
such as `num`, `int`, `bool` and `String`), `List<T>` and `Map<K, V>`, and the nullable form `T?` of
each of these where it means something. Function types, type parameters, other generic classes,
`FutureOr`, records and extension types aren't represented.

## Class hierarchies

Subtyping between interface types depends on the program's classes, but `DartTypeRepr` needs a
subtype relation that depends only on the type representation. So the representation is indexed
by a *class hierarchy* (`ClassHierarchy`): a table of each class's superclasses, which the
translator emits for each program. `KernelType H` is the type representation for the classes in
`H`.

Classes are identified by number, because the Lean kernel compares numbers quickly, and the
translator proves facts about the table with `decide`, which the kernel evaluates. Two numbers are
reserved: `boolClass` and `intClass`, so that the special types `bool` and `int` of `DartTypeRepr`
don't depend on the table.

A hierarchy only has to describe the classes that can appear in a type of the program, and only
the superclasses that can themselves appear in a type. Leaving out a superclass that can't (such
as `Comparable<num>`, a generic class) can't change the answer to any subtype question between
types that can be represented.

## Canonical forms

Nullability is a flag on the constructors where it means something. `Null?`, `Never?`,
`dynamic?` and `void?` can't be written: the translator normalizes them (to `Null`, `Null`,
`dynamic` and `void`), as the front end does. So the only distinct types that are subtypes of
each other are the *top types* `dynamic`, `void` and `Object?`.
-/

namespace DartLang

/-- The number of class `bool` in every class hierarchy. -/
@[expose]
public def boolClass : Nat := 0

/-- The number of class `int` in every class hierarchy. -/
@[expose]
public def intClass : Nat := 1

namespace ClassHierarchy

/--
The superclasses that the table `supers` lists for class `c`: `supers[c]`, or none if `c` is out
of range.
-/
@[expose]
public def supersOf (supers : List (List Nat)) (c : Nat) : List Nat :=
  supers.getD c []

/--
Whether the table `supers` is well formed: every entry lists neither `bool` nor `int` (which can't
be extended or implemented), and is transitively closed (it lists every superclass of every class
it lists).
-/
@[expose]
public def isWellFormed (supers : List (List Nat)) : Bool :=
  supers.all fun cs =>
    !cs.contains boolClass && !cs.contains intClass &&
      cs.all fun d => (supersOf supers d).all fun e => cs.contains e

end ClassHierarchy

/--
A class hierarchy: for each class, its name and its proper superclasses (direct or indirect).
Class `c` is named `names[c]`, and its superclasses are `supersOf supers c`. Classes `boolClass`
and `intClass` are `bool` and `int`.
-/
public structure ClassHierarchy where
  /-- The name of each class, for printing types. -/
  names : List String
  /-- The proper superclasses of each class. -/
  supers : List (List Nat)
  /-- The table of superclasses is well formed (the translator proves this with `decide`). -/
  wf : ClassHierarchy.isWellFormed supers = true

namespace ClassHierarchy

variable (H : ClassHierarchy)

/-- Whether class `c` is class `d` or a subclass of it. -/
@[expose]
public def isSubclass (c d : Nat) : Bool :=
  c == d || (supersOf H.supers c).contains d

/--
The superclasses of a class's superclass are superclasses of the class: if `d` is a superclass of
`c` (`hd`) and `e` is a superclass of `d` (`he`), then `e` is a superclass of `c`
(`e ∈ supersOf H.supers c`).
-/
public theorem mem_supersOf_trans {c d e : Nat} (hd : d ∈ supersOf H.supers c)
    (he : e ∈ supersOf H.supers d) : e ∈ supersOf H.supers c := by
  have hwf := H.wf
  unfold supersOf at hd ⊢
  rw [List.getD_eq_getElem?_getD] at hd ⊢
  cases hc : H.supers[c]? with
  | none => simp [hc] at hd
  | some cs =>
    simp only [hc, Option.getD_some] at hd ⊢
    have hrow := List.all_eq_true.mp hwf cs (List.mem_of_getElem? hc)
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hrow
    exact hrow.2 d hd e he

/--
No class has `bool` as a superclass: if `d` is a superclass of `c` (`hd`), it isn't `bool`
(`d ≠ boolClass`).
-/
public theorem ne_boolClass_of_mem_supersOf {c d : Nat} (hd : d ∈ supersOf H.supers c) :
    d ≠ boolClass := by
  have hwf := H.wf
  unfold supersOf at hd
  rw [List.getD_eq_getElem?_getD] at hd
  cases hc : H.supers[c]? with
  | none => simp [hc] at hd
  | some cs =>
    simp only [hc, Option.getD_some] at hd
    have hrow := List.all_eq_true.mp hwf cs (List.mem_of_getElem? hc)
    intro heq
    subst heq
    simp_all

/-- `isSubclass` is reflexive (`H.isSubclass c c = true`). -/
public theorem isSubclass_refl (c : Nat) : H.isSubclass c c = true := by
  simp [isSubclass]

/--
`isSubclass` is transitive: if `c` is a subclass of `d` (`hcd`) and `d` is a subclass of `e`
(`hde`), then `c` is a subclass of `e` (`H.isSubclass c e = true`).
-/
public theorem isSubclass_trans {c d e : Nat} (hcd : H.isSubclass c d = true)
    (hde : H.isSubclass d e = true) : H.isSubclass c e = true := by
  simp only [isSubclass, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hcd hde ⊢
  rcases hcd with rfl | hcd
  · exact hde
  · rcases hde with rfl | hde
    · exact Or.inr hcd
    · exact Or.inr (H.mem_supersOf_trans hcd hde)

/--
Only `bool` itself is a subclass of `bool`: if `c` isn't `bool` (`hc`), it isn't a subclass of
`bool` (`H.isSubclass c boolClass = false`).
-/
public theorem isSubclass_boolClass {c : Nat} (hc : c ≠ boolClass) :
    H.isSubclass c boolClass = false := by
  simp only [isSubclass, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  refine ⟨hc, ?_⟩
  rw [Bool.eq_false_iff]
  intro hd
  rw [List.contains_iff_mem] at hd
  exact H.ne_boolClass_of_mem_supersOf hd rfl

end ClassHierarchy

/--
A Dart type, for a program whose classes are described by the class hierarchy `H` (see the module
doc). `nullable` says whether the type is the nullable form `T?`.
-/
public inductive KernelType (H : ClassHierarchy) where
  | dynamic : KernelType H
  | void : KernelType H
  | Never : KernelType H
  | Null : KernelType H
  /-- `Object`, or `Object?` if `nullable`. -/
  | Object (nullable : Bool) : KernelType H
  /-- The interface type of class `cls` (which has no type parameters), or its nullable form. -/
  | interface (cls : Nat) (nullable : Bool) : KernelType H
  /-- `List<elem>`, or its nullable form. -/
  | List (elem : KernelType H) (nullable : Bool) : KernelType H
  /-- `Map<key, value>`, or its nullable form. -/
  | Map (key value : KernelType H) (nullable : Bool) : KernelType H
  deriving DecidableEq, Repr

namespace KernelType

variable {H : ClassHierarchy}

/--
`==` on `KernelType` is structural equality, decided by the derived `DecidableEq`, as for
`SimpleType`.
-/
public instance instBEqKernelType : BEq (KernelType H) := instBEqOfDecidableEq

/-- `==` on `KernelType` is reflexive (`(T == T) = true`). -/
public theorem instLawfulBEq_rfl {T : KernelType H} : (T == T) = true :=
  decide_eq_true rfl

/-- Types that `==` says are equal (`h`) are equal (`T₁ = T₂`). -/
public theorem instLawfulBEq_eq_of_beq {T₁ T₂ : KernelType H}
    (h : instBEqKernelType.beq T₁ T₂ = true) : T₁ = T₂ :=
  of_decide_eq_true h

/-- Whether `T` is a top type: `dynamic`, `void` or `Object?`. -/
@[expose]
public def isTop : KernelType H → Bool
  | dynamic => true
  | void => true
  | Object nullable => nullable
  | _ => false

/-- Whether `T` is nullable, that is, whether `Null` is a subtype of it. -/
@[expose]
public def isNullable : KernelType H → Bool
  | dynamic => true
  | void => true
  | Never => false
  | Null => true
  | Object nullable => nullable
  | interface _ nullable => nullable
  | List _ nullable => nullable
  | Map _ _ nullable => nullable

/--
Whether `S` is a subtype of `T`, following the subtype rules of the language specification:

- `Never` is a subtype of every type, and every type is a subtype of the top types;
- a top type is a subtype only of the top types, and `Null` only of the nullable types;
- a nullable type is a subtype only of nullable types;
- `Object`, interface types, `List<T>` and `Map<K, V>` are subtypes of `Object`;
- an interface type is a subtype of the interface type of each superclass (`isSubclass`); and
- `List` and `Map` are covariant in their type arguments.

In the last three rules, `S` can be nullable only if `T` is (`!n || m`).
-/
@[expose]
public def isSubtype : KernelType H → KernelType H → Bool
  | Never, _ => true
  | dynamic, T => T.isTop
  | void, T => T.isTop
  | Null, T => T.isNullable
  | Object n, T => match T with
    | dynamic | void => true
    | Object m => !n || m
    | _ => false
  | interface c n, T => match T with
    | dynamic | void => true
    | Object m => !n || m
    | interface d m => (!n || m) && H.isSubclass c d
    | _ => false
  | List S n, T => match T with
    | dynamic | void => true
    | Object m => !n || m
    | List U m => (!n || m) && isSubtype S U
    | _ => false
  | Map K V n, T => match T with
    | dynamic | void => true
    | Object m => !n || m
    | Map K' V' m => (!n || m) && isSubtype K K' && isSubtype V V'
    | _ => false

/-- `isSubtype` is reflexive (`T.isSubtype T = true`). -/
public theorem isSubtype_refl (T : KernelType H) : T.isSubtype T = true := by
  cases T <;> simp [isSubtype, isTop, isNullable, ClassHierarchy.isSubclass_refl]
  case List T' n => exact isSubtype_refl T'
  case Map K V n => exact ⟨isSubtype_refl K, isSubtype_refl V⟩

/--
`isSubtype` is transitive: if `T` is a subtype of `U` (`hTU`) and `U` is a subtype of `V` (`hUV`),
then `T` is a subtype of `V` (`T.isSubtype V = true`).
-/
public theorem isSubtype_trans (T U V : KernelType H) (hTU : T.isSubtype U = true)
    (hUV : U.isSubtype V = true) : T.isSubtype V = true := by
  revert hTU hUV
  cases T <;> cases U <;> cases V <;> simp [isSubtype, isTop, isNullable]
  case interface.interface.interface c n d m e k =>
    intro hnm hcd hmk hde
    exact ⟨by grind, H.isSubclass_trans hcd hde⟩
  case List.List.List S n T' m U k =>
    intro hnm hST hmk hTU
    exact ⟨by grind, isSubtype_trans S T' U hST hTU⟩
  case Map.Map.Map K₁ V₁ n K₂ V₂ m K₃ V₃ k =>
    intro hnm hK₁₂ hV₁₂ hmk hK₂₃ hV₂₃
    exact ⟨⟨by grind, isSubtype_trans K₁ K₂ K₃ hK₁₂ hK₂₃⟩, isSubtype_trans V₁ V₂ V₃ hV₁₂ hV₂₃⟩
  -- What's left is reasoning about the nullable flags.
  all_goals grind

/--
The non-nullable form of `T` (`NonNull(T)` in the language specification): `Null` becomes `Never`,
the top types other than `Object?` are unchanged, and the other types lose their nullable flag.
-/
@[expose]
public def NonNull : KernelType H → KernelType H
  | dynamic => dynamic
  | void => void
  | Never => Never
  | Null => Never
  | Object _ => Object false
  | interface c _ => interface c false
  | List T _ => List T false
  | Map K V _ => Map K V false

/-- `T`, written as in Dart, with class names taken from `H`. -/
public def toDart : KernelType H → String
  | dynamic => "dynamic"
  | void => "void"
  | Never => "Never"
  | Null => "Null"
  | Object n => suffix "Object" n
  | interface c n => suffix (H.names.getD c s!"#{c}") n
  | List T n => suffix s!"List<{toDart T}>" n
  | Map K V n => suffix s!"Map<{toDart K}, {toDart V}>" n
where
  /-- `s`, followed by `?` if `nullable`. -/
  suffix (s : String) (nullable : Bool) : String := if nullable then s ++ "?" else s

/-- `KernelType H` is a type representation, with `bool` and `int` the reserved classes. -/
public instance instDartTypeRepr : DartTypeRepr (KernelType H) where
  rfl := instLawfulBEq_rfl
  eq_of_beq := instLawfulBEq_eq_of_beq
  le T U := isSubtype T U = true
  le_refl := isSubtype_refl
  le_trans := isSubtype_trans
  toString := toDart
  decideEq T U := inferInstance
  decideLE T U :=
    if h : T.isSubtype U then
      isTrue $ by simp_all [LE.le]
    else
      isFalse $ by simp_all [LE.le]
  decideLT T U :=
    if hrev : U.isSubtype T then
      isFalse $ by simp_all [LT.lt]
    else if h : T.isSubtype U then
      isTrue $ by simp_all [LT.lt]
    else
      isFalse $ by simp_all [LT.lt]
  NonNull := NonNull
  bool := interface boolClass false
  dynamic := dynamic
  int := interface intClass false
  Map K V := Map K V false
  Null := Null
  Object := Object false
  ObjectQ := Object true
  default := Never

namespace instDartTypeRepr

/-- `T ≤ U` holds for `KernelType H` exactly when `T.isSubtype U`. -/
@[simp]
public theorem le.iff {T U : KernelType H} : T ≤ U ↔ T.isSubtype U := by rfl

/-- `T < U` holds for `KernelType H` exactly when `T.isSubtype U` and not `U.isSubtype T`. -/
@[simp]
public theorem lt.iff {T U : KernelType H} :
    T < U ↔ T.isSubtype U ∧ ¬U.isSubtype T := by rfl

end instDartTypeRepr

/-- `int` isn't a subtype of `bool` (`¬ int ≤ bool`), since no class has `bool` as a superclass. -/
public theorem not_int_le_bool :
    ¬ (DartTypeRepr.int : KernelType H) ≤ DartTypeRepr.bool := by
  simp only [instDartTypeRepr.le.iff]
  simp [DartTypeRepr.int, DartTypeRepr.bool, isSubtype,
    H.isSubclass_boolClass (c := intClass) (by decide)]

/-- For `KernelType`, subtyping is decidable, so the run-time check always terminates. -/
public instance instDartRuntimeTypeRepr : DartRuntimeTypeRepr (KernelType H) where
  RtSub S T b := decide (S ≤ T) = b
  rtSub_true h := by simpa using h
  rtSub_false h := by simpa using h
  rtSub_of_le h := by simpa using h

/-- For `KernelType`, the run-time check answers immediately, using no fuel. -/
public instance instRtSubChecker : RtSubChecker (KernelType H) where
  check fuel S T := some (decide (S ≤ T), fuel)
  check_fuel_le h := by
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  check_mono k h := by
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  check_sound h := by
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1
  check_complete h := ⟨0, 0, by simp only [Option.some.injEq, Prod.mk.injEq]; exact ⟨h, trivial⟩⟩

end KernelType
end DartLang
