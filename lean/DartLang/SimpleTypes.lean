module
public import DartLang.RuntimeTypes
public import DartLang.Types

namespace DartLang

/--
A minimal type system sufficient for studying flow analysis.

TODO(paulberry): expand on this as needed.
-/
public inductive SimpleType where
  | Object : SimpleType
  | ObjectQ : SimpleType
  | dynamic : SimpleType
  /--
  The type `void`. Like `Object?` and `dynamic`, it's a top type: every type is a subtype of it,
  and it's a subtype of exactly the top types. It differs from them only statically (for example,
  the value of an expression of type `void` can't be used); at run time, every subtype check gives
  the same answer for `void` as for `Object?`.
  -/
  | void : SimpleType
  | Null : SimpleType
  | Never : SimpleType
  | int : SimpleType
  | bool : SimpleType
  /-- The type `String`, which (like `int` and `bool`) can't be extended or implemented. -/
  | String : SimpleType
  | List (elementType : SimpleType) : SimpleType
  | Map (key value : SimpleType) : SimpleType
  /--
  The (non-generic) class type with key `name`. `supers` lists the class's proper supertypes,
  other than `Object` and the top types, by key (as a class hierarchy computes them: its
  superclass, the superclass's superclass, and so on, plus implemented interfaces). `Class n s`
  is a subtype of `Class m t` when they're the same class type (`n = m` and `s = t`), or when `m`
  is one of `s` and `t ⊆ s` (every supertype of `m` is also a supertype of `n`). The second
  condition makes subtyping transitive for every value, with no well-formedness condition on
  `supers`.
  -/
  | Class (name : String) (supers : List String) : SimpleType
  deriving Repr, DecidableEq, Repr

namespace SimpleType

/--
`==` on `SimpleType` is structural equality, decided by the derived `DecidableEq`. (A derived
`BEq` would do the same, but with this many constructors, its equation lemmas make `simp` loop in
the proofs below.)
-/
public instance instBEqSimpleType : BEq SimpleType := instBEqOfDecidableEq

/-- `==` on `SimpleType` is reflexive (`(T == T) = true`). -/
public theorem instLawfulBEq_rfl {T : SimpleType} : (T == T) = true :=
  decide_eq_true rfl

/-- Types that `==` says are equal (`h`) are equal (`T₁ = T₂`). -/
public theorem instLawfulBEq_eq_of_beq {T₁ T₂ : SimpleType}
    (h : instBEqSimpleType.beq T₁ T₂ = true) : T₁ = T₂ :=
  of_decide_eq_true h

@[expose]
public def isSubtype : SimpleType -> SimpleType -> Bool
  | Never,     _         => true
  | _,         ObjectQ   => true
  | _,         dynamic   => true
  | _,         void      => true
  | Object,    Object    => true
  | Null,      Null      => true
  | int,       int       => true
  | int,       Object    => true
  | bool,      bool      => true
  | bool,      Object    => true
  | String,    String    => true
  | String,    Object    => true
  | List _,    Object    => true
  | List T,    List U    => isSubtype T U
  | Map _ _,   Object    => true
  | Map K₁ V₁, Map K₂ V₂ => isSubtype K₁ K₂ && isSubtype V₁ V₂
  | Class _ _, Object    => true
  | Class n s, Class m t => (n == m && s == t) || (s.contains m && t.all s.contains)
  | _,         _         => false

/-- `isSubtype` is reflexive (`T.isSubtype T = true`). -/
public theorem isSubtype_refl (T : SimpleType) : T.isSubtype T = true := by
  cases T <;> try simp [isSubtype]
  case List T' => apply isSubtype_refl
  case Map K V => constructor <;> apply isSubtype_refl

/--
`isSubtype` is transitive: if `T` is a subtype of `U` (`hTU`) and `U` is a subtype of `V` (`hUV`),
then `T` is a subtype of `V` (`T.isSubtype V = true`).
-/
public theorem isSubtype_trans (T U V : SimpleType) (hTU : T.isSubtype U = true)
    (hUV : U.isSubtype V = true) : T.isSubtype V = true := by
  -- `cases` needs the hypotheses back in the goal, so that they're specialized to each case.
  revert hTU hUV
  cases T <;> cases U <;> cases V <;> try simp [isSubtype]
  case List.List.List T' U' V' => apply isSubtype_trans
  case Map.Map.Map K₁ V₁ K₂ V₂ K₃ V₃ =>
    intro hK₁₂ hV₁₂ hK₂₃ hV₂₃
    constructor
    · apply isSubtype_trans K₁ K₂ K₃ (by assumption) (by assumption)
    · apply isSubtype_trans V₁ V₂ V₃ (by assumption) (by assumption)
  case Class.Class.Class n s m t o u =>
    -- Either way, the middle class's supertypes are among the first's.
    rintro (⟨rfl, rfl⟩ | ⟨hm, hts⟩) (⟨rfl, rfl⟩ | ⟨ho, hut⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨ho, hut⟩
    · exact Or.inr ⟨hm, hts⟩
    · exact Or.inr ⟨hts o ho, fun x hx => hts x (hut x hx)⟩

@[expose]
public def NonNull : SimpleType -> SimpleType
  | ObjectQ => Object
  | Object  => Object
  | dynamic => dynamic
  | void    => void
  | Null    => Never
  | Never   => Never
  | int     => int
  | bool    => bool
  | String  => String
  | List T' => List T'
  | Map K V => Map K V
  | Class n s => Class n s

public instance instSimpleTypeRepr : DartTypeRepr SimpleType where
  rfl := instLawfulBEq_rfl
  eq_of_beq := instLawfulBEq_eq_of_beq
  le T U := isSubtype T U = true
  le_refl := isSubtype_refl
  le_trans := isSubtype_trans
  toString T := (repr T).pretty
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
  bool := bool
  dynamic := dynamic
  int := int
  Map := Map
  Null := Null
  Object := Object
  ObjectQ := ObjectQ
  String := String
  default := Never

namespace instSimpleTypeRepr

/-- `T ≤ U` holds for `SimpleType` exactly when `T.isSubtype U`. -/
@[simp]
public theorem le.iff {T U : SimpleType} : T ≤ U ↔ T.isSubtype U := by rfl

/-- `T < U` holds for `SimpleType` exactly when `T.isSubtype U` and not `U.isSubtype T`. -/
@[simp]
public theorem lt.iff {T U : SimpleType} :
    T < U ↔ T.isSubtype U ∧ ¬U.isSubtype T := by rfl

/-- The `dynamic` type of the `DartTypeRepr` instance is `SimpleType.dynamic`. -/
@[simp]
public theorem dynamic.eq :
    (inferInstance : DartTypeRepr SimpleType).dynamic = dynamic := by rfl

/-- The `int` type of the `DartTypeRepr` instance is `SimpleType.int`. -/
@[simp]
public theorem int.eq :
    (inferInstance : DartTypeRepr SimpleType).int = int := by rfl

/-- The `Map` type constructor of the `DartTypeRepr` instance is `SimpleType.Map`. -/
@[simp]
public theorem Map.eq :
    (inferInstance : DartTypeRepr SimpleType).Map = Map := by rfl

/-- The `Object` type of the `DartTypeRepr` instance is `SimpleType.Object`. -/
@[simp]
public theorem Object.eq :
    (inferInstance : DartTypeRepr SimpleType).Object = Object := by rfl

/-- The `Object?` type of the `DartTypeRepr` instance is `SimpleType.ObjectQ`. -/
@[simp]
public theorem ObjectQ.eq :
    (inferInstance : DartTypeRepr SimpleType).ObjectQ = ObjectQ := by rfl

/-- The `String` type of the `DartTypeRepr` instance is `SimpleType.String`. -/
@[simp]
public theorem String.eq :
    (inferInstance : DartTypeRepr SimpleType).String = String := by rfl

end instSimpleTypeRepr

/-- For `SimpleType`, subtyping is decidable, so the run-time check always terminates. -/
public instance instDartRuntimeTypeRepr : DartRuntimeTypeRepr SimpleType where
  RtSub S T b := decide (S ≤ T) = b
  rtSub_true h := by simpa using h
  rtSub_false h := by simpa using h
  rtSub_of_le h := by simpa using h

/-- For `SimpleType`, the run-time check answers immediately, using no fuel. -/
public instance instRtSubChecker : RtSubChecker SimpleType where
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

end SimpleType
end DartLang
