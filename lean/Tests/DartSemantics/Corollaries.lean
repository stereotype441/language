module
public import DartSemantics.Safety

/-!
# Corollaries of safety

Small programs whose safety depends on promotion (and, for one, on demotion by an assignment, and
for another, on a `final` variable being assigned only while it is unassigned), proved safe for
every type representation that obeys `TypeLaws`, and every choice of `SemanticParams`. When
`SemanticParams.promotionChecks` is `PromotionChecks.verify`, "safe" includes that every promoted
read passes its promotion check: the promotions are sound.

These are worked examples, by hand, of using the typing rules (`Compat`) and the safety theorem
(`safety`) end to end: the flow analysis soundness theorem will produce proofs like these for every
program that flow analysis accepts. Nothing in the libraries depends on them.
`SemanticTyping.lean` instantiates them at `SimpleType`.
-/

namespace DartSemantics

open DartLang Iris Iris.BI Iris.ProgramLogic

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "State" => State (τ := τ)
local notation "Fact" => Fact (τ := τ)

/--
The program `{ x as T; x }`, where `x` has static type `Tx` and the second read of `x` is promoted
to `T` by the cast.
-/
@[expose]
public def castThenRead (x : Variable) (Tx T : τ) : LoweredExpr :=
  .block [.as (.var x Tx) T, .var x T]

/--
`{ x as T; x }` is semantically well typed, with type `Null`, given that `x` holds a value that
satisfies `U` (`[.var x U]`), if `U` is a subtype of `x`'s static type `Tx` (`hU`). It guarantees
afterwards that `x` holds a value that satisfies `T`, as well as `U` (`[.var x T, .var x U]`).
-/
public theorem castThenRead_typed {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]
    [SemanticParams τ] {x : Variable} {U Tx T : τ} (hU : U ≤ Tx) :
    SemTyped GF [.var x U] (castThenRead x Tx T) Γ.Null (fun _ => [.var x T, .var x U]) := by
  refine SemTyped.block_cons (fun _ _ _ h => by cases h)
    (SemTyped.as_var (List.mem_singleton_self _) hU) ?_
  exact SemTyped.block_cons (fun _ _ _ h => by cases h)
    (SemTyped.var (List.mem_cons_self ..) le_rfl) (SemTyped.block_nil _)

/--
`{ x as T; x }`, started in state `σ` with its variables bound by `bindings`, never gets stuck, and
every outcome it completes with is consistent with `Null` (`OutcomeOk Γ.Null o`), if:
- `U` is a subtype of `x`'s static type `Tx` (`hU`);
- the bindings are suitable (`hb`); and
- `x` holds a value that satisfies `U` in `σ` (`hσ`).

In particular, the read of `x` promoted to `T` never fails its promotion check.
-/
public theorem castThenRead_safe [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF]
    {x : Variable} {U Tx T : τ} (hU : U ≤ Tx) (σ : State) (bindings : List (Variable × Loc))
    (hb : BindingsOk σ bindings) (hσ : FactHolds σ bindings (.var x U)) :
    adequate .NotStuck ((castThenRead x Tx T).bindVariables bindings) σ
      (fun o _ => OutcomeOk Γ.Null o) :=
  safety (GF := GF) σ bindings (castThenRead_typed hU) hb fun f hf => by
    rw [List.mem_singleton.1 hf]
    exact hσ

/--
The program `{ x._f!; x._f }`, where `x` has static type `Tx`, the first read of `x._f` (property
`p`) has static type `W`, and the second read of `x._f` is promoted to `NonNull W` by the null
check.
-/
@[expose]
public def nullCheckThenRead (x : Variable) (Tx : τ) (p : Property) (W : τ) : LoweredExpr :=
  .block [.nullCheck (.propertyGet (.var x Tx) p W), .propertyGet (.var x Tx) p (Γ.NonNull W)]

/--
`{ x._f!; x._f }` is semantically well typed, with type `Null`, given that `x` holds a value
that satisfies `U`, which refers to an object with an instance variable named `p.name`, holding a
value that satisfies `W` (`[.var x U, .field x p.name W]`), if `U` is a subtype of `x`'s static
type `Tx` (`hU`). It also guarantees afterwards that the instance variable holds a value that
satisfies `NonNull W` (`.field x p.name (Γ.NonNull W)`).
-/
public theorem nullCheckThenRead_typed {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]
    [SemanticParams τ] (L : TypeLaws τ) {x : Variable} {p : Property} {U Tx W : τ}
    (hU : U ≤ Tx) :
    SemTyped GF [.var x U, .field x p.name W] (nullCheckThenRead x Tx p W) Γ.Null
      (fun _ => [.field x p.name (Γ.NonNull W), .var x U, .field x p.name W]) := by
  refine SemTyped.block_cons (fun _ _ _ h => by cases h)
    (SemTyped.nullCheck_field L (List.mem_cons_self ..) hU (by simp) le_rfl) ?_
  exact SemTyped.block_cons (fun _ _ _ h => by cases h)
    (SemTyped.propertyGet (by simp) hU (List.mem_cons_self ..) le_rfl) (SemTyped.block_nil _)

/--
`{ x._f!; x._f }`, started in state `σ` with its variables bound by `bindings`, never gets stuck,
and every outcome it completes with is consistent with `Null` (`OutcomeOk Γ.Null o`), if:
- `U` is a subtype of `x`'s static type `Tx` (`hU`);
- the bindings are suitable (`hb`);
- `x` holds a value that satisfies `U` in `σ` (`hx`); and
- that value refers to an object with an instance variable named `p.name`, holding a value that
  satisfies `W` in `σ` (`hf`).

In particular, the read of `x._f` promoted to `NonNull W` never fails its promotion check.
-/
public theorem nullCheckThenRead_safe [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF]
    (L : TypeLaws τ) {x : Variable} {p : Property} {U Tx W : τ} (hU : U ≤ Tx) (σ : State)
    (bindings : List (Variable × Loc)) (hb : BindingsOk σ bindings)
    (hx : FactHolds σ bindings (.var x U)) (hf : FactHolds σ bindings (.field x p.name W)) :
    adequate .NotStuck ((nullCheckThenRead x Tx p W).bindVariables bindings) σ
      (fun o _ => OutcomeOk Γ.Null o) :=
  safety (GF := GF) σ bindings (nullCheckThenRead_typed L hU) hb fun f hf' => by
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hf'
    rcases hf' with rfl | rfl
    · exact hx
    · exact hf

/--
The program `{ x as T; x = y; x }`, where `x` has static type `Tx`, `y` has static type `Ty`, and
the last read of `x` has static type `Ty`: the assignment demotes `x` from `T`, the type the cast
promoted it to.
-/
@[expose]
public def castAssignRead (x : Variable) (Tx T : τ) (y : Variable) (Ty : τ) : LoweredExpr :=
  .block [.as (.var x Tx) T, .variableSet x (.var y Ty), .var x Ty]

/--
`{ x as T; x = y; x }` is semantically well typed, with type `Null`, given that `x` is in
scope and holds a value that satisfies `Ux`, and `y` holds a value that satisfies `U`
(`[.var x Ux, .decl x, .var y U]`), if:
- `x` isn't `final` (`hnf`);
- `Ux` is a subtype of `x`'s static type `Tx` (`hUx`); and
- `U` is a subtype of `y`'s static type `Ty` (`hU`).

It guarantees afterwards that `x` holds a value that satisfies `Ty` (`.var x Ty`), but not that it
holds a value that satisfies `T`: the promotion to `T` is forgotten (`Ctx.forget … x`).
-/
public theorem castAssignRead_typed {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]
    [SemanticParams τ] {x y : Variable} {Ux Tx T U Ty : τ} (hnf : x.isFinal = false)
    (hUx : Ux ≤ Tx) (hU : U ≤ Ty) :
    SemTyped GF [.var x Ux, .decl x, .var y U] (castAssignRead x Tx T y Ty) Γ.Null
      (fun _ => .var x Ty :: .decl x ::
        Ctx.forget [.var x T, .var x Ux, .decl x, .var y U] x) := by
  refine SemTyped.block_cons (fun _ _ _ h => by cases h)
    (SemTyped.as_var (List.mem_cons_self ..) hUx) ?_
  refine SemTyped.block_cons (fun _ _ _ h => by cases h)
    (SemTyped.variableSet (by simp) (SemTyped.var (by simp) hU) (by simp [hnf])) ?_
  exact SemTyped.block_cons (fun _ _ _ h => by cases h)
    (SemTyped.var (List.mem_cons_self ..) le_rfl) (SemTyped.block_nil _)

/--
`{ x as T; x = y; x }`, started in state `σ` with its variables bound by `bindings`, never gets
stuck, and every outcome it completes with is consistent with `Null` (`OutcomeOk Γ.Null o`), if:
- `x` isn't `final` (`hnf`);
- `Ux` is a subtype of `x`'s static type `Tx` (`hUx`);
- `U` is a subtype of `y`'s static type `Ty` (`hU`);
- the bindings are suitable (`hb`);
- `x` holds a value that satisfies `Ux` in `σ` (`hx`); and
- `y` holds a value that satisfies `U` in `σ` (`hy`).

In particular, the last read of `x`, demoted to `Ty`, never fails its promotion check.
-/
public theorem castAssignRead_safe [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF]
    {x y : Variable} {Ux Tx T U Ty : τ} (hnf : x.isFinal = false) (hUx : Ux ≤ Tx) (hU : U ≤ Ty)
    (σ : State) (bindings : List (Variable × Loc)) (hb : BindingsOk σ bindings)
    (hx : FactHolds σ bindings (.var x Ux)) (hy : FactHolds σ bindings (.var y U)) :
    adequate .NotStuck ((castAssignRead x Tx T y Ty).bindVariables bindings) σ
      (fun o _ => OutcomeOk Γ.Null o) :=
  safety (GF := GF) σ bindings (castAssignRead_typed (T := T) hnf hUx hU) hb fun f hf => by
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact hx
    · obtain ⟨ℓ, -, -, hl, -⟩ := hx
      exact ⟨ℓ, hl⟩
    · exact hy

/--
The program `{ T z; z = y; z }`, where `z` is declared without an initializer (so it starts out
unassigned), `y` has static type `Ty`, and the read of `z` has static type `Ty`. If `z` is `final`,
this is `{ final T z; z = y; z }`, which assigns `z` exactly once.
-/
@[expose]
public def finalInitRead (z : Variable) (T : τ) (y : Variable) (Ty : τ) : LoweredExpr :=
  .block [.declare z T false, .variableSet z (.var y Ty), .var z Ty]

/--
`{ T z; z = y; z }` is semantically well typed, with type `Null`, given that `y` holds a value that
satisfies `U` (`[.var y U]`), whether or not `z` is `final`, if:
- `y` is a different variable from `z` (`hyz`); and
- `U` is a subtype of `y`'s static type `Ty` (`hU`).

It guarantees nothing afterwards (`[]`).
-/
public theorem finalInitRead_typed {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]
    [SemanticParams τ] {z y : Variable} {T U Ty : τ} (hyz : y ≠ z) (hU : U ≤ Ty) :
    SemTyped GF [.var y U] (finalInitRead z T y Ty) Γ.Null (fun _ => []) := by
  have hrest := SemTyped.block_cons (GF := GF)
    (Δ := (if false = true then [Fact.var z T] else [Fact.uninit z]) ++
      Fact.decl z :: Ctx.forget [.var y U] z)
    (fun _ _ _ h => by cases h)
    (SemTyped.variableSet (v := z)
      (by simp) (SemTyped.var (x := y) (by simp [Ctx.forget, Fact.variable, hyz]) hU)
      (fun _ _ => by simp))
    (SemTyped.block_cons (fun _ _ _ h => by cases h)
      (SemTyped.var (List.mem_cons_self ..) le_rfl) (SemTyped.block_nil _))
  exact (SemTyped.block_declare (fun h => by cases h) hrest).weaken (fun _ h => h) le_rfl
    (fun _ _ h => by cases h)

/--
`{ T z; z = y; z }`, started in state `σ` with its variables bound by `bindings`, never gets stuck,
and every outcome it completes with is consistent with `Null` (`OutcomeOk Γ.Null o`), if:
- `y` is a different variable from `z` (`hyz`);
- `U` is a subtype of `y`'s static type `Ty` (`hU`);
- the bindings are suitable (`hb`); and
- `y` holds a value that satisfies `U` in `σ` (`hy`).

In particular, if `z` is `final`, the assignment to it doesn't get stuck: `z` hasn't been assigned
before.
-/
public theorem finalInitRead_safe [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF]
    {z y : Variable} {T U Ty : τ} (hyz : y ≠ z) (hU : U ≤ Ty) (σ : State)
    (bindings : List (Variable × Loc)) (hb : BindingsOk σ bindings)
    (hy : FactHolds σ bindings (.var y U)) :
    adequate .NotStuck ((finalInitRead z T y Ty).bindVariables bindings) σ
      (fun o _ => OutcomeOk Γ.Null o) :=
  safety (GF := GF) σ bindings (finalInitRead_typed (T := T) hyz hU) hb fun f hf => by
    rw [List.mem_singleton.1 hf]
    exact hy

end DartSemantics
