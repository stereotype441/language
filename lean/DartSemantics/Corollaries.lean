module
public import DartSemantics.Safety

/-!
# Corollaries of safety

Two small programs whose safety depends on promotion, proved safe for every type representation
that obeys `TypeLaws`, and every choice of `SemanticParams`. When
`SemanticParams.promotionChecks` is `PromotionChecks.verify`, "safe" includes that the promoted
read passes its promotion check: the promotion is sound.
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
`{ x as T; x }` is semantically well typed, if `x` holds a value that satisfies `U`, and `U` is a
subtype of `Tx`.
-/
public theorem castThenRead_typed {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]
    [SemanticParams τ] {x : Variable} {U Tx T : τ} (hU : U ≤ Tx) :
    SemTyped GF [.var x U] (castThenRead x Tx T) Γ.Null (fun _ => [.var x T, .var x U]) := by
  refine SemTyped.block_cons (fun _ _ _ h => by cases h)
    (SemTyped.as_var (List.mem_singleton_self _) hU) ?_
  exact SemTyped.block_cons (fun _ _ _ h => by cases h)
    (SemTyped.var (List.mem_cons_self ..) le_rfl) (SemTyped.block_nil _)

/--
`{ x as T; x }` is safe, started in any state where `x` holds a value that satisfies `U`, and `U`
is a subtype of `Tx`: in particular, the read of `x` promoted to `T` never fails its promotion
check.
-/
public theorem castThenRead_safe [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF]
    {x : Variable} {U Tx T : τ} (hU : U ≤ Tx) (σ : State) (bindings : List (Variable × Loc))
    (hσ : FactHolds σ bindings (.var x U)) :
    adequate .NotStuck ((castThenRead x Tx T).bindVariables bindings) σ
      (fun o _ => OutcomeOk Γ.Null o) :=
  safety (GF := GF) σ bindings (castThenRead_typed hU) fun f hf => by
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
`{ x._f!; x._f }` is semantically well typed, if `x` holds a value that satisfies `U`, and `U` is
a subtype of `Tx`, and that value refers to an object with an instance variable named `p.name`,
holding a value that satisfies `W`.
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
`{ x._f!; x._f }` is safe, started in any state where `x` holds a value that satisfies `U`, and
`U` is a subtype of `Tx`, and that value refers to an object with an instance variable named
`p.name`, holding a value that satisfies `W`: in particular, the read of `x._f` promoted to
`NonNull W` never fails its promotion check.
-/
public theorem nullCheckThenRead_safe [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF]
    (L : TypeLaws τ) {x : Variable} {p : Property} {U Tx W : τ} (hU : U ≤ Tx) (σ : State)
    (bindings : List (Variable × Loc)) (hx : FactHolds σ bindings (.var x U))
    (hf : FactHolds σ bindings (.field x p.name W)) :
    adequate .NotStuck ((nullCheckThenRead x Tx p W).bindVariables bindings) σ
      (fun o _ => OutcomeOk Γ.Null o) :=
  safety (GF := GF) σ bindings (nullCheckThenRead_typed L hU) fun f hf' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf'
    rcases hf' with rfl | rfl
    · exact hx
    · exact hf

end DartSemantics
