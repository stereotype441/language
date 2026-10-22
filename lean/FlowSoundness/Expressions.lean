module
public import FlowSoundness.Frame

/-!
# Soundness of expression elaboration

`ElabExpr.semTyped`: in the property-free subset of Dart, the `LoweredExpr` that flow analysis
produces for an expression is semantically well typed with the static type that flow analysis gives
it, from the facts that the flow model before it implies (`ctxOf σ fm₀`), guaranteeing afterwards
the facts that the flow model for its value implies.

The proof has the shape of a logical type soundness proof: one typing rule (compatibility lemma)
per elaboration rule (`ElabExpr.semTyped_var`, `ElabExpr.semTyped_nullCheck`, …), and
`ElabExpr.semTyped` combining them by induction on the elaboration. Keeping the per-rule lemmas
separate means that, when expressions and statements become mutually recursive (for example, for
function expressions with block bodies), only the short inductive proof has to join a `mutual`
block with the statement proofs.

Each typing rule uses the corresponding rule in `DartSemantics.Compat`. A promotion (`x!`,
`x as T`, `x is T`) of a variable uses the rule for the promoting form, which records the promotion
as a fact; the lemmas in `Translation.lean` show that this is exactly what flow analysis records.
-/

namespace FlowSoundness

open DartLang DartSemantics FlowAnalysis Iris

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Value" => Value (τ := τ)
local notation "Fact" => Fact (τ := τ)
local notation "Ctx" => Ctx (τ := τ)
local notation "Scope" => Scope (τ := τ)
local notation "Expr" => Expr (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := AstPath)
local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := AstPath)
local notation "ExprModel" => ExprModel (τ := τ) (ℓ := AstPath)

/-! ### Facts about the variable that a name resolves to -/

omit Γ in
/--
If the facts guaranteed when a condition is `true` and when it's `false` are the same list `Δ`, then
they're `Δ` whatever its value `w` is (`Ctx.byCondition Δ Δ w = Δ`).
-/
public theorem byCondition_self (Δ : Ctx) (w : Value) : Ctx.byCondition Δ Δ w = Δ := by
  unfold Ctx.byCondition
  split <;> rfl

/--
The type of a read of a variable with promotion model `pm` and declared type `b` is the declared
type or one of the types it's promoted to (`pm.currentType b ∈ b :: pm.promotedTypes.val`).
-/
public theorem currentType_mem (pm : PromotionModel) (b : τ) :
    pm.currentType b ∈ b :: pm.promotedTypes.val := by
  unfold PromotionModel.currentType
  split
  · exact List.mem_cons_self ..
  · rename_i T hT
    split
    · exact List.mem_cons_of_mem _ (List.mem_of_getLast? hT)
    · exact List.mem_cons_self ..

/--
The variable `v` that name `n` resolves to in `σ` (`hl`) is in scope (`Fact.decl v ∈ ctxOf σ fm`),
given that `σ` is well formed (`hwf`).
-/
public theorem decl_mem_ctxOf {σ : Scope} {fm : FlowModel} {n : String} {v : Variable}
    {decl : AstPath} (hwf : Scope.WellFormed σ) (hl : σ.lookup n = some (v, decl)) :
    Fact.decl v ∈ ctxOf σ fm :=
  mem_ctxOf_of_lookup hwf hl (by simp [factsOf])

/--
A readable variable holds a value that satisfies its declared type and each type it's promoted to.

If the following conditions hold:
- `σ` is well formed (`hwf`);
- name `n` resolves in `σ` to the variable `v`, declared at `decl` (`hl`);
- `v`'s promotion model in `fm` is `pm` (`hpm`);
- `v` is readable (`hreadable`); and
- `U` is `v`'s declared type or a type it's promoted to (`hU`),

then `v` holds a value that satisfies `U` (`Fact.var v U ∈ ctxOf σ fm`).
-/
public theorem var_mem_ctxOf {σ : Scope} {fm : FlowModel} {n : String} {v : Variable}
    {decl : AstPath} {pm : PromotionModel} {U : τ} (hwf : Scope.WellFormed σ)
    (hl : σ.lookup n = some (v, decl)) (hpm : fm.promotionInfo (.var decl) = some pm)
    (hreadable : pm.Readable v)
    (hU : U ∈ v.type :: pm.promotedTypes.val) : Fact.var v U ∈ ctxOf σ fm := by
  refine mem_ctxOf_of_lookup hwf hl ?_
  simp only [factsOf, hpm, pmFacts]
  refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
  split
  · exact List.mem_map_of_mem hU
  · rcases hreadable with h | h <;> simp_all

/--
A definitely unassigned `final` variable hasn't been assigned.

If the following conditions hold:
- `σ` is well formed (`hwf`);
- name `n` resolves in `σ` to the variable `v`, declared at `decl` (`hl`);
- `v`'s promotion model in `fm` is `pm` (`hpm`);
- `v` is `final` (`hf`); and
- `pm` says `v` is definitely unassigned (`hu`),

then `v` hasn't been assigned (`Fact.uninit v ∈ ctxOf σ fm`).
-/
public theorem uninit_mem_ctxOf {σ : Scope} {fm : FlowModel} {n : String} {v : Variable}
    {decl : AstPath} {pm : PromotionModel} (hwf : Scope.WellFormed σ)
    (hl : σ.lookup n = some (v, decl)) (hpm : fm.promotionInfo (.var decl) = some pm)
    (hf : v.isFinal = true) (hu : pm.unassigned = true) : Fact.uninit v ∈ ctxOf σ fm := by
  refine mem_ctxOf_of_lookup hwf hl ?_
  simp [factsOf, hpm, pmFacts, hf, hu]

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF] [SemanticParams τ]

/--
If `m` guarantees the facts of flow model `fm_true` when it evaluates to `true`, and those of
`fm_false` otherwise (`h`), then it guarantees the facts of their join, whatever its value
(`SemTyped GF Δ m T (fun _ => ctxOf σ (fm_true.join fm_false))`).

This holds because the facts of the join are facts of both flow models.
-/
public theorem SemTyped.toJoin {Δ : Ctx} {m : LoweredExpr} {T : τ} {σ : Scope}
    {fm_true fm_false : FlowModel}
    (h : SemTyped GF Δ m T (Ctx.byCondition (ctxOf σ fm_true) (ctxOf σ fm_false))) :
    SemTyped GF Δ m T (fun _ => ctxOf σ (fm_true.join fm_false)) :=
  h.weaken (fun _ hf => hf) le_rfl fun w f hf => by
    obtain ⟨h₁, h₂⟩ := mem_ctxOf_join hf
    unfold Ctx.byCondition
    split
    · exact h₁
    · exact h₂

/--
An expression that guarantees the facts `Δ'` whatever its value (`h`) also guarantees them when
they're given separately for `true` and `false`, as the same list for both
(`SemTyped GF Δ m T (Ctx.byCondition Δ' Δ')`).
-/
public theorem SemTyped.toByCondition {Δ : Ctx} {m : LoweredExpr} {T : τ} {Δ' : Ctx}
    (h : SemTyped GF Δ m T (fun _ => Δ')) : SemTyped GF Δ m T (Ctx.byCondition Δ' Δ') :=
  h.weaken (fun _ hf => hf) le_rfl fun w f hf => by rwa [byCondition_self] at hf

/-! ### Typing rules for each elaboration rule

Each lemma below is the typing rule (in the terminology of logical type soundness, the
*compatibility lemma*) for one rule of `ElabExpr`: given that the operand, if any, is semantically
well typed as flow analysis says (`ih`), so is the expression. `ElabExpr.semTyped` combines them by
induction on the elaboration.
-/

/--
The typing rule for a read of a variable (`ElabExpr.var`).

If the following conditions hold:
- `σ` is well formed (`hwf`);
- name `n` resolves in `σ` to the variable `v`, declared at `decl` (`hl`);
- `v`'s promotion model in `fm` is `pm` (`hpm`);
- `v` is readable (`hreadable`); and
- `T` is the type `v` is promoted to, if any, and otherwise its declared type (`hT`),

then the read `.var v T` is semantically well typed with type `T`, starting from the facts that `fm`
implies, and guaranteeing afterwards the same facts, whatever its value.
-/
public theorem ElabExpr.semTyped_var {σ : Scope} {fm : FlowModel} {n : String} {v : Variable}
    {decl : AstPath} {pm : PromotionModel} {T : τ} (hwf : Scope.WellFormed σ)
    (hl : σ.lookup n = some (v, decl)) (hpm : fm.promotionInfo (.var decl) = some pm)
    (hreadable : pm.Readable v) (hT : T = pm.currentType v.type) :
    SemTyped GF (ctxOf σ fm) (.var v T) T (Ctx.byCondition (ctxOf σ fm) (ctxOf σ fm)) := by
  subst hT
  exact SemTyped.toByCondition
    (SemTyped.var (var_mem_ctxOf hwf hl hpm hreadable (currentType_mem _ _)) le_rfl)

/--
The typing rule for the null literal (`ElabExpr.nullLiteral`): `.null` is semantically well typed
with type `Null`, starting from the facts that `fm` implies, and guaranteeing afterwards the same
facts, whatever its value.
-/
public theorem ElabExpr.semTyped_nullLiteral {σ : Scope} {fm : FlowModel} :
    SemTyped GF (ctxOf σ fm) .null Γ.Null (Ctx.byCondition (ctxOf σ fm) (ctxOf σ fm)) :=
  SemTyped.toByCondition (SemTyped.null _)

/--
The typing rule for a null check (`e₁!`, `ElabExpr.nullCheck`).

If the following conditions hold:
- the type representation obeys `TypeLaws` (`L`);
- the operand `e₁`, at AST path `0 :: π` and in scope `σ`, elaborates to `m₁` with expression
  model `em₁` starting from flow model `fm₀` (`h₁`);
- `e₁` reads no properties (`hnp`);
- `σ` is well formed (`hwf`);
- `fm` is the flow model after `e₁`, with what `e₁` refers to, if anything, promoted to its
  non-nullable type (`hfm`); and
- `m₁` is semantically well typed with type `em₁.type`, starting from the facts that `fm₀` implies,
  and guaranteeing afterwards those that `em₁.fm_true` or `em₁.fm_false` implies, depending on its
  value (`ih`),

then the null check `m₁.nullCheck` is semantically well typed with type `Γ.NonNull em₁.type`,
starting from the facts that `fm₀` implies, and guaranteeing afterwards the facts that `fm` implies,
whatever its value.
-/
public theorem ElabExpr.semTyped_nullCheck (L : TypeLaws τ) {π : AstPath} {σ : Scope}
    {fm₀ fm : FlowModel} {e₁ : Expr} {m₁ : LoweredExpr} {em₁ : ExprModel}
    (h₁ : ElabExpr (0 :: π) σ fm₀ e₁ m₁ em₁) (hnp : e₁.NoProperties) (hwf : Scope.WellFormed σ)
    (hfm : fm = em₁.fm_after.promoteToNonNull em₁.ref? em₁.type)
    (ih : SemTyped GF (ctxOf σ fm₀) m₁ em₁.type
      (Ctx.byCondition (ctxOf σ em₁.fm_true) (ctxOf σ em₁.fm_false))) :
    SemTyped GF (ctxOf σ fm₀) m₁.nullCheck (Γ.NonNull em₁.type)
      (Ctx.byCondition (ctxOf σ fm) (ctxOf σ fm)) := by
  subst hfm
  refine SemTyped.toByCondition ?_
  cases hr : em₁.ref? with
  | none =>
    have h := SemTyped.nullCheck L (SemTyped.toJoin ih)
    simpa [FlowModel.promoteToNonNull, FlowModel.tryPromote, hr, ExprModel.fm_after] using h
  | some r =>
    obtain ⟨n, v, decl, pm, hl, hpm, hreadable, rfl, rfl, rfl, rfl⟩ :=
      ElabExpr.eq_var_of_ref h₁ hnp hr
    have hpm' : (fm₀.join fm₀).promotionInfo (.var decl) = some (pm.join pm) := by
      simp [FlowModel.join, hpm]
    refine (SemTyped.nullCheck_var L
      (var_mem_ctxOf hwf hl hpm hreadable (currentType_mem _ _)) le_rfl).weaken
      (fun _ hf => hf) le_rfl fun _ f hf => ?_
    simp only [ExprModel.fm_after, FlowModel.promoteToNonNull] at hf
    rcases List.mem_cons.1 (mem_ctxOf_tryPromote hwf hl hpm' hf) with rfl | hf
    · exact .head _
    · exact .tail _ (mem_ctxOf_join hf).1

/--
The typing rule for a cast (`e₁ as T`, `ElabExpr.asExpr`).

If the following conditions hold:
- the operand `e₁`, at AST path `0 :: π` and in scope `σ`, elaborates to `m₁` with expression
  model `em₁` starting from flow model `fm₀` (`h₁`);
- `e₁` reads no properties (`hnp`);
- `σ` is well formed (`hwf`);
- `fm` is the flow model after `e₁`, with what `e₁` refers to, if anything, promoted to `T`
  (`hfm`); and
- `m₁` is semantically well typed with type `em₁.type`, starting from the facts that `fm₀` implies,
  and guaranteeing afterwards those that `em₁.fm_true` or `em₁.fm_false` implies, depending on its
  value (`ih`),

then the cast `m₁.as T` is semantically well typed with type `T`, starting from the facts that
`fm₀` implies, and guaranteeing afterwards the facts that `fm` implies, whatever its value.
-/
public theorem ElabExpr.semTyped_asExpr {π : AstPath} {σ : Scope} {fm₀ fm : FlowModel} {e₁ : Expr}
    {m₁ : LoweredExpr} {em₁ : ExprModel} {T : τ} (h₁ : ElabExpr (0 :: π) σ fm₀ e₁ m₁ em₁)
    (hnp : e₁.NoProperties) (hwf : Scope.WellFormed σ)
    (hfm : fm = em₁.fm_after.tryPromote em₁.ref? em₁.type T)
    (ih : SemTyped GF (ctxOf σ fm₀) m₁ em₁.type
      (Ctx.byCondition (ctxOf σ em₁.fm_true) (ctxOf σ em₁.fm_false))) :
    SemTyped GF (ctxOf σ fm₀) (m₁.as T) T (Ctx.byCondition (ctxOf σ fm) (ctxOf σ fm)) := by
  subst hfm
  refine SemTyped.toByCondition ?_
  cases hr : em₁.ref? with
  | none =>
    have h := SemTyped.as (T := T) (SemTyped.toJoin ih)
    simpa [FlowModel.tryPromote, hr, ExprModel.fm_after] using h
  | some r =>
    obtain ⟨n, v, decl, pm, hl, hpm, hreadable, rfl, rfl, rfl, rfl⟩ :=
      ElabExpr.eq_var_of_ref h₁ hnp hr
    have hpm' : (fm₀.join fm₀).promotionInfo (.var decl) = some (pm.join pm) := by
      simp [FlowModel.join, hpm]
    refine (SemTyped.as_var (T := T)
      (var_mem_ctxOf hwf hl hpm hreadable (currentType_mem _ _)) le_rfl).weaken
      (fun _ hf => hf) le_rfl fun _ f hf => ?_
    simp only [ExprModel.fm_after] at hf
    rcases List.mem_cons.1 (mem_ctxOf_tryPromote hwf hl hpm' hf) with rfl | hf
    · exact .head _
    · exact .tail _ (mem_ctxOf_join hf).1

/--
The typing rule for a type test (`e₁ is T`, `ElabExpr.isExpr`).

If the following conditions hold:
- the operand `e₁`, at AST path `0 :: π` and in scope `σ`, elaborates to `m₁` with expression
  model `em₁` starting from flow model `fm₀` (`h₁`);
- `e₁` reads no properties (`hnp`);
- `σ` is well formed (`hwf`);
- `fm_true` is the flow model after `e₁`, with what `e₁` refers to, if anything, promoted to `T`
  (`hfm`); and
- `m₁` is semantically well typed with type `em₁.type`, starting from the facts that `fm₀` implies,
  and guaranteeing afterwards those that `em₁.fm_true` or `em₁.fm_false` implies, depending on its
  value (`ih`),

then the type test `m₁.is T` is semantically well typed with type `bool`, starting from the facts
that `fm₀` implies, and guaranteeing afterwards:
- if it evaluates to `true`, the facts that `fm_true` implies; and
- otherwise, the facts that the flow model after `e₁` implies (`em₁.fm_after`).
-/
public theorem ElabExpr.semTyped_isExpr {π : AstPath} {σ : Scope} {fm₀ fm_true : FlowModel}
    {e₁ : Expr} {m₁ : LoweredExpr} {em₁ : ExprModel} {T : τ}
    (h₁ : ElabExpr (0 :: π) σ fm₀ e₁ m₁ em₁) (hnp : e₁.NoProperties) (hwf : Scope.WellFormed σ)
    (hfm : fm_true = em₁.fm_after.tryPromote em₁.ref? em₁.type T)
    (ih : SemTyped GF (ctxOf σ fm₀) m₁ em₁.type
      (Ctx.byCondition (ctxOf σ em₁.fm_true) (ctxOf σ em₁.fm_false))) :
    SemTyped GF (ctxOf σ fm₀) (m₁.is T) Γ.bool
      (Ctx.byCondition (ctxOf σ fm_true) (ctxOf σ em₁.fm_after)) := by
  subst hfm
  cases hr : em₁.ref? with
  | none =>
    have h := SemTyped.toByCondition (SemTyped.is (T := T) (SemTyped.toJoin ih))
    simpa [FlowModel.tryPromote, hr, ExprModel.fm_after] using h
  | some r =>
    obtain ⟨n, v, decl, pm, hl, hpm, hreadable, rfl, rfl, rfl, rfl⟩ :=
      ElabExpr.eq_var_of_ref h₁ hnp hr
    have hpm' : (fm₀.join fm₀).promotionInfo (.var decl) = some (pm.join pm) := by
      simp [FlowModel.join, hpm]
    refine (SemTyped.is_var (T := T)
      (var_mem_ctxOf hwf hl hpm hreadable (currentType_mem _ _)) le_rfl).weaken
      (fun _ hf => hf) le_rfl fun w f hf => ?_
    simp only [ExprModel.fm_after] at hf
    unfold Ctx.byCondition at hf ⊢
    split
    · rcases List.mem_cons.1 (mem_ctxOf_tryPromote hwf hl hpm' hf) with rfl | hf
      · exact .head _
      · exact .tail _ (mem_ctxOf_join hf).1
    · next hne =>
      split at hf
      · exact absurd rfl hne
      · exact (mem_ctxOf_join hf).1

/--
The typing rule for an assignment to a variable (`n = e₁`, `ElabExpr.assign`).

If the following conditions hold:
- `σ` is well formed (`hwf`);
- name `n` resolves in `σ` to the variable `v`, declared at `decl` (`hl`);
- `v`'s promotion model in the flow model after `e₁` is `pm` (`hpm`);
- the static type of `e₁` is a subtype of `v`'s declared type (`hT`);
- if `v` is `final`, `pm` says it's definitely unassigned (`hfin`);
- `fm` is the flow model after `e₁`, with `v`'s promotion model updated for the write (`hfm`); and
- `m₁` is semantically well typed with type `em₁.type`, starting from the facts that `fm₀` implies,
  and guaranteeing afterwards those that `em₁.fm_true` or `em₁.fm_false` implies, depending on its
  value (`ih`),

then the assignment `.variableSet v m₁` is semantically well typed with type `em₁.type`, starting
from the facts that `fm₀` implies, and guaranteeing afterwards the facts that `fm` implies, whatever
its value.
-/
public theorem ElabExpr.semTyped_assign {π : AstPath} {σ : Scope} {fm₀ fm : FlowModel} {n : String}
    {m₁ : LoweredExpr} {em₁ : ExprModel} {v : Variable} {decl : AstPath} {pm : PromotionModel}
    (hwf : Scope.WellFormed σ) (hl : σ.lookup n = some (v, decl))
    (hpm : em₁.fm_after.promotionInfo (.var decl) = some pm) (hT : em₁.type ≤ v.type)
    (hfin : v.isFinal = true → pm.unassigned = true)
    (hfm : fm = em₁.fm_after.set (.var decl) (pm.write em₁.type (ValueVersion.root π)))
    (ih : SemTyped GF (ctxOf σ fm₀) m₁ em₁.type
      (Ctx.byCondition (ctxOf σ em₁.fm_true) (ctxOf σ em₁.fm_false))) :
    SemTyped GF (ctxOf σ fm₀) (.variableSet v m₁) em₁.type
      (Ctx.byCondition (ctxOf σ fm) (ctxOf σ fm)) := by
  subst hfm
  refine SemTyped.toByCondition ?_
  have h := SemTyped.toJoin ih
  refine (SemTyped.variableSet (decl_mem_ctxOf hwf hl) h fun hf _ =>
    uninit_mem_ctxOf hwf hl hpm hf (hfin hf)).weaken' (fun f hf => ⟨f, hf, .refl _⟩) le_rfl
    fun _ f hf => implies_ctxOf_write hwf hl hT hf

/-! ### The soundness of expression elaboration -/

/--
**Soundness of expression elaboration**, for expressions that read no properties.

If the following conditions hold:
- the type representation obeys `TypeLaws` (`L`), which the typing rules for null checks and
  conditionals need;
- the expression `e`, at AST path `π` and in scope `σ`, elaborates to `m` with expression model `em`
  starting from flow model `fm₀` (`helab`);
- `e` reads no properties (`hnp`); and
- `σ` is well formed (`hwf`),

then `m` is semantically well typed:
- with the static type that flow analysis gives it (`em.type`);
- starting from the facts that `fm₀` implies (`ctxOf σ fm₀`); and
- guaranteeing afterwards the facts that the flow model for its value implies:
  - if it evaluates to `true`, the facts that `em.fm_true` implies (`ctxOf σ em.fm_true`); and
  - otherwise, the facts that `em.fm_false` implies (`ctxOf σ em.fm_false`).

The proof is by induction on the elaboration, applying the typing rule for each elaboration rule.
-/
public theorem ElabExpr.semTyped (L : TypeLaws τ) {π : AstPath} {σ : Scope} {fm₀ : FlowModel}
    {e : Expr} {m : LoweredExpr} {em : ExprModel} (helab : ElabExpr π σ fm₀ e m em)
    (hnp : e.NoProperties) (hwf : Scope.WellFormed σ) :
    SemTyped GF (ctxOf σ fm₀) m em.type
      (Ctx.byCondition (ctxOf σ em.fm_true) (ctxOf σ em.fm_false)) :=
  match helab, hnp, hwf with
  | .var hl hpm hreadable hT, _, hwf => ElabExpr.semTyped_var hwf hl hpm hreadable hT
  | .nullLiteral, _, _ => ElabExpr.semTyped_nullLiteral
  | .propertyGet .., hnp, _ => hnp.elim
  | .nullCheck h₁ hfm, hnp, hwf =>
    ElabExpr.semTyped_nullCheck L h₁ hnp hwf hfm (ElabExpr.semTyped L h₁ hnp hwf)
  | .asExpr h₁ hfm, hnp, hwf =>
    ElabExpr.semTyped_asExpr h₁ hnp hwf hfm (ElabExpr.semTyped L h₁ hnp hwf)
  | .isExpr h₁ hfm, hnp, hwf =>
    ElabExpr.semTyped_isExpr h₁ hnp hwf hfm (ElabExpr.semTyped L h₁ hnp hwf)
  | .assign (em₁ := em₁) h₁ hl hpm hT hfin hfm, hnp, hwf =>
    ElabExpr.semTyped_assign (em₁ := em₁) hwf hl hpm hT hfin hfm (ElabExpr.semTyped L h₁ hnp hwf)

end FlowSoundness
