module
public import FlowSoundness.Expressions

/-!
# Soundness of statement elaboration

`ElabStmt.semTyped`: in the property-free subset of Dart, the `LoweredExpr` that flow analysis
produces for a statement is semantically well typed, from the facts that the flow model before it
implies (`ctxOf σ fm₀`), guaranteeing afterwards the facts that the flow model after it implies
(`ctxOf σ fm₁`). `ElabStmts.semTyped` is the same for a list of statements, lowered to a block.

A declaration is the interesting case. Inside the rest of its block, `ctxOf` describes the new
variable, and forgets any outer declaration of the same `Variable` that it shadows. At the end of
the block, `SemTyped.block_declare` gives back the facts about the outer declaration that held
before the block; `ElabStmts.frame` shows that these are all that flow analysis knows about it
afterwards, since no name in the block resolves to it.
-/

namespace FlowSoundness

open DartLang DartSemantics FlowAnalysis Iris

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Fact" => Fact (τ := τ)
local notation "Ctx" => Ctx (τ := τ)
local notation "Scope" => Scope (τ := τ)
local notation "Stmt" => Stmt (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := AstPath)

/-! ### Scopes -/

omit Γ in
/--
No declaration in a scope `σ` that is well formed at `π` (`hwf`) is at `π` itself
(`π ∉ σ.map (·.2.2)`).
-/
public theorem Scope.WellFormedAt.not_mem {π : AstPath} {σ : Scope} (hwf : Scope.WellFormedAt π σ) :
    π ∉ σ.map (·.2.2) := fun hm => by
  obtain ⟨e, he, heq⟩ := List.mem_map.1 hm
  exact hwf.fresh e he (heq ▸ List.suffix_refl π)

omit Γ in
/--
A scope `σ` that is well formed at a node (`hwf`) is well formed at each child
(`Scope.WellFormedAt (i :: π) σ`).
-/
public theorem Scope.WellFormedAt.sub {π : AstPath} {σ : Scope} (hwf : Scope.WellFormedAt π σ)
    (i : Nat) : Scope.WellFormedAt (i :: π) σ :=
  ⟨hwf.toWellFormed, fun e he h => hwf.fresh e he ((List.suffix_cons _ _).trans h)⟩

omit Γ in
/--
In a list of statements at `π`, whose scope `σ` is well formed at `π` (`hwf`), the scope of the
statements after the first, `s`, (`s.extendScope σ (0 :: π)`) is well formed at their path
`1 :: π` (`Scope.WellFormedAt (1 :: π) (s.extendScope σ (0 :: π))`): a declaration that `s` adds is
at `0 :: π`, outside their subtree, and isn't already in `σ`.
-/
public theorem Scope.WellFormedAt.extendScope {π : AstPath} {σ : Scope}
    (hwf : Scope.WellFormedAt π σ) (s : Stmt) :
    Scope.WellFormedAt (1 :: π) (s.extendScope σ (0 :: π)) := by
  cases s with
  | declare n T isFinal =>
    refine ⟨⟨?_, fun e he => ?_⟩, fun e he => ?_⟩
    · simp only [Stmt.extendScope, List.map_cons, List.nodup_cons]
      exact ⟨(hwf.sub 0).not_mem, hwf.nodup⟩
    · rcases List.mem_cons.1 he with rfl | he
      · rfl
      · exact hwf.names e he
    · rcases List.mem_cons.1 he with rfl | he
      · intro h
        simpa using h.eq_of_length (by simp)
      · exact (hwf.sub 1).fresh e he
  | _ => exact hwf.sub 1

/-! ### Lowered statements -/

/-- The lowering of an expression is never a declaration. -/
public theorem ElabExpr.ne_declare {π : AstPath} {σ : Scope} {fm : FlowModel} {e : Expr (τ := τ)}
    {m : LoweredExpr} {em : ExprModel (τ := τ) (ℓ := AstPath)} (h : ElabExpr π σ fm e m em) :
    ∀ v T sN, m ≠ .declare v T sN := by
  intro v T sN heq
  cases h <;> cases heq

/--
A variable `v` starts out holding the null object (`h`) only if `Null` is a subtype of its type
(`Γ.Null ≤ v.type`).
-/
public theorem startsNull_le {v : Variable} (h : v.startsNull = true) : Γ.Null ≤ v.type := by
  simp_all

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF] [SemanticParams τ]

/--
A block that only declares `v` is semantically well typed with type `Null`, if `hsN` (as for
`SemTyped.declare`). It guarantees afterwards all the facts that held beforehand (`Δ`).
-/
public theorem SemTyped.block_declare_nil {Δ : Ctx} {v : Variable} {T : τ} {sN : Bool}
    (hsN : sN = true → Γ.Null ≤ T) :
    SemTyped GF Δ (.block [.declare v T sN]) Γ.Null (fun _ => Δ) :=
  (SemTyped.block_declare hsN (SemTyped.block_nil _)).weaken (fun _ hf => hf) le_rfl
    fun _ f hf => by
      by_cases hfv : f.variable = v
      · exact List.mem_append_right _ (List.mem_filter.2 ⟨hf, by simpa using hfv⟩)
      · refine List.mem_append_left _ (Ctx.mem_forget.2 ⟨?_, hfv⟩)
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (Ctx.mem_forget.2 ⟨hf, hfv⟩))

/--
The block (`.block [m]`) that holds just the lowering `m` of a statement (`h`), which is
semantically well typed (`hraw`), is semantically well typed with type `Null`, with the same facts
beforehand and afterwards, given that `σ` is well formed at `π` (`hwf`). (A declaration's facts
afterwards are the ones beforehand, since `ctxOf σ` doesn't describe it.)
-/
public theorem ElabStmt.semTyped_block {π : AstPath} {σ : Scope} {fm₀ fm₁ : FlowModel} {s : Stmt}
    {m : LoweredExpr} (h : ElabStmt π σ fm₀ s m fm₁) (hwf : Scope.WellFormedAt π σ)
    (hraw : ∃ T, SemTyped GF (ctxOf σ fm₀) m T (fun _ => ctxOf σ fm₁)) :
    SemTyped GF (ctxOf σ fm₀) (.block [m]) Γ.Null (fun _ => ctxOf σ fm₁) := by
  cases h with
  | declare =>
    rw [ctxOf_set_of_not_mem hwf.not_mem]
    exact SemTyped.block_declare_nil startsNull_le
  | exprStmt h₁ =>
    obtain ⟨T, hT⟩ := hraw
    exact SemTyped.block_cons (ElabExpr.ne_declare h₁) hT (SemTyped.block_nil _)
  | ifStmt =>
    obtain ⟨T, hT⟩ := hraw
    exact SemTyped.block_cons (by intro _ _ _ h; cases h) hT (SemTyped.block_nil _)
  | block =>
    obtain ⟨T, hT⟩ := hraw
    exact SemTyped.block_cons (by intro _ _ _ h; cases h) hT (SemTyped.block_nil _)

/--
A list of statements `s :: ss` (`h`, `hs`) in the property-free subset of Dart (`hnp`), whose
scope `σ` is well formed at `π` (`hwf`), lowers to a semantically well typed block, if the lowering
of `s` is semantically well typed (`hraw`), and so is the lowering of `ss`, in the scope that `s`
extends (`hrest`).

If `s` declares a variable `v`, the facts about any outer `v` that it shadows are restored at the
end of the block (`SemTyped.block_declare`), and these are all that flow analysis knows about it
afterwards (`ElabStmts.frame`).
-/
public theorem ElabStmts.semTyped_cons {π : AstPath} {σ : Scope} {fm₀ fm₁ fm : FlowModel}
    {s : Stmt} {ss : List Stmt} {m : LoweredExpr} {ms : List LoweredExpr}
    (h : ElabStmt (0 :: π) σ fm₀ s m fm₁)
    (hs : ElabStmts (1 :: π) (s.extendScope σ (0 :: π)) fm₁ ss ms fm)
    (hnp : Stmt.NoPropertiesList ss) (hwf : Scope.WellFormedAt π σ)
    (hraw : ∃ T, SemTyped GF (ctxOf σ fm₀) m T (fun _ => ctxOf σ fm₁))
    (hrest : SemTyped GF (ctxOf (s.extendScope σ (0 :: π)) fm₁) (.block ms) Γ.Null
      (fun _ => ctxOf (s.extendScope σ (0 :: π)) fm)) :
    SemTyped GF (ctxOf σ fm₀) (.block (m :: ms)) Γ.Null (fun _ => ctxOf σ fm) := by
  cases h with
  | declare _ _ _ n T isFinal =>
    have hne : ∀ e ∈ σ, 0 :: π ≠ e.2.2 := fun e he heq =>
      (hwf.sub 0).not_mem (List.mem_map.2 ⟨e, he, heq.symm⟩)
    refine (SemTyped.block_declare (startsNull_le (v := ⟨n, T, isFinal⟩))
      (hrest.weaken (fun f hf => ?_) le_rfl fun _ _ hf => hf)).weaken (fun _ hf => hf) le_rfl
      fun _ f hf => ?_
    · -- The facts at the start of the rest of the block are among those the rule provides.
      simp only [Stmt.extendScope, ctxOf, List.mem_append] at hf
      rcases hf with hf | hf
      · clear hrest hs hraw
        revert hf
        cases isFinal <;> by_cases hN : Γ.Null ≤ T <;>
          simp +contextual [factsOf, pmFacts, FlowModel.set, PromotionModel.declared,
            PromotionModel.Readable, hN] <;>
          tauto
      · rw [ctxOf_set_of_not_mem (hwf.sub 0).not_mem] at hf
        exact List.mem_append_right _ (List.mem_cons_of_mem _ hf)
    · -- The facts at the end of the block are among those the rule guarantees.
      by_cases hfv : f.variable = ⟨n, T, isFinal⟩
      · refine List.mem_append_right _ (List.mem_filter.2 ⟨?_, by simpa using hfv⟩)
        refine mem_ctxOf_of_factsSub (fun e he hev => ?_) hf hfv
        refine (ElabStmts.frame hs hnp ?_ fun h => hwf.fresh e he
          ((List.suffix_cons _ _).trans h)).trans (FactsSub.set_ne (hne e he))
        rintro ⟨n', v', hl⟩
        simp only [Stmt.extendScope, List.lookup] at hl
        split at hl
        · simp only [Option.some.injEq, Prod.mk.injEq] at hl
          exact hne e he hl.2
        · rename_i hn'
          have heq := List.inj_on_of_nodup_map hwf.nodup (mem_of_lookup hl) he rfl
          have h₁ : e.1 = n := (hwf.names e he).symm.trans (by rw [hev])
          have h₂ : n' = n := by rw [← h₁, ← heq]
          simp [h₂] at hn'
      · refine List.mem_append_left _ (Ctx.mem_forget.2 ⟨?_, hfv⟩)
        simp only [Stmt.extendScope, ctxOf]
        exact List.mem_append_right _ (Ctx.mem_forget.2 ⟨hf, hfv⟩)
  | exprStmt h₁ =>
    obtain ⟨T, hT⟩ := hraw
    exact SemTyped.block_cons (ElabExpr.ne_declare h₁) hT hrest
  | ifStmt =>
    obtain ⟨T, hT⟩ := hraw
    exact SemTyped.block_cons (by intro _ _ _ h; cases h) hT hrest
  | block =>
    obtain ⟨T, hT⟩ := hraw
    exact SemTyped.block_cons (by intro _ _ _ h; cases h) hT hrest

/-! ### The soundness of statement elaboration -/

mutual

/--
**Soundness of statement elaboration**, for statements that read no properties. If the statement
`s`, at AST path `π` and in scope `σ`, elaborates to `m`, taking flow model `fm₀` to `fm₁`
(`helab`), then `m` is semantically well typed with some type `T`, from the facts that `fm₀` implies
(`ctxOf σ fm₀`), guaranteeing afterwards the facts that `fm₁` implies (`ctxOf σ fm₁`). This holds
if:
- the type representation obeys `TypeLaws` (`L`), which the typing rules for null checks and
  conditionals need;
- `s` reads no properties (`hnp`); and
- `σ` is well formed at `π` (`hwf`).
-/
public theorem ElabStmt.semTyped (L : TypeLaws τ) {π : AstPath} {σ : Scope}
    {fm₀ : FlowModel} {s : Stmt} {m : LoweredExpr} {fm₁ : FlowModel}
    (helab : ElabStmt π σ fm₀ s m fm₁) (hnp : s.NoProperties) (hwf : Scope.WellFormedAt π σ) :
    ∃ T, SemTyped GF (ctxOf σ fm₀) m T (fun _ => ctxOf σ fm₁) :=
  match helab, hnp, hwf with
  | .declare .., _, hwf => ⟨_, by
      rw [ctxOf_set_of_not_mem hwf.not_mem]
      exact SemTyped.declare startsNull_le⟩
  | .exprStmt h, hnp, hwf => ⟨_, by
      simpa only [ExprModel.fm_after] using
        SemTyped.toJoin (ElabExpr.semTyped L h hnp hwf.toWellFormed)⟩
  | .ifStmt h₁ hb h₂ h₃, hnp, hwf => by
    have hc := ElabExpr.semTyped (GF := GF) L h₁ hnp.1 hwf.toWellFormed
    rw [hb] at hc
    have hb₂ := ElabStmt.semTyped_block (GF := GF) h₂ (hwf.sub 1)
      (ElabStmt.semTyped L h₂ hnp.2.1 (hwf.sub 1))
    have hb₃ := ElabStmt.semTyped_block (GF := GF) h₃ (hwf.sub 2)
      (ElabStmt.semTyped L h₃ hnp.2.2 (hwf.sub 2))
    exact ⟨_, SemTyped.cond L hc
      (hb₂.weaken (fun _ hf => hf) le_rfl fun _ _ hf => (mem_ctxOf_join hf).1)
      (hb₃.weaken (fun _ hf => hf) le_rfl fun _ _ hf => (mem_ctxOf_join hf).2)⟩
  | .block h, hnp, hwf => ⟨_, ElabStmts.semTyped L h hnp (hwf.sub 0)⟩

/--
**Soundness of statement list elaboration**, for statements that read no properties. If the list
of statements `ss`, at AST path `π` and in scope `σ`, elaborates to `ms`, taking flow model `fm₀` to
`fm₁` (`helab`), then the block `.block ms` is semantically well typed with type `Null`, from the
facts that `fm₀` implies (`ctxOf σ fm₀`), guaranteeing afterwards the facts that `fm₁` implies
(`ctxOf σ fm₁`). This holds if:
- the type representation obeys `TypeLaws` (`L`);
- the statements read no properties (`hnp`); and
- `σ` is well formed at `π` (`hwf`).
-/
public theorem ElabStmts.semTyped (L : TypeLaws τ) {π : AstPath} {σ : Scope}
    {fm₀ : FlowModel} {ss : List Stmt} {ms : List LoweredExpr} {fm₁ : FlowModel}
    (helab : ElabStmts π σ fm₀ ss ms fm₁) (hnp : Stmt.NoPropertiesList ss)
    (hwf : Scope.WellFormedAt π σ) :
    SemTyped GF (ctxOf σ fm₀) (.block ms) Γ.Null (fun _ => ctxOf σ fm₁) :=
  match helab, hnp, hwf with
  | .nil, _, _ => SemTyped.block_nil _
  | .cons h hs, hnp, hwf =>
    ElabStmts.semTyped_cons h hs hnp.2 hwf (ElabStmt.semTyped L h hnp.1 (hwf.sub 0))
      (ElabStmts.semTyped L hs hnp.2 (hwf.extendScope _))

end

end FlowSoundness
