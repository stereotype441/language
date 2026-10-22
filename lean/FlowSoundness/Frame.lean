module
public import FlowSoundness.Translation

/-!
# What elaboration leaves alone

Elaboration only updates the promotion models of declarations that some name in scope resolves to
(by promoting or assigning a variable), or that lie in the subtree being elaborated (a declaration's
own promotion model). This file proves the corresponding *frame* property: for any other
declaration, the facts that the flow model implies after elaboration were implied before.

The soundness proof needs this at the end of a block that declares a variable shadowing an outer
declaration of the same `Variable`. Inside the block, no name resolves to the outer declaration, so
the facts about it that held before the block still hold after it (see
`DartSemantics.SemTyped.block_declare`).
-/

namespace FlowSoundness

open DartLang DartSemantics FlowAnalysis

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Fact" => Fact (τ := τ)
local notation "Scope" => Scope (τ := τ)
local notation "Expr" => Expr (τ := τ)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := AstPath)
local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := AstPath)
local notation "Reference" => Reference (ℓ := AstPath)

/-- Some name resolves to the declaration at `decl` in scope `σ`. -/
@[expose]
public def Resolves (σ : Scope) (decl : AstPath) : Prop :=
  ∃ n v, σ.lookup n = some (v, decl)

/--
`FactsSub decl fm₁ fm₀`: every fact that `fm₁` implies about the variable declared at `decl` is
implied by `fm₀` too, whichever `Variable` that is.
-/
@[expose]
public def FactsSub (decl : AstPath) (fm₁ fm₀ : FlowModel) : Prop :=
  ∀ (v : Variable) f, f ∈ factsOf v decl fm₁ → f ∈ factsOf v decl fm₀

/-- `FactsSub` is reflexive. -/
public theorem FactsSub.refl (decl : AstPath) (fm : FlowModel) : FactsSub decl fm fm :=
  fun _ _ h => h

/--
`FactsSub` is transitive: if `fm₂` implies no more than `fm₁` about `decl` (`h₂`), and `fm₁` no
more than `fm₀` (`h₁`), then `fm₂` implies no more than `fm₀` (`FactsSub decl fm₂ fm₀`).
-/
public theorem FactsSub.trans {decl : AstPath} {fm₂ fm₁ fm₀ : FlowModel}
    (h₂ : FactsSub decl fm₂ fm₁) (h₁ : FactsSub decl fm₁ fm₀) : FactsSub decl fm₂ fm₀ :=
  fun v f h => h₁ v f (h₂ v f h)

/--
Updating the promotion model of a declaration other than `decl` (`hne`) implies no more about the
variable declared at `decl` than before (`FactsSub decl (fm.set (.var decl') pm) fm`).
-/
public theorem FactsSub.set_ne {decl decl' : AstPath} {fm : FlowModel} {pm : PromotionModel}
    (hne : decl' ≠ decl) : FactsSub decl (fm.set (.var decl') pm) fm := by
  intro v f h
  simpa [factsOf, FlowModel.set, hne] using h

/--
If the join of two flow models implies a fact about the variable `v` declared at `decl` (`h`), then
each flow model individually implies that fact (`f ∈ factsOf v decl fm₁` and
`f ∈ factsOf v decl fm₂`).
-/
public theorem mem_factsOf_join {v : Variable} {decl : AstPath} {fm₁ fm₂ : FlowModel} {f : Fact}
    (h : f ∈ factsOf v decl (fm₁.join fm₂)) : f ∈ factsOf v decl fm₁ ∧ f ∈ factsOf v decl fm₂ := by
  simp only [factsOf, List.mem_cons] at h ⊢
  rcases h with rfl | h
  · exact ⟨.inl rfl, .inl rfl⟩
  · simp only [FlowModel.join] at h
    split at h
    · simp at h
    · rename_i pm hpm
      split at hpm
      · simp at hpm
      · rename_i pm₁ hpm₁
        split at hpm
        · simp at hpm
        · rename_i pm₂ hpm₂
          cases hpm
          obtain ⟨h₁, h₂⟩ := mem_pmFacts_join h
          exact ⟨.inr (by rw [hpm₁]; exact h₁), .inr (by rw [hpm₂]; exact h₂)⟩

/--
The join of two flow models implies no more about a declaration than its left side does
(`FactsSub decl (fm₁.join fm₂) fm₁`).
-/
public theorem FactsSub.join_left (decl : AstPath) (fm₁ fm₂ : FlowModel) :
    FactsSub decl (fm₁.join fm₂) fm₁ :=
  fun _ _ h => (mem_factsOf_join h).1

/--
The join of two flow models implies no more about a declaration than its right side does
(`FactsSub decl (fm₁.join fm₂) fm₂`).
-/
public theorem FactsSub.join_right (decl : AstPath) (fm₁ fm₂ : FlowModel) :
    FactsSub decl (fm₁.join fm₂) fm₂ :=
  fun _ _ h => (mem_factsOf_join h).2

/--
Promoting the variable declared at `decl'`, a declaration other than `decl` (`hne`), implies no
more about the variable declared at `decl` than before
(`FactsSub decl (fm.tryPromote (some (.var decl' version?)) previousType T) fm`).
-/
public theorem FactsSub.tryPromote {decl decl' : AstPath} {fm : FlowModel}
    {version? : Option (ValueVersion (ℓ := AstPath))} {previousType T : τ} (hne : decl' ≠ decl) :
    FactsSub decl (fm.tryPromote (some (.var decl' version?)) previousType T) fm := by
  simp only [FlowModel.tryPromote]
  split
  · split
    · exact FactsSub.set_ne hne
    · exact FactsSub.refl _ _
  · exact FactsSub.refl _ _

/--
In the property-free subset of Dart, an expression that refers to a location is a read of a
variable.

If the following conditions hold:
- the expression `e`, at AST path `π` and in scope `σ`, elaborates to `m` with expression model `em`
  starting from flow model `fm₀` (`helab`);
- `e` reads no properties (`hnp`); and
- `e` refers to a location `r` (`hr`),

then there are a name `n`, a variable `v`, a declaration `decl` and a promotion model `pm` such
that:
- `n` resolves to `v`, declared at `decl` (`σ.lookup n = some (v, decl)`);
- `v`'s promotion model before the read is `pm` (`fm₀.promotionInfo (.var decl) = some pm`);
- `v` is readable (`pm.Readable v`);
- the location that `e` refers to is `v`'s declaration, with the value version that `pm` records
  (`r = .var decl pm.version?`);
- `e` is the read of `n` (`e = .var n`);
- `e` lowers to a read of `v` whose static type is the type `v` is promoted to, if any, and
  otherwise its declared type (`m = .var v (pm.currentType v.type)`); and
- `e`'s expression model has that type, refers to `r`, and leaves the flow model unchanged, whether
  `e` is `true` or `false` (`em = ⟨pm.currentType v.type, some r, fm₀, fm₀⟩`).
-/
public theorem ElabExpr.eq_var_of_ref {π : AstPath} {σ : Scope} {fm₀ : FlowModel} {e : Expr}
    {m : LoweredExpr (τ := τ)} {em : ExprModel (τ := τ) (ℓ := AstPath)} {r : Reference}
    (helab : ElabExpr π σ fm₀ e m em) (hnp : e.NoProperties) (hr : em.ref? = some r) :
    ∃ n v decl pm, σ.lookup n = some (v, decl) ∧ fm₀.promotionInfo (.var decl) = some pm ∧
      pm.Readable v ∧
      r = .var decl pm.version? ∧ e = .var n ∧ m = .var v (pm.currentType v.type) ∧
      em = ⟨pm.currentType v.type, some r, fm₀, fm₀⟩ := by
  cases helab
  case var n v decl pm T hreadable hT hl hpm =>
    subst hT
    simp only [Option.some.injEq] at hr
    subst hr
    exact ⟨n, v, decl, pm, hl, hpm, hreadable, rfl, rfl, rfl, rfl⟩
  case propertyGet => exact hnp.elim
  all_goals simp at hr

/--
Elaborating an expression leaves alone the facts about a declaration that no name resolves to.

If the following conditions hold:
- the expression `e`, at AST path `π` and in scope `σ`, elaborates to `m` with expression model `em`
  starting from flow model `fm₀` (`helab`);
- `e` reads no properties (`hnp`); and
- no name resolves to `decl` in `σ` (`hd`),

then the flow model afterwards implies no more about the declaration at `decl` than `fm₀` did:
- when `e` is `true` (`FactsSub decl em.fm_true fm₀`); and
- when `e` is `false` (`FactsSub decl em.fm_false fm₀`).
-/
public theorem ElabExpr.frame {decl : AstPath} {π : AstPath} {σ : Scope} {fm₀ : FlowModel}
    {e : Expr} {m : LoweredExpr (τ := τ)} {em : ExprModel (τ := τ) (ℓ := AstPath)}
    (helab : ElabExpr π σ fm₀ e m em) (hnp : e.NoProperties) (hd : ¬Resolves σ decl) :
    FactsSub decl em.fm_true fm₀ ∧ FactsSub decl em.fm_false fm₀ :=
  match helab, hnp, hd with
  | .var .., _, _ => ⟨FactsSub.refl _ _, FactsSub.refl _ _⟩
  | .nullLiteral, _, _ => ⟨FactsSub.refl _ _, FactsSub.refl _ _⟩
  | .propertyGet .., hnp, _ => hnp.elim
  | .nullCheck (em₁ := em₁) h₁ hfm, hnp, hd => by
    subst hfm
    have hafter := (FactsSub.join_left decl em₁.fm_true em₁.fm_false).trans
      (ElabExpr.frame h₁ hnp hd).1
    have h := tryPromote_frame h₁ hnp hd hafter (Γ.NonNull em₁.type)
    exact ⟨h, h⟩
  | .asExpr (em₁ := em₁) (T := T) h₁ hfm, hnp, hd => by
    subst hfm
    have hafter := (FactsSub.join_left decl em₁.fm_true em₁.fm_false).trans
      (ElabExpr.frame h₁ hnp hd).1
    have h := tryPromote_frame h₁ hnp hd hafter T
    exact ⟨h, h⟩
  | .isExpr (em₁ := em₁) (T := T) h₁ hfm, hnp, hd => by
    subst hfm
    have hafter := (FactsSub.join_left decl em₁.fm_true em₁.fm_false).trans
      (ElabExpr.frame h₁ hnp hd).1
    exact ⟨tryPromote_frame h₁ hnp hd hafter T, hafter⟩
  | .assign (em₁ := em₁) (decl := decl') h₁ hl _ _ _ hfm, hnp, hd => by
    subst hfm
    have hafter := (FactsSub.join_left decl em₁.fm_true em₁.fm_false).trans
      (ElabExpr.frame h₁ hnp hd).1
    have hne : decl' ≠ decl := by
      rintro rfl
      exact hd ⟨_, _, hl⟩
    refine ⟨?_, ?_⟩ <;> exact (FactsSub.set_ne hne).trans hafter
where
  /--
  Promoting the location (if any) that the operand of a promotion refers to keeps the flow model
  implying no more about `decl` than `fm₀` does.

  If the following conditions hold:
  - the operand `e`, at AST path `π` and in scope `σ`, elaborates to `m` with expression model `em`
    starting from flow model `fm₀` (`helab`);
  - `e` reads no properties (`hnp`);
  - no name resolves to `decl` in `σ` (`hd`); and
  - `fm` implies no more about `decl` than `fm₀` (`hfm`),

  then:
  - after promoting the location that `e` refers to, if any, to `T`, `fm` still implies no more
    about `decl` than `fm₀` (`FactsSub decl (fm.tryPromote em.ref? em.type T) fm₀`).

  This holds because the location, if any, is a variable that a name resolves to.
  -/
  tryPromote_frame {π : AstPath} {σ : Scope} {fm₀ fm : FlowModel} {e : Expr}
      {m : LoweredExpr (τ := τ)} {em : ExprModel (τ := τ) (ℓ := AstPath)}
      (helab : ElabExpr π σ fm₀ e m em) (hnp : e.NoProperties) (hd : ¬Resolves σ decl)
      (hfm : FactsSub decl fm fm₀) (T : τ) :
      FactsSub decl (fm.tryPromote em.ref? em.type T) fm₀ := by
    cases hr : em.ref? with
    | none => simpa [FlowModel.tryPromote] using hfm
    | some r =>
      obtain ⟨n, v, decl', pm, hl, -, -, rfl, -⟩ := ElabExpr.eq_var_of_ref helab hnp hr
      have hne : decl' ≠ decl := by
        rintro rfl
        exact hd ⟨_, _, hl⟩
      exact (FactsSub.tryPromote hne).trans hfm

omit Γ in
/--
Adding the statement `s` to the scope doesn't make an outer declaration visible.

Here `π` is the AST path of a nonempty statement list `s :: ss` (see `ElabStmts`), so `s` itself is
at `0 :: π` (an AST path lists child indices from a node up to the root). The statements `ss` after
`s` are analyzed in the scope `s.extendScope σ (0 :: π)`.

If no name resolves to `decl` in scope `σ` (`hd`), and `decl` isn't in the subtree at `π` (`hπ`),
then no name resolves to `decl` in the scope that the statements after `s` are analyzed in
(`¬Resolves (s.extendScope σ (0 :: π)) decl`).

This holds because the scope that `s` extends `σ` to has at most one new entry: if `s` declares a
variable, an entry for that declaration, which is at `s`'s own path `0 :: π`. That path is in the
subtree at `π`, and `decl` isn't, so the new entry isn't for `decl`; and no entry already in `σ` is
for `decl` either (`hd`).
-/
public theorem not_resolves_extendScope {σ : Scope} {decl : AstPath} {π : AstPath}
    {s : Stmt (τ := τ)} (hd : ¬Resolves σ decl) (hπ : ¬π <:+ decl) :
    ¬Resolves (s.extendScope σ (0 :: π)) decl := by
  cases s with
  | declare n T isFinal =>
    rintro ⟨n', v, hl⟩
    simp only [Stmt.extendScope, List.lookup] at hl
    split at hl
    · cases hl
      exact hπ (List.suffix_cons _ _)
    · exact hd ⟨n', v, hl⟩
  | _ => exact hd

mutual

/--
Elaborating a statement leaves alone the facts about a declaration that no name resolves to, and
that isn't in the statement's subtree.

If the following conditions hold:
- the statement `s`, at AST path `π` and in scope `σ`, elaborates to `m`, taking flow model `fm₀`
  to `fm₁` (`helab`);
- `s` reads no properties (`hnp`);
- no name resolves to `decl` in `σ` (`hd`); and
- `decl` isn't in the subtree at `π` (`hπ`),

then:
- `fm₁` implies no more about the declaration at `decl` than `fm₀` did (`FactsSub decl fm₁ fm₀`).
-/
public theorem ElabStmt.frame {decl : AstPath} {π : AstPath} {σ : Scope} {fm₀ : FlowModel}
    {s : Stmt (τ := τ)} {m : LoweredExpr (τ := τ)} {fm₁ : FlowModel}
    (helab : ElabStmt π σ fm₀ s m fm₁) (hnp : s.NoProperties) (hd : ¬Resolves σ decl)
    (hπ : ¬π <:+ decl) : FactsSub decl fm₁ fm₀ :=
  match helab, hnp, hd, hπ with
  | .declare π _ _ _ _ _, _, _, hπ =>
    FactsSub.set_ne fun h => hπ (h ▸ List.suffix_refl π)
  | .exprStmt (em := em) h, hnp, hd, _ =>
    (FactsSub.join_left decl em.fm_true em.fm_false).trans (ElabExpr.frame h hnp hd).1
  | .ifStmt h₁ _ h₂ _, hnp, hd, hπ =>
    (FactsSub.join_left _ _ _).trans
      ((ElabStmt.frame h₂ hnp.2.1 hd fun h => hπ ((List.suffix_cons _ _).trans h)).trans
        (ElabExpr.frame h₁ hnp.1 hd).1)
  | .block h, hnp, hd, hπ =>
    ElabStmts.frame h hnp hd fun h => hπ ((List.suffix_cons _ _).trans h)

/--
Elaborating a list of statements leaves alone the facts about a declaration that no name resolves
to, and that isn't in the list's subtree.

If the following conditions hold:
- the statements `ss`, at AST path `π` and in scope `σ`, elaborate to `ms`, taking flow model `fm₀`
  to `fm₁` (`helab`);
- the statements read no properties (`hnp`);
- no name resolves to `decl` in `σ` (`hd`); and
- `decl` isn't in the subtree at `π` (`hπ`),

then:
- `fm₁` implies no more about the declaration at `decl` than `fm₀` did (`FactsSub decl fm₁ fm₀`).
-/
public theorem ElabStmts.frame {decl : AstPath} {π : AstPath} {σ : Scope} {fm₀ : FlowModel}
    {ss : List (Stmt (τ := τ))} {ms : List (LoweredExpr (τ := τ))} {fm₁ : FlowModel}
    (helab : ElabStmts π σ fm₀ ss ms fm₁) (hnp : Stmt.NoPropertiesList ss)
    (hd : ¬Resolves σ decl) (hπ : ¬π <:+ decl) : FactsSub decl fm₁ fm₀ :=
  match helab, hnp, hd, hπ with
  | .nil, _, _, _ => FactsSub.refl _ _
  | .cons h hs, hnp, hd, hπ =>
    (ElabStmts.frame hs hnp.2 (not_resolves_extendScope hd hπ)
        fun h => hπ ((List.suffix_cons _ _).trans h)).trans
      (ElabStmt.frame h hnp.1 hd fun h => hπ ((List.suffix_cons _ _).trans h))

end

/--
A fact about variable `v` (`hfv`) that `fm₁` implies in scope `σ` (`hf`) is implied by `fm₀` too, if
`fm₁` implies no more than `fm₀` about each declaration of `v` in `σ` (`h`).
-/
public theorem mem_ctxOf_of_factsSub {σ : Scope} {fm₁ fm₀ : FlowModel} {v : Variable} {f : Fact}
    (h : ∀ e ∈ σ, e.2.1 = v → FactsSub e.2.2 fm₁ fm₀) (hf : f ∈ ctxOf σ fm₁)
    (hfv : f.variable = v) : f ∈ ctxOf σ fm₀ := by
  induction σ with
  | nil => simp [ctxOf] at hf
  | cons e σ ih =>
    obtain ⟨n, v', decl⟩ := e
    simp only [ctxOf, List.mem_append] at hf ⊢
    rcases hf with hf | hf
    · have hv : v' = v := (variable_of_mem_factsOf hf).symm.trans hfv
      exact .inl (h (n, v', decl) (List.mem_cons_self ..) hv v' f hf)
    · obtain ⟨hf, hfv'⟩ := Ctx.mem_forget.1 hf
      exact .inr (Ctx.mem_forget.2
        ⟨ih (fun e he => h e (List.mem_cons_of_mem _ he)) hf, hfv'⟩)

end FlowSoundness
