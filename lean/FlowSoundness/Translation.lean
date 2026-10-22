module
public import FlowAnalysis.Elaboration
public import DartSemantics.Compat

/-!
# Translating flow models to facts

The proof that flow analysis is sound relates what flow analysis knows at a point in the program
(a scope `σ` and a flow model `fm`) to what the semantic typing judgment knows (a list of facts, see
`DartSemantics.Fact`). This file defines `ctxOf σ fm` as the list of facts that `σ` and `fm` imply,
and proves lemmas about how `ctxOf` changes when flow analysis updates a promotion model.

For each variable in scope, `ctxOf` uses the innermost declaration of that `Variable` in `σ`, and
its promotion model in `fm`. It produces the facts that:
- the variable is in scope (`Fact.decl`);
- it hasn't been assigned (`Fact.uninit`), if it's `final` and definitely unassigned (the only case
  where semantic typing needs this fact); and
- it holds a value that satisfies its declared type and each type it's promoted to (`Fact.var`), if
  it's readable (`PromotionModel.Readable`).

Most lemmas assume that the scope is *well formed* (`Scope.WellFormed`): the declarations in it are
at distinct paths, and each entry is for a variable with the entry's name. The soundness proof
threads a stronger invariant through elaboration: the scope of the node at AST path `π` is *well
formed at* `π` (`Scope.WellFormedAt`), meaning that it is well formed, and no declaration in it lies
in the subtree at `π`.

The proof covers the property-free subset of Dart (`Expr.NoProperties`); facts about
property paths are left for later.
-/

namespace FlowAnalysis

open DartLang

variable {τ : Type} [DartTypeRepr τ]

/-! ### The property-free subset of Dart -/

/-- Whether expression `e` reads no properties. -/
@[expose]
public def Expr.NoProperties : Expr (τ := τ) → Prop
  | .var _ => True
  | .nullCheck e => e.NoProperties
  | .as e _ => e.NoProperties
  | .is e _ => e.NoProperties
  | .null => True
  | .property _ _ => False
  | .assign _ e => e.NoProperties

mutual

/-- Whether statement `s` reads no properties. -/
@[expose]
public def Stmt.NoProperties : Stmt (τ := τ) → Prop
  | .declare _ _ _ => True
  | .exprStmt e => e.NoProperties
  | .ifStmt e s₂ s₃ => e.NoProperties ∧ s₂.NoProperties ∧ s₃.NoProperties
  | .block ss => Stmt.NoPropertiesList ss

/-- Whether none of the statements in `ss` reads properties. -/
@[expose]
public def Stmt.NoPropertiesList : List (Stmt (τ := τ)) → Prop
  | [] => True
  | s :: ss => s.NoProperties ∧ Stmt.NoPropertiesList ss

end

end FlowAnalysis

namespace FlowSoundness

open DartLang DartSemantics FlowAnalysis

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Fact" => Fact (τ := τ)
local notation "Ctx" => Ctx (τ := τ)
local notation "Scope" => Scope (τ := τ)
local notation "Expr" => Expr (τ := τ)
local notation "Stmt" => Stmt (τ := τ)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := AstPath)
local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := AstPath)

/-! ### The translation -/

/--
The facts that promotion model `pm` implies about variable `v`:
- that `v` hasn't been assigned (`Fact.uninit v`), if `v` is `final` and `pm` says it's definitely
  unassigned; and
- that `v` holds a value that satisfies `v`'s declared type, and each type in `pm`'s promotion chain
  (`Fact.var v U`), if `v` is readable (`pm.Readable v`).
-/
@[expose]
public def pmFacts (v : Variable) (pm : PromotionModel) : Ctx :=
  (if v.isFinal && pm.unassigned then [.uninit v] else []) ++
    (if pm.Readable v then (v.type :: pm.promotedTypes.val).map (.var v) else [])

/--
The facts about variable `v`, declared at `decl`, that flow model `fm` implies: that `v` is in scope
(`Fact.decl v`), plus the facts that its promotion model implies (`pmFacts`), if it has one.
-/
@[expose]
public def factsOf (v : Variable) (decl : AstPath) (fm : FlowModel) : Ctx :=
  .decl v :: match fm.promotionInfo (.var decl) with
    | none => []
    | some pm => pmFacts v pm

/--
The list of facts that scope `σ` and flow model `fm` imply: for each variable in scope, the facts
about it that `fm` implies (`factsOf`), for its innermost declaration in `σ`. An inner declaration
of the same `Variable` shadows an outer one, so the facts about the outer one are left out.
-/
@[expose]
public def ctxOf : Scope → FlowModel → Ctx
  | [], _ => []
  | (_, v, decl) :: σ, fm => factsOf v decl fm ++ (ctxOf σ fm).forget v

/--
A scope `σ` is *well formed* if:
- the declarations in `σ` are at distinct paths (`nodup`); and
- each entry of `σ` is for a variable with the entry's name (`names`).
-/
public structure Scope.WellFormed (σ : Scope) : Prop where
  nodup : (σ.map (·.2.2)).Nodup
  names : ∀ e ∈ σ, e.2.1.name = e.1

/--
A scope `σ` is *well formed at* AST path `π` if it is well formed, and no declaration in `σ` lies
in the subtree at `π` (`fresh`). This is the invariant on scopes that the soundness proof threads
through: the scope of the node at `π` is well formed at `π`.
-/
public structure Scope.WellFormedAt (π : AstPath) (σ : Scope) : Prop
    extends Scope.WellFormed σ where
  fresh : ∀ e ∈ σ, ¬ π <:+ e.2.2

/-! ### Basic properties -/

/-- Every fact that `pmFacts` produces for `v` (`h`) is about `v` (`f.variable = v`). -/
public theorem variable_of_mem_pmFacts {v : Variable} {pm : PromotionModel} {f : Fact}
    (h : f ∈ pmFacts v pm) : f.variable = v := by
  simp only [pmFacts, List.mem_append] at h
  rcases h with h | h
  · split at h <;> simp_all [Fact.variable]
  · split at h
    · obtain ⟨_, -, rfl⟩ := List.mem_map.1 h
      rfl
    · simp at h

/-- Every fact that `factsOf` produces for `v` (`h`) is about `v` (`f.variable = v`). -/
public theorem variable_of_mem_factsOf {v : Variable} {decl : AstPath} {fm : FlowModel} {f : Fact}
    (h : f ∈ factsOf v decl fm) : f.variable = v := by
  simp only [factsOf, List.mem_cons] at h
  rcases h with rfl | h
  · rfl
  · split at h
    · simp at h
    · exact variable_of_mem_pmFacts h

/--
`ctxOf σ` only depends on the promotion models of the declarations in `σ`: if `fm₁` and `fm₂` agree
on those promotion models (`h`), then `ctxOf σ fm₁ = ctxOf σ fm₂`.
-/
public theorem ctxOf_congr {σ : Scope} {fm₁ fm₂ : FlowModel}
    (h : ∀ e ∈ σ, fm₁.promotionInfo (.var e.2.2) = fm₂.promotionInfo (.var e.2.2)) :
    ctxOf σ fm₁ = ctxOf σ fm₂ := by
  induction σ with
  | nil => rfl
  | cons e σ ih =>
    obtain ⟨n, v, decl⟩ := e
    simp only [ctxOf, factsOf, h (n, v, decl) (List.mem_cons_self ..),
      ih (fun e he => h e (List.mem_cons_of_mem _ he))]

/--
Updating the promotion model of a declaration that isn't in `σ` (`h`) doesn't change `ctxOf σ`.
-/
public theorem ctxOf_set_of_not_mem {σ : Scope} {fm : FlowModel} {decl : AstPath}
    {pm : PromotionModel} (h : decl ∉ σ.map (·.2.2)) :
    ctxOf σ (fm.set (.var decl) pm) = ctxOf σ fm := by
  refine ctxOf_congr fun e he => ?_
  have hne : decl ≠ e.2.2 := fun heq => h (List.mem_map.2 ⟨e, he, heq.symm⟩)
  simp [FlowModel.set, hne]

omit Γ in
/-- If looking up name `n` in scope `σ` finds `x` (`h`), then `(n, x)` is an entry of `σ`. -/
public theorem mem_of_lookup {σ : Scope} {n : String} {x : Variable × AstPath}
    (h : σ.lookup n = some x) : (n, x) ∈ σ := by
  induction σ with
  | nil => simp at h
  | cons e σ ih =>
    obtain ⟨n', x'⟩ := e
    simp only [List.lookup] at h
    split at h
    · rename_i heq
      cases h
      simp only [beq_iff_eq] at heq
      subst heq
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

/--
Each fact that a flow model implies about a variable in scope is in `ctxOf σ fm` (`f ∈ ctxOf σ fm`),
given that:
- `σ` is well formed (`hwf`);
- name `n` resolves in `σ` to the variable `v`, declared at `decl` (`hl`); and
- `f` is a fact that flow model `fm` implies about `v` (`hf`).
-/
public theorem mem_ctxOf_of_lookup {σ : Scope} {fm : FlowModel} {n : String} {v : Variable}
    {decl : AstPath} {f : Fact} (hwf : Scope.WellFormed σ)
    (hl : σ.lookup n = some (v, decl)) (hf : f ∈ factsOf v decl fm) : f ∈ ctxOf σ fm := by
  obtain ⟨-, hnames⟩ := hwf
  induction σ with
  | nil => simp at hl
  | cons e σ ih =>
    obtain ⟨n', v', d'⟩ := e
    simp only [List.lookup] at hl
    simp only [ctxOf, List.mem_append]
    split at hl
    · cases hl
      exact .inl hf
    · rename_i hne
      have hvn : v.name = n := hnames (n, v, decl) (List.mem_cons_of_mem _ (mem_of_lookup hl))
      have hvn' : v'.name = n' := hnames (n', v', d') (List.mem_cons_self ..)
      have hvv : f.variable ≠ v' := by
        rw [variable_of_mem_factsOf hf]
        rintro rfl
        simp_all
      exact .inr (Ctx.mem_forget.2
        ⟨ih hl (fun e he => hnames e (List.mem_cons_of_mem _ he)), hvv⟩)

/--
Updating the promotion model of the variable that a name resolves to only changes the facts about
that variable.

If the following conditions hold:
- `σ` is well formed (`hwf`);
- name `n` resolves in `σ` to the variable `v`, declared at `decl` (`hl`); and
- `f` is a fact in `ctxOf σ` after setting `v`'s promotion model in `fm` to `pm` (`hf`),

then either:
- `f` is about `v`, and comes from `pm` (`f ∈ factsOf v decl (fm.set (.var decl) pm)`); or
- `f` isn't about `v`, and was in `ctxOf σ` before the update (`f.variable ≠ v ∧ f ∈ ctxOf σ fm`).
-/
public theorem mem_ctxOf_set {σ : Scope} {fm : FlowModel} {n : String} {v : Variable}
    {decl : AstPath} {pm : PromotionModel} {f : Fact} (hwf : Scope.WellFormed σ)
    (hl : σ.lookup n = some (v, decl))
    (hf : f ∈ ctxOf σ (fm.set (.var decl) pm)) :
    f ∈ factsOf v decl (fm.set (.var decl) pm) ∨ (f.variable ≠ v ∧ f ∈ ctxOf σ fm) := by
  obtain ⟨hnodup, hnames⟩ := hwf
  induction σ with
  | nil => simp at hl
  | cons e σ ih =>
    obtain ⟨n', v', d'⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.lookup] at hl
    simp only [ctxOf, List.mem_append] at hf ⊢
    split at hl
    · cases hl
      rcases hf with hf | hf
      · exact .inl hf
      · obtain ⟨hf, hfv⟩ := Ctx.mem_forget.1 hf
        rw [ctxOf_set_of_not_mem hnodup.1] at hf
        exact .inr ⟨hfv, .inr (Ctx.mem_forget.2 ⟨hf, hfv⟩)⟩
    · rename_i hne
      have hmem := mem_of_lookup hl
      have hdd : decl ≠ d' := fun heq => hnodup.1 (List.mem_map.2 ⟨_, hmem, heq⟩)
      have hvn : v.name = n := hnames (n, v, decl) (List.mem_cons_of_mem _ hmem)
      have hvn' : v'.name = n' := hnames (n', v', d') (List.mem_cons_self ..)
      have hvv : v' ≠ v := by
        rintro rfl
        simp_all
      rcases hf with hf | hf
      · have hfacts : factsOf v' d' (fm.set (.var decl) pm) = factsOf v' d' fm := by
          simp [factsOf, FlowModel.set, hdd]
        rw [hfacts] at hf
        refine .inr ⟨?_, .inl hf⟩
        rw [variable_of_mem_factsOf hf]
        exact hvv
      · obtain ⟨hf, hfv⟩ := Ctx.mem_forget.1 hf
        rcases ih hl hf hnodup.2 (fun e he => hnames e (List.mem_cons_of_mem _ he)) with h | h
        · exact .inl h
        · exact .inr ⟨h.1, .inr (Ctx.mem_forget.2 ⟨h.2, hfv⟩)⟩

/--
A fact about variable `v` that the join of two promotion models implies (`h`) is implied by each of
them (`f ∈ pmFacts v pm₁` and `f ∈ pmFacts v pm₂`).
-/
public theorem mem_pmFacts_join {v : Variable} {pm₁ pm₂ : PromotionModel} {f : Fact}
    (h : f ∈ pmFacts v (pm₁.join pm₂)) : f ∈ pmFacts v pm₁ ∧ f ∈ pmFacts v pm₂ := by
  simp only [pmFacts, PromotionModel.Readable, PromotionModel.join, List.mem_append,
    List.mem_ite_nil_right, List.not_mem_nil, or_false, List.mem_map, List.mem_cons,
    PromotionChain.mem_join, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with ⟨⟨hf, hu₁, hu₂⟩, rfl⟩ | ⟨hc, hU⟩
  · exact ⟨.inl ⟨⟨hf, hu₁⟩, rfl⟩, .inl ⟨⟨hf, hu₂⟩, rfl⟩⟩
  · obtain ⟨U, hU, rfl⟩ := hU
    constructor <;> exact .inr ⟨by tauto, U, by tauto, rfl⟩

/--
A fact that the join of two flow models implies in scope `σ` (`h`) is implied by each of them
(`f ∈ ctxOf σ fm₁` and `f ∈ ctxOf σ fm₂`).
-/
public theorem mem_ctxOf_join {σ : Scope} {fm₁ fm₂ : FlowModel} {f : Fact}
    (h : f ∈ ctxOf σ (fm₁.join fm₂)) : f ∈ ctxOf σ fm₁ ∧ f ∈ ctxOf σ fm₂ := by
  induction σ with
  | nil => simp [ctxOf] at h
  | cons e σ ih =>
    obtain ⟨n, v, decl⟩ := e
    simp only [ctxOf, List.mem_append] at h ⊢
    rcases h with h | h
    · simp only [factsOf, List.mem_cons] at h ⊢
      rcases h with rfl | h
      · exact ⟨.inl (.inl rfl), .inl (.inl rfl)⟩
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
              exact ⟨.inl (.inr (by rw [hpm₁]; exact h₁)), .inl (.inr (by rw [hpm₂]; exact h₂))⟩
    · obtain ⟨h, hfv⟩ := Ctx.mem_forget.1 h
      obtain ⟨h₁, h₂⟩ := ih h
      exact ⟨.inr (Ctx.mem_forget.2 ⟨h₁, hfv⟩), .inr (Ctx.mem_forget.2 ⟨h₂, hfv⟩)⟩

/--
A type `U` in the promotion chain `c` after trying to promote it to `T` (`h`) was in `c` before
(`U ∈ c.val`), or is `T` (`U = T`).
-/
public theorem mem_tryPromote {c : PromotionChain (τ := τ)} {T U : τ}
    (h : U ∈ (c.tryPromote T).val) : U ∈ c.val ∨ U = T := by
  by_cases hb : c.strictly_bounds T
  · rw [PromotionChain.val_tryPromote_of_strictly_bounds hb] at h
    simpa using h
  · simp only [PromotionChain.tryPromote, hb, dite_false] at h
    exact .inl h

/--
A fact `f` about variable `v` that promotion model `pm` implies after promoting it to `T` (`h`) was
implied before (`f ∈ pmFacts v pm`), or is that `v` holds a value that satisfies `T`
(`f = .var v T`).
-/
public theorem mem_pmFacts_tryPromote {v : Variable} {pm : PromotionModel} {T : τ}
    {hwc : ¬pm.writeCaptured} {f : Fact} (h : f ∈ pmFacts v (pm.tryPromote T hwc)) :
    f ∈ pmFacts v pm ∨ f = .var v T := by
  have ha : (pm.tryPromote T hwc).assigned = pm.assigned := rfl
  have hu : (pm.tryPromote T hwc).unassigned = pm.unassigned := rfl
  have hp : (pm.tryPromote T hwc).promotedTypes = pm.promotedTypes.tryPromote T := rfl
  simp only [pmFacts, PromotionModel.Readable, ha, hu, hp, List.mem_append,
    List.mem_ite_nil_right, List.mem_map, List.mem_cons] at h ⊢
  rcases h with h | ⟨hc, U, hU, rfl⟩
  · exact .inl (.inl h)
  · rcases hU with rfl | hU
    · exact .inl (.inr ⟨hc, _, .inl rfl, rfl⟩)
    · rcases mem_tryPromote hU with hU | rfl
      · exact .inl (.inr ⟨hc, U, .inr hU, rfl⟩)
      · exact .inr rfl

/--
Promoting the variable that a name resolves to adds at most one fact: that the variable holds a
value that satisfies the type it's promoted to.

If the following conditions hold:
- `σ` is well formed (`hwf`);
- name `n` resolves in `σ` to the variable `v`, declared at `decl` (`hl`);
- `v`'s promotion model in `fm` is `pm` (`hpm`); and
- `f` is a fact in `ctxOf σ` after flow analysis tries to promote `v` to `T` in `fm` (`hf`),

then:
- `f` was in `ctxOf σ` before the promotion, or is that `v` holds a value that satisfies `T`
  (`f ∈ .var v T :: ctxOf σ fm`).
-/
public theorem mem_ctxOf_tryPromote {σ : Scope} {fm : FlowModel} {n : String} {v : Variable}
    {decl : AstPath} {version? : Option (ValueVersion (ℓ := AstPath))} {pm : PromotionModel}
    {previousType T : τ} {f : Fact} (hwf : Scope.WellFormed σ) (hl : σ.lookup n = some (v, decl))
    (hpm : fm.promotionInfo (.var decl) = some pm)
    (hf : f ∈ ctxOf σ (fm.tryPromote (some (.var decl version?)) previousType T)) :
    f ∈ .var v T :: ctxOf σ fm := by
  simp only [FlowModel.tryPromote, FlowModel.infoFor, Reference.key_var, hpm] at hf
  split at hf
  · rename_i hc
    rcases mem_ctxOf_set hwf hl hf with h | ⟨-, h⟩
    · simp only [factsOf, FlowModel.set, ite_true, List.mem_cons] at h
      rcases h with rfl | h
      · exact .tail _ (mem_ctxOf_of_lookup hwf hl (by simp [factsOf]))
      · rcases mem_pmFacts_tryPromote h with h | rfl
        · exact .tail _ (mem_ctxOf_of_lookup hwf hl (by simp [factsOf, hpm, h]))
        · exact .head _
    · exact .tail _ h
  · exact .tail _ hf

/--
After an assignment to the variable that a name resolves to, every fact is implied by one of the
facts that `SemTyped.variableSet` guarantees.

If the following conditions hold:
- `σ` is well formed (`hwf`);
- name `n` resolves in `σ` to the variable `v`, declared at `decl` (`hl`);
- `T`, the type of the assigned value, is a subtype of `v`'s declared type (`hT`); and
- `f` is a fact in `ctxOf σ` after setting `v`'s promotion model in `fm` to `pm.write T version`,
  the promotion model after assigning a value of type `T` (`hf`),

then `f` is implied (`f₀.Implies f`) by some fact `f₀` among the following:
- that `v` holds a value that satisfies `T` (`.var v T`);
- that `v` is in scope (`.decl v`); or
- a fact in `ctxOf σ` before the assignment that isn't about `v` (`(ctxOf σ fm).forget v`).
-/
public theorem implies_ctxOf_write {σ : Scope} {fm : FlowModel} {n : String} {v : Variable}
    {decl : AstPath} {pm : PromotionModel} {T : τ} {version : ValueVersion (ℓ := AstPath)}
    {f : Fact} (hwf : Scope.WellFormed σ)
    (hl : σ.lookup n = some (v, decl)) (hT : T ≤ v.type)
    (hf : f ∈ ctxOf σ (fm.set (.var decl) (pm.write T version))) :
    ∃ f₀ ∈ (Fact.var v T :: .decl v :: (ctxOf σ fm).forget v), f₀.Implies f := by
  rcases mem_ctxOf_set hwf hl hf with h | ⟨hfv, h⟩
  · simp only [factsOf, FlowModel.set, ite_true, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨.decl v, .tail _ (.head _), Fact.Implies.refl _⟩
    · simp only [pmFacts, PromotionModel.Readable, PromotionModel.write, Bool.and_false,
        List.mem_append, List.mem_ite_nil_right, List.mem_map, List.mem_cons,
        PromotionChain.val_demote, List.mem_filter, decide_eq_true_eq] at h
      rcases h with ⟨h, -⟩ | ⟨-, U, hU, rfl⟩
      · simp at h
      · refine ⟨.var v T, .head _, rfl, ?_⟩
        rcases hU with rfl | ⟨-, hU⟩
        · exact hT
        · exact hU
  · exact ⟨f, .tail _ (.tail _ (Ctx.mem_forget.2 ⟨h, hfv⟩)), Fact.Implies.refl _⟩

end FlowSoundness
