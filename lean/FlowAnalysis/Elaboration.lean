module
import DartLang.Types
public import FlowAnalysis.State
public import FlowAnalysis.Syntax
public import DartLang.Lowered

/-!
# The specification of flow analysis

This module is the declarative specification of flow analysis, for the subset of Dart in
`FlowAnalysis.Syntax`. It's a set of inference rules, one for each kind of expression or statement,
in the style of the rules in `flow-analysis.md`:

- `ElabExpr π σ fm₀ e m em`: the expression `e`, at AST path `π` and in scope `σ`, analyzed
  starting from the flow model `fm₀`, has the expression model `em` (its static type, the location
  it read, and the flow models after it), and is lowered to `m`.
- `ElabStmt` and `ElabStmts`: likewise for statements and statement lists, taking a flow model to a
  flow model.

Unlike `flow-analysis.md`, which only describes the flow models, the rules also produce the
`LoweredExpr` that each construct is lowered to. That is what lets the semantics give meaning to the
promotions flow analysis makes, so that their soundness can be proved. A program that no rule
applies to is one that flow analysis rejects (for example, because it reads a variable that isn't
definitely assigned).

The module also proves that elaboration preserves `FlowModel.WellFormed`.
-/

namespace FlowAnalysis
open DartLang

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "LoweredExpr" => LoweredExpr (τ := τ)

section
variable {ℓ : Type} [DecidableEq ℓ]

local notation "FlowModel" => FlowModel (τ := τ) (ℓ := ℓ)
local notation "Reference" => Reference (ℓ := ℓ)

/--
`fm.tryPromote ref? previousType T` returns an updated flow model in which the referent of `ref?`
has been promoted from `previousType` to `T`, assuming such a promotion is valid. Otherwise it
returns `fm` unchanged.

`previousType` is the static type of the expression that produced the reference, exactly as in the
implementation, where it is `_Reference._type`.  It is not recomputed from the flow model, which is
what lets this function serve any kind of key without knowing what the key names.

A write-captured location is never promoted: flow analysis has given up on tracking which value it
holds, so it has no basis for a promotion.  The guard is also what supplies the hypothesis
`PromotionModel.tryPromote` needs in order to re-establish `writeCaptured_promotedTypes`.

The promotion model to promote is obtained with `FlowModel.infoFor`, as in the Dart implementation,
so a location with no promotion model yet (as for the first promotion of a property) is promoted
starting from a fresh model. `infoFor` returns `none` only for a write-captured location, which
wouldn't be promoted anyway.
-/
@[expose]
public def FlowModel.tryPromote (ref? : Option Reference) (previousType T : τ)
    (fm : FlowModel) :
    FlowModel :=
  match ref? with
  | none => fm
  | some r =>
    match fm.infoFor r with
    | some pm =>
      if h : ¬pm.writeCaptured ∧ T < previousType then
        fm.set r.key (pm.tryPromote T h.1)
      else
        fm
    | none => fm

/--
`fm.promoteToNonNull ref? previousType` promotes the referent of `ref?` to the non-nullable form of
`previousType`, if that is a valid promotion.

Mirrors the specification's `promoteToNonNull(E, M)`, which is defined in terms of `promote` in
exactly this way.
-/
@[expose]
public def FlowModel.promoteToNonNull (ref? : Option Reference) (previousType : τ)
    (fm : FlowModel) : FlowModel :=
  fm.tryPromote ref? previousType (NonNull previousType)

/--
Promoting a reference preserves well-formedness (`(fm.tryPromote ref? previousType T).WellFormed`,
given `hwf`): the model stored back under the key is the one `infoFor` supplied, with an extra
promoted type, so it holds the same version.
-/
public theorem FlowModel.WellFormed.tryPromote {fm : FlowModel} (hwf : fm.WellFormed)
    (ref? : Option Reference) (previousType T : τ) :
    (fm.tryPromote ref? previousType T).WellFormed := by
  simp only [FlowModel.tryPromote]
  split
  case h_1 => exact hwf
  case h_2 r =>
    split
    case h_1 pm hinfo =>
      split
      case isTrue => exact hwf.set fun v q hkey => hwf.infoFor hinfo v q hkey
      case isFalse => exact hwf
    case h_2 => exact hwf

end

/-
The elaboration rules label the value versions they create by AST paths, so from here on labels are
`AstPath`s.
-/

local notation "ExprModel" => ExprModel (τ := τ) (ℓ := AstPath)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := AstPath)
local notation "Scope" => Scope (τ := τ)

/--
Expression elaboration rules.

`ElabExpr π σ fm₀ e m em` says that the expression `e`, at AST path `π` and in scope `σ`, elaborates
to `m` with expression model `em`, starting from flow model `fm₀`.
-/
public inductive ElabExpr : AstPath → Scope → FlowModel → Expr →
    LoweredExpr → ExprModel -> Prop where
  /--
  Read of the variable named `n`: the innermost declaration of `n` in scope, which is the variable
  `v`, declared at `decl`.

  The variable must be readable (`PromotionModel.Readable`): definitely assigned, unless it starts
  out holding the null object.

  There is deliberately no rule for a name that isn't in scope, or for a variable with no promotion
  model: referring to an undeclared variable is a compile-time error. (Dart's `variableRead` instead
  falls back to a fresh promotion model.)
  -/
  | var {π σ fm n v decl pm T} :
      σ.lookup n = some (v, decl) →
      (fm : FlowModel).promotionInfo (.var decl) = some pm →
      pm.Readable v →
      T = pm.currentType v.type →
      -- `(τ := τ)`: nothing in `.var n` determines `τ`, and leaving it to unification makes the
      -- kernel reject this constructor.
      ElabExpr π σ fm (Expr.var (τ := τ) n) (.var v T) ⟨T, some (.var decl pm.version?), fm, fm⟩
  /-- Null check operator (`e₁!`). -/
  | nullCheck {π σ fm₀ e₁ m₁ em₁ fm} :
      ElabExpr (0 :: π) σ fm₀ e₁ m₁ em₁ →
      fm = em₁.fm_after.promoteToNonNull em₁.ref? em₁.type →
      ElabExpr π σ fm₀ e₁.nullCheck m₁.nullCheck ⟨NonNull em₁.type, none, fm, fm⟩
  /-- Type cast (`e₁ as T`). -/
  | asExpr {π σ fm₀ e₁ m₁ em₁ fm T} :
      ElabExpr (0 :: π) σ fm₀ e₁ m₁ em₁ →
      fm = em₁.fm_after.tryPromote em₁.ref? em₁.type T →
      ElabExpr π σ fm₀ (e₁.as T) (m₁.as T) ⟨T, none, fm, fm⟩
  /-- Null literal (`null`). -/
  | nullLiteral {π σ fm} :
      ElabExpr π σ fm .null .null ⟨Γ.Null, none, fm, fm⟩
  /--
  Property read (`e₁.p`). Mirrors Dart's `propertyGet`.

  The read refers to the property of the value that `e₁` read, if flow analysis tracks it (see
  `Reference.property?`), and its type is the property's promoted type, if any. The read doesn't
  change the flow model: like Dart's `_handleProperty`, it only looks up the property's promotion
  model, and doesn't create one.
  -/
  | propertyGet {π σ fm₀ e₁ m₁ em₁ p ref? T} :
      ElabExpr (0 :: π) σ fm₀ e₁ m₁ em₁ →
      ref? = em₁.ref?.bind (·.property? p) →
      T = em₁.fm_after.currentTypeOf ref? p.type →
      ElabExpr π σ fm₀ (e₁.property p) (m₁.propertyGet p T)
        ⟨T, ref?, em₁.fm_after, em₁.fm_after⟩
  /--
  Assignment to the variable named `n` (`n = e₁`), resolved as for a read (to `v`, declared at
  `decl`). Mirrors the flow analysis specification's "Local-variable assignment" rule:
  `before(e₁) = before(N)`, and `after(N) = assign(x, e₁, after(e₁))`, so the variable's promotion
  model is updated (`PromotionModel.write`) in the flow model *after* `e₁`. The static type of
  `e₁` must be a subtype of `v`'s declared type (type coercion isn't modeled yet). The written value
  gets a new value version, labeled by the assignment's AST path.

  The assignment's value is not a reference to `v`, so it can't promote `v`.
  -/
  | assign {π σ fm₀ n e₁ m₁ em₁ v decl pm fm} :
      ElabExpr (0 :: π) σ fm₀ e₁ m₁ em₁ →
      σ.lookup n = some (v, decl) →
      em₁.fm_after.promotionInfo (.var decl) = some pm →
      em₁.type ≤ v.type →
      fm = em₁.fm_after.set (.var decl) (pm.write em₁.type (ValueVersion.root π)) →
      ElabExpr π σ fm₀ (.assign n e₁) (.variableSet v m₁) ⟨em₁.type, none, fm, fm⟩

mutual

/--
Statement elaboration rules.

`ElabStmt π σ fm₀ s m fm` says that the statement `s`, at AST path `π` and in scope `σ`, elaborates
to `m`, taking flow model `fm₀` to `fm`. (A declaration's effect on the scope of the statements that
follow it is handled by `ElabStmts`, using `Stmt.extendScope`.)
-/
public inductive ElabStmt : AstPath → Scope → FlowModel → Stmt →
    LoweredExpr → FlowModel -> Prop where
  /--
  Variable declaration statement. TODO: support more than one variable.

  Mirrors Dart's `declare`, which creates a new `ValueVersion` object for the variable. Here the new
  value version is the root labelled by the declaration's own AST path, so distinct declarations,
  including re-declarations of the same variable, get distinct versions. The variable itself is
  identified by the same path (see `Scope`), so its promotion model is recorded under `.var π`.
  Declarations have no initializers yet, so the variable starts out definitely unassigned. It starts
  out holding the null object if its type is nullable (`Variable.startsNull`).
  -/
  | declare π σ fm n T :
      ElabStmt π σ fm (.declare n T)
        (.declare ⟨n, T⟩ T (Variable.startsNull ⟨n, T⟩))
        (fm.set (.var π) (PromotionModel.declared false (ValueVersion.root π)))
  /-- Expression statement. -/
  | exprStmt {π σ fm₀ e m em} :
      ElabExpr (0 :: π) σ fm₀ e m em →
      ElabStmt π σ fm₀ (.exprStmt e) m em.fm_after
  /-- If statement. -/
  | ifStmt {π σ fm₀ e₁ m₁ em₁ s₂ m₂ fm₂ s₃ m₃ fm₃} :
      ElabExpr (0 :: π) σ fm₀ e₁ m₁ em₁ →
      -- TODO: support dynamic downcast
      em₁.type = Γ.bool →
      ElabStmt (1 :: π) σ em₁.fm_true s₂ m₂ fm₂ →
      ElabStmt (2 :: π) σ em₁.fm_false s₃ m₃ fm₃ →
      ElabStmt π σ fm₀ (.ifStmt e₁ s₂ s₃) (.cond m₁ m₂ m₃ Γ.Null) (fm₂.join fm₃)
  /--
  Block statement. The block's declarations go out of scope at its end, but nothing in the flow
  model is restored: the promotion models of the block's variables remain, under keys that nothing
  outside the block can name.
  -/
  | block {π σ fm₀ ss ms fm} :
      ElabStmts (0 :: π) σ fm₀ ss ms fm →
      ElabStmt π σ fm₀ (.block ss) (.block ms) fm

/--
Statement list elaboration rules.

A nonempty list is addressed by its cons cells: in `s :: ss` at path `π`, `s` is at `0 :: π` and
`ss` is at `1 :: π`. `ss` is elaborated in the scope extended by the variable that `s` declares, if
any.
-/
public inductive ElabStmts : AstPath → Scope → FlowModel → List Stmt →
    List (LoweredExpr) → FlowModel → Prop where
  | nil {π σ fm} : ElabStmts π σ fm [] [] fm
  | cons {π σ s ss fm₀ fm₁ fm m ms} :
      ElabStmt (0 :: π) σ fm₀ s m fm₁ →
      ElabStmts (1 :: π) (s.extendScope σ (0 :: π)) fm₁ ss ms fm →
      ElabStmts π σ fm₀ (s :: ss) (m :: ms) fm

end

-- Theorems --

/--
An expression whose elaboration (`helab`) has different flow models for `true` and `false`
(`hHasInfo`) has static type `bool` (`em.type = Γ.bool`).
-/
public theorem ElabExpr.boolInfo_onlyIf_bool {π σ} {fm : FlowModel} {e m} {em : ExprModel}
    (helab : ElabExpr π σ fm e m em) (hHasInfo : em.fm_true ≠ em.fm_false) : em.type = Γ.bool := by
  induction helab <;> simp_all

/--
Elaborating an expression (`helab`) from a well-formed flow model (`hwf`) produces well-formed flow
models, both for when it's `true` (`em.fm_true.WellFormed`) and for when it's `false`
(`em.fm_false.WellFormed`).

The only interesting case is the promotion of a property: the promotion model it stores under the
property's key is either the one already there, or a fresh one holding the version recorded in the
reference, which is the version named by the key.
-/
public theorem ElabExpr.wellFormed {π σ} {fm₀ : FlowModel} {e m} {em : ExprModel}
    (helab : ElabExpr π σ fm₀ e m em) (hwf : fm₀.WellFormed) :
    em.fm_true.WellFormed ∧ em.fm_false.WellFormed := by
  induction helab
  case var => exact ⟨hwf, hwf⟩
  case nullCheck ih =>
    obtain ⟨hwf_true, hwf_false⟩ := ih hwf
    subst_vars
    exact ⟨(hwf_true.join hwf_false).tryPromote _ _ _, (hwf_true.join hwf_false).tryPromote _ _ _⟩
  case asExpr ih =>
    obtain ⟨hwf_true, hwf_false⟩ := ih hwf
    subst_vars
    exact ⟨(hwf_true.join hwf_false).tryPromote _ _ _, (hwf_true.join hwf_false).tryPromote _ _ _⟩
  case nullLiteral => exact ⟨hwf, hwf⟩
  case propertyGet ih =>
    obtain ⟨hwf_true, hwf_false⟩ := ih hwf
    subst_vars
    exact ⟨hwf_true.join hwf_false, hwf_true.join hwf_false⟩
  case assign ih =>
    obtain ⟨hwf_true, hwf_false⟩ := ih hwf
    subst_vars
    exact ⟨(hwf_true.join hwf_false).set (by rintro r p ⟨⟩),
      (hwf_true.join hwf_false).set (by rintro r p ⟨⟩)⟩

mutual

/--
Elaborating a statement (`helab`) from a well-formed flow model (`hwf`) produces a well-formed flow
model (`fm.WellFormed`).
-/
public theorem ElabStmt.wellFormed {π σ} {fm₀ : FlowModel} {s m fm}
    (helab : ElabStmt π σ fm₀ s m fm) (hwf : fm₀.WellFormed) : fm.WellFormed :=
  match helab, hwf with
  | .declare _ _ _ _ _, hwf => hwf.set (by rintro r p ⟨⟩)
  | .exprStmt helab, hwf =>
    have ⟨hwf_true, hwf_false⟩ := helab.wellFormed hwf
    hwf_true.join hwf_false
  | .ifStmt helab₁ _ helab₂ helab₃, hwf =>
    have ⟨hwf_true, hwf_false⟩ := helab₁.wellFormed hwf
    (helab₂.wellFormed hwf_true).join (helab₃.wellFormed hwf_false)
  | .block helab, hwf => helab.wellFormed hwf

/--
Elaborating a statement list (`helab`) from a well-formed flow model (`hwf`) produces a well-formed
flow model (`fm.WellFormed`).
-/
public theorem ElabStmts.wellFormed {π σ} {fm₀ : FlowModel} {ss ms fm}
    (helab : ElabStmts π σ fm₀ ss ms fm) (hwf : fm₀.WellFormed) : fm.WellFormed :=
  match helab, hwf with
  | .nil, hwf => hwf
  | .cons helab helabs, hwf => helabs.wellFormed (helab.wellFormed hwf)

end

end FlowAnalysis
