module
import FlowAnalysis.Types
public import FlowAnalysis.State
public import FlowAnalysis.Syntax
public import FlowAnalysis.Lowered

namespace FlowAnalysis

open DartTypeRepr

variable {τ : Type} [Γ : DartTypeRepr τ]

local notation "LoweredExpr" => LoweredExpr (τ := τ)

section
variable {ℓ : Type} [DecidableEq ℓ]

local notation "FlowModel" => FlowModel (τ := τ) (ℓ := ℓ)
local notation "Key" => Key (τ := τ) (ℓ := ℓ)

/--
`fm.tryPromote ref? previousType T` returns an updated flow model in which the referent of `ref?` has
been promoted from `previousType` to `T`, assuming such a promotion is valid. Otherwise it returns
`fm` unchanged.

`previousType` is the static type of the expression that produced the reference, exactly as in the
implementation, where it is `_Reference._type`.  It is not recomputed from the flow model, which is
what lets this function serve any kind of key without knowing what the key names.

A write-captured location is never promoted: flow analysis has given up on tracking which value it
holds, so it has no basis for a promotion.  The guard is also what supplies the hypothesis
`PromotionModel.tryPromote` needs in order to re-establish `writeCaptured_promotedTypes`.

If the key has no promotion model, this returns `fm` unchanged. That departs from the Dart
implementation, whose `infoFor` creates `PromotionModel.fresh(version: reference.version)` and
promotes that. The branch is currently unreachable, because a key only comes from `ElabExpr.var`,
which requires the variable to have a promotion model, and a variable read doesn't change the flow
model.

TODO(stage 4): in the inner `none` branch, create a fresh promotion model at the reference's value
version and promote that.
-/
@[expose]
public def FlowModel.tryPromote (ref? : Option Key) (previousType T : τ)
    (fm : FlowModel) :
    FlowModel :=
  match ref? with
  | none => fm
  | some k =>
    match fm.promotionInfo k with
    | some pm =>
      if h : ¬pm.writeCaptured ∧ T < previousType then
        fm.set k (pm.tryPromote T h.1)
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
public def FlowModel.promoteToNonNull (ref? : Option Key) (previousType : τ) (fm : FlowModel) :
    FlowModel :=
  fm.tryPromote ref? previousType (NonNull previousType)

end

/-
The elaboration rules label the value versions they create by AST paths, so from here on labels are
`AstPath`s.
-/

local notation "ExprModel" => ExprModel (τ := τ) (ℓ := AstPath)
local notation "FlowModel" => FlowModel (τ := τ) (ℓ := AstPath)

/--
Expression elaboration rules.

`ElabExpr π fm₀ e m em` says that the expression `e`, at AST path `π`, elaborates to `m` with
expression model `em`, starting from flow model `fm₀`.
-/
public inductive ElabExpr : AstPath → FlowModel → Expr →
    LoweredExpr → ExprModel -> Prop where
  /--
  Read of variable `v`.

  There is deliberately no rule for a variable with no promotion model: referring to an undeclared
  variable is a compile-time error. (Dart's `variableRead` instead falls back to a fresh promotion
  model.)
  -/
  | var {π fm v pm T} :
      (fm : FlowModel).promotionInfo (.var v) = some pm →
      T = pm.currentType v.type →
      ElabExpr π fm (.var v) (.var v T) ⟨T, some (.var v), fm, fm⟩
  /-- Null check operator (`e₁!`). -/
  | nullCheck {π fm₀ e₁ m₁ em₁ fm} :
      ElabExpr (0 :: π) fm₀ e₁ m₁ em₁ →
      fm = em₁.fm_after.promoteToNonNull em₁.ref? em₁.type →
      ElabExpr π fm₀ e₁.nullCheck m₁.nullCheck ⟨NonNull em₁.type, none, fm, fm⟩
  /-- Type cast (`e₁ as T`). -/
  | asExpr {π fm₀ e₁ m₁ em₁ fm T} :
      ElabExpr (0 :: π) fm₀ e₁ m₁ em₁ →
      fm = em₁.fm_after.tryPromote em₁.ref? em₁.type T →
      ElabExpr π fm₀ (e₁.as T) (m₁.as T) ⟨T, none, fm, fm⟩
  /-- Null literal (`null`). -/
  | nullLiteral {π fm} :
      ElabExpr π fm .null .null ⟨Γ.Null, none, fm, fm⟩

mutual

/--
Statement elaboration rules.

`ElabStmt π fm₀ s m fm` says that the statement `s`, at AST path `π`, elaborates to `m`, taking flow
model `fm₀` to `fm`.
-/
public inductive ElabStmt : AstPath → FlowModel → Stmt →
    LoweredExpr → FlowModel -> Prop where
  /--
  Variable declaration statement. TODO: support more than one variable.

  Mirrors Dart's `declare`, which creates a new `ValueVersion` object for the variable. Here the new
  value version is the root labelled by the declaration's own AST path, so distinct declarations,
  including re-declarations of the same variable, get distinct versions.
  -/
  | declare π fm n T :
      ElabStmt π fm (.declare n T) (.declare ⟨n, T⟩ T)
        (fm.set (.var ⟨n, T⟩) (PromotionModel.declared (ValueVersion.root π)))
  /-- Expression statement. -/
  | exprStmt {π fm₀ e m em} :
      ElabExpr (0 :: π) fm₀ e m em →
      ElabStmt π fm₀ (.exprStmt e) m em.fm_after
  /-- If statement. -/
  | ifStmt {π fm₀ e₁ m₁ em₁ s₂ m₂ fm₂ s₃ m₃ fm₃} :
      ElabExpr (0 :: π) fm₀ e₁ m₁ em₁ →
      -- TODO: support dynamic downcast
      em₁.type = Γ.bool →
      ElabStmt (1 :: π) em₁.fm_true s₂ m₂ fm₂ →
      ElabStmt (2 :: π) em₁.fm_false s₃ m₃ fm₃ →
      ElabStmt π fm₀ (.ifStmt e₁ s₂ s₃) (.cond m₁ m₂ m₃ Γ.Null) (fm₂.join fm₃)
  /-- Block statement. -/
  | block {π fm₀ ss ms fm} :
      ElabStmts (0 :: π) fm₀ ss ms fm →
      ElabStmt π fm₀ (.block ss) (.block ms) fm

/--
Statement list elaboration rules.

A nonempty list is addressed by its cons cells: in `s :: ss` at path `π`, `s` is at `0 :: π` and
`ss` is at `1 :: π`.
-/
public inductive ElabStmts : AstPath → FlowModel → List Stmt →
    List (LoweredExpr) → FlowModel → Prop where
  | nil {π fm} : ElabStmts π fm [] [] fm
  | cons {π s ss fm₀ fm₁ fm m ms} :
      ElabStmt (0 :: π) fm₀ s m fm₁ →
      ElabStmts (1 :: π) fm₁ ss ms fm →
      ElabStmts π fm₀ (s :: ss) (m :: ms) fm

end

-- Theorems --

public theorem ElabExpr.boolInfo_onlyIf_bool {π} {fm : FlowModel} {e m} {em : ExprModel} :
    ElabExpr π fm e m em → em.fm_true ≠ em.fm_false → em.type = Γ.bool := by
  intro hDeriv hHasInfo
  induction hDeriv <;> simp_all

end FlowAnalysis
