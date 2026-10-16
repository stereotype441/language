module
public import DartSemantics.Resolve

/-!
# Facts about binding variables to cells

Lemmas about `LoweredExpr.resolve` and `LoweredExpr.bindVariables` (see `Resolve.lean`), for the
semantic typing judgment (see `SemanticTyping.lean`), which binds an expression's free variables to
cells before running it.

## Resolving and binding

*Resolving* (`LoweredExpr.resolve`, and `LoweredExpr.resolveBlock` for the elements of a block) is
the basic operation, for one variable `x` and one location `ℓ`. It replaces each reference to `x`
that isn't shadowed: `var x T` becomes `varAt x T ℓ`, and `variableSet x m'` becomes
`variableSetAt x ℓ m'`. `resolveBlock` stops at a declaration of `x`, which shadows it for the rest
of the block. The semantics resolves during execution: when a block declares `v`, the head step
allocates a cell for `v`, and resolves `v` to it in the rest of the block (see
`HeadStep.blockDeclare`).

*Binding* (`LoweredExpr.bindVariables`, and `LoweredExpr.bindBlock` for the elements of a block)
resolves each variable in a list of bindings in turn. It's for an expression's free variables (such
as formal parameters), which no enclosing block declares: they're bound once, before execution
starts, to cells allocated in the initial state, as if they had been declared around the
expression. That's why the semantic typing judgment, `safety`, and its corollaries talk about
`m.bindVariables bindings`.

So binding is resolving repeated, up front, for free variables, while resolving on its own is what a
declaration does at run time. Most of the lemmas here connect the two, so that the typing rule for a
block that declares a variable (`SemTyped.block_declare`) can treat the newly declared variable as
one more binding: resolving commutes with binding other variables (`resolveBlock_bindBlock`), and a
declaration shadows any binding of the variable it declares (`bindBlock_declare`).
-/

namespace DartLang

variable {τ : Type} [DartTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)

/--
Bind free variables to cells in the elements of a block, as `LoweredExpr.bindVariables` does for an
expression.
-/
@[expose]
public def LoweredExpr.bindBlock (bindings : List (Variable × Loc)) (ms : List LoweredExpr) :
    List LoweredExpr :=
  bindings.foldl (fun ms (x, ℓ) => LoweredExpr.resolveBlock x ℓ ms) ms

/--
Resolving a variable in an expression that isn't a declaration (`hm`) doesn't make it one
(`m.resolve x ℓ ≠ .declare v T sN`).
-/
public theorem LoweredExpr.resolve_ne_declare {m : LoweredExpr}
    (hm : ∀ v T sN, m ≠ .declare v T sN) (x : Variable) (ℓ : Loc) :
    ∀ v T sN, m.resolve x ℓ ≠ .declare v T sN := by
  intro v T sN h
  cases m with
  | var v' T' =>
    simp only [resolve] at h
    split at h <;> simp at h
  | declare v' T' sN' => exact hm v' T' sN' rfl
  | variableSet v' m' =>
    simp only [resolve] at h
    split at h <;> simp at h
  | _ => simp [resolve] at h

/--
Resolving a variable in a block that starts with anything other than a declaration (`hm`) resolves
it in that element and in the rest of the block.
-/
public theorem LoweredExpr.resolveBlock_cons_of_ne {m : LoweredExpr}
    (hm : ∀ v T sN, m ≠ .declare v T sN) (x : Variable) (ℓ : Loc) (ms : List LoweredExpr) :
    resolveBlock x ℓ (m :: ms) = m.resolve x ℓ :: resolveBlock x ℓ ms := by
  cases m with
  | declare v T sN => exact absurd rfl (hm v T sN)
  | _ => rfl

mutual

/-- Resolving two different variables (`hne`) gives the same result in either order. -/
public theorem LoweredExpr.resolve_comm {x y : Variable} {ℓ ℓ' : Loc} (hne : x ≠ y) :
    ∀ m : LoweredExpr, (m.resolve x ℓ).resolve y ℓ' = (m.resolve y ℓ').resolve x ℓ
  | .var v T => by
    by_cases hx : v = x
    · subst hx
      simp [resolve, hne]
    · by_cases hy : v = y
      · subst hy
        simp [resolve, hx]
      · simp [resolve, hx, hy]
  | .nullCheck m => by simp only [resolve, resolve_comm hne m]
  | .as m T => by simp only [resolve, resolve_comm hne m]
  | .is m T => by simp only [resolve, resolve_comm hne m]
  | .null => rfl
  | .declare _ _ _ => rfl
  | .cond m₁ m₂ m₃ T => by
    simp only [resolve, resolve_comm hne m₁, resolve_comm hne m₂, resolve_comm hne m₃]
  | .block ms => by simp only [resolve, resolveBlock_comm hne ms]
  | .propertyGet m p T => by simp only [resolve, resolve_comm hne m]
  | .variableSet v m => by
    by_cases hx : v = x
    · subst hx
      simp [resolve, hne, resolve_comm hne m]
    · by_cases hy : v = y
      · subst hy
        simp [resolve, hx, resolve_comm hne m]
      · simp [resolve, hx, hy, resolve_comm hne m]
  | .val _ => rfl
  | .throwing _ => rfl
  | .varAt _ _ _ => rfl
  | .seq m₁ m₂ => by simp only [resolve, resolve_comm hne m₁, resolve_comm hne m₂]
  | .variableSetAt _ _ m => by simp only [resolve, resolve_comm hne m]

/-- Resolving two different variables (`hne`) in a block gives the same result in either order. -/
public theorem LoweredExpr.resolveBlock_comm {x y : Variable} {ℓ ℓ' : Loc} (hne : x ≠ y) :
    ∀ ms : List LoweredExpr,
      resolveBlock y ℓ' (resolveBlock x ℓ ms) = resolveBlock x ℓ (resolveBlock y ℓ' ms)
  | [] => rfl
  | m :: ms => by
    by_cases hm : ∃ v T sN, m = .declare v T sN
    · obtain ⟨v, T, sN, rfl⟩ := hm
      by_cases hx : v = x
      · subst hx
        by_cases hy : v = y
        · exact absurd hy hne
        · simp [resolveBlock, hy]
      · by_cases hy : v = y
        · subst hy
          simp [resolveBlock, hx]
        · simp [resolveBlock, hx, hy, resolveBlock_comm hne ms]
    · have hm' : ∀ v T sN, m ≠ .declare v T sN := fun v T sN h => hm ⟨v, T, sN, h⟩
      rw [resolveBlock_cons_of_ne hm', resolveBlock_cons_of_ne (resolve_ne_declare hm' _ _),
        resolveBlock_cons_of_ne hm', resolveBlock_cons_of_ne (resolve_ne_declare hm' _ _),
        resolve_comm hne m, resolveBlock_comm hne ms]

end

/--
Resolving a variable `x` commutes with binding variables that don't include it (`h`), in a block.
-/
public theorem LoweredExpr.resolveBlock_bindBlock {x : Variable} {ℓ : Loc}
    {bindings : List (Variable × Loc)} (h : ∀ b ∈ bindings, b.1 ≠ x) (ms : List LoweredExpr) :
    resolveBlock x ℓ (bindBlock bindings ms) = bindBlock bindings (resolveBlock x ℓ ms) := by
  induction bindings generalizing ms with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨y, ℓ'⟩ := b
    simp only [bindBlock, List.foldl_cons] at ih ⊢
    rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    rw [resolveBlock_comm (h (y, ℓ') (List.mem_cons_self ..))]

/-- Binding variables in the null literal leaves it alone. -/
@[simp]
public theorem LoweredExpr.bindVariables_null (bindings : List (Variable × Loc)) :
    (LoweredExpr.null : LoweredExpr).bindVariables bindings = .null := by
  induction bindings with
  | nil => rfl
  | cons b bs ih => exact ih

/--
Binding variables in a declaration leaves it alone. (Once declarations can have initializers,
binding will resolve the variable references in the initializer instead.)
-/
@[simp]
public theorem LoweredExpr.bindVariables_declare (bindings : List (Variable × Loc)) {v : Variable}
    {T : τ} {sN : Bool} :
    (LoweredExpr.declare v T sN).bindVariables bindings = .declare v T sN := by
  induction bindings with
  | nil => rfl
  | cons b bs ih => exact ih

/--
Binding variables in a reference to a variable `x` resolves it to the variable's cell `ℓ`, if any
(`bindings.lookup x = some ℓ`), giving `.varAt x T ℓ`; otherwise it leaves it alone.
-/
public theorem LoweredExpr.bindVariables_var (bindings : List (Variable × Loc)) (x : Variable)
    (T : τ) :
    (LoweredExpr.var x T).bindVariables bindings =
      match bindings.lookup x with
      | some ℓ => .varAt x T ℓ
      | none => .var x T := by
  induction bindings with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨y, ℓ⟩ := b
    by_cases h : x = y
    · subst h
      simp only [bindVariables, List.foldl_cons, resolve, ite_true, List.lookup_cons_self]
      clear ih
      induction bs with
      | nil => rfl
      | cons b bs ih => exact ih
    · have hb : (x == y) = false := by simpa using h
      simp only [bindVariables, List.foldl_cons, resolve, h, ite_false, List.lookup, hb]
      exact ih

/-- Binding variables in a variable reference that is already resolved leaves it alone. -/
@[simp]
public theorem LoweredExpr.bindVariables_varAt (bindings : List (Variable × Loc)) {x : Variable}
    {T : τ} {ℓ : Loc} :
    (LoweredExpr.varAt x T ℓ).bindVariables bindings = .varAt x T ℓ := by
  induction bindings with
  | nil => rfl
  | cons b bs ih => exact ih

/--
Binding variables in an assignment whose target is already resolved binds them in its right-hand
side.
-/
@[simp]
public theorem LoweredExpr.bindVariables_variableSetAt (bindings : List (Variable × Loc))
    {x : Variable} {ℓ : Loc} (m : LoweredExpr) :
    (LoweredExpr.variableSetAt x ℓ m).bindVariables bindings =
      .variableSetAt x ℓ (m.bindVariables bindings) := by
  induction bindings generalizing m with
  | nil => rfl
  | cons b bs ih => exact ih _

/--
Binding variables in an assignment to a variable `x` binds them in its right-hand side, and
resolves its target to the variable's cell `ℓ`, if any (`bindings.lookup x = some ℓ`), giving
`.variableSetAt x ℓ …`; otherwise it leaves the target alone.
-/
public theorem LoweredExpr.bindVariables_variableSet (bindings : List (Variable × Loc))
    (x : Variable) (m : LoweredExpr) :
    (LoweredExpr.variableSet x m).bindVariables bindings =
      match bindings.lookup x with
      | some ℓ => .variableSetAt x ℓ (m.bindVariables bindings)
      | none => .variableSet x (m.bindVariables bindings) := by
  induction bindings generalizing m with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨y, ℓ⟩ := b
    by_cases h : x = y
    · subst h
      simp only [bindVariables, List.foldl_cons, resolve, ite_true, List.lookup_cons_self]
      exact bindVariables_variableSetAt bs _
    · have hb : (x == y) = false := by simpa using h
      simp only [bindVariables, List.foldl_cons, resolve, h, ite_false, List.lookup, hb]
      exact ih _

/-- Binding variables in a null check binds them in its operand. -/
@[simp]
public theorem LoweredExpr.bindVariables_nullCheck (bindings : List (Variable × Loc))
    (m : LoweredExpr) :
    m.nullCheck.bindVariables bindings = (m.bindVariables bindings).nullCheck := by
  induction bindings generalizing m with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- Binding variables in a cast binds them in its operand. -/
@[simp]
public theorem LoweredExpr.bindVariables_as (bindings : List (Variable × Loc)) (m : LoweredExpr)
    (T : τ) : (m.as T).bindVariables bindings = (m.bindVariables bindings).as T := by
  induction bindings generalizing m with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- Binding variables in an is-expression binds them in its operand. -/
@[simp]
public theorem LoweredExpr.bindVariables_is (bindings : List (Variable × Loc)) (m : LoweredExpr)
    (T : τ) : (m.is T).bindVariables bindings = (m.bindVariables bindings).is T := by
  induction bindings generalizing m with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- Binding variables in a conditional binds them in its subexpressions. -/
@[simp]
public theorem LoweredExpr.bindVariables_cond (bindings : List (Variable × Loc))
    (m₁ m₂ m₃ : LoweredExpr) (T : τ) :
    (LoweredExpr.cond m₁ m₂ m₃ T).bindVariables bindings =
      .cond (m₁.bindVariables bindings) (m₂.bindVariables bindings) (m₃.bindVariables bindings)
        T := by
  induction bindings generalizing m₁ m₂ m₃ with
  | nil => rfl
  | cons b bs ih => exact ih _ _ _

/-- Binding variables in a property extraction binds them in its receiver. -/
@[simp]
public theorem LoweredExpr.bindVariables_propertyGet (bindings : List (Variable × Loc))
    (m : LoweredExpr) (p : Property (τ := τ)) (T : τ) :
    (m.propertyGet p T).bindVariables bindings = (m.bindVariables bindings).propertyGet p T := by
  induction bindings generalizing m with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- Binding variables in a block binds them in its elements. -/
@[simp]
public theorem LoweredExpr.bindVariables_block (bindings : List (Variable × Loc))
    (ms : List LoweredExpr) :
    (LoweredExpr.block ms).bindVariables bindings = .block (bindBlock bindings ms) := by
  induction bindings generalizing ms with
  | nil => rfl
  | cons b bs ih => exact ih _

/-- Binding variables in an empty block leaves it empty. -/
@[simp]
public theorem LoweredExpr.bindBlock_nil (bindings : List (Variable × Loc)) :
    bindBlock bindings ([] : List LoweredExpr) = [] := by
  induction bindings with
  | nil => rfl
  | cons b bs ih => exact ih

/--
Binding variables in a block that starts with a declaration of `v` binds the others
(`bindings.filter (fun b => b.1 ≠ v)`) in the rest of the block: the declaration shadows any
binding of `v`.
-/
public theorem LoweredExpr.bindBlock_declare (bindings : List (Variable × Loc)) (v : Variable)
    (T : τ) (sN : Bool) (ms : List LoweredExpr) :
    bindBlock bindings (.declare v T sN :: ms) =
      .declare v T sN :: bindBlock (bindings.filter (fun b => b.1 ≠ v)) ms := by
  induction bindings generalizing ms with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨y, ℓ⟩ := b
    by_cases h : v = y
    · subst h
      simp only [bindBlock, List.foldl_cons, resolveBlock, ite_true, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
      exact ih ms
    · have h' : y ≠ v := Ne.symm h
      simp only [bindBlock, List.foldl_cons, resolveBlock, h, ite_false, ne_eq, h',
        not_false_eq_true, decide_true, List.filter_cons_of_pos]
      exact ih _

/--
Binding variables in a block that starts with anything other than a declaration (`hm`) binds them
in that element and in the rest of the block.

Together with `bindBlock_nil` and `bindBlock_declare`, this covers every block: a declaration later
in the block is handled by `bindBlock_declare` once the rest of the block starts with it.
-/
public theorem LoweredExpr.bindBlock_cons (bindings : List (Variable × Loc)) {m : LoweredExpr}
    (hm : ∀ v T sN, m ≠ .declare v T sN) (ms : List LoweredExpr) :
    bindBlock bindings (m :: ms) = m.bindVariables bindings :: bindBlock bindings ms := by
  induction bindings generalizing m ms with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨y, ℓ⟩ := b
    simp only [bindBlock, List.foldl_cons, resolveBlock_cons_of_ne hm] at ih ⊢
    exact ih (resolve_ne_declare hm _ _) _

/--
Binding variables in an expression that isn't a declaration (`hm`) doesn't make it one
(`m.bindVariables bindings ≠ .declare v T sN`).
-/
public theorem LoweredExpr.bindVariables_ne_declare (bindings : List (Variable × Loc))
    {m : LoweredExpr} (hm : ∀ v T sN, m ≠ .declare v T sN) :
    ∀ v T sN, m.bindVariables bindings ≠ .declare v T sN := by
  induction bindings generalizing m with
  | nil => exact hm
  | cons b bs ih => exact ih (resolve_ne_declare hm _ _)

/--
Removing the bindings of `v` from a list of bindings (`bindings.filter (fun b => b.1 ≠ v)`) doesn't
change the cell that it binds any other variable `x` (`h`) to.
-/
public theorem lookup_filter_ne {α : Type} {bindings : List (Variable × α)} {v x : Variable}
    (h : x ≠ v) : (bindings.filter (fun b => b.1 ≠ v)).lookup x = bindings.lookup x := by
  induction bindings with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨y, a⟩ := b
    by_cases hy : y = v
    · subst hy
      have hxy : (x == y) = false := by simpa using h
      simpa [List.lookup, hxy] using ih
    · by_cases hxy : x = y
      · subst hxy
        simp [List.lookup, hy]
      · have hxy' : (x == y) = false := by simpa using hxy
        simpa [List.lookup, hy, hxy'] using ih

/--
Adding a binding of `v` to the front of a list of bindings (`(v, a) :: bindings`) doesn't change the
cell that it binds any other variable `x` (`h`) to.
-/
public theorem lookup_cons_ne {α : Type} {bindings : List (Variable × α)} {v x : Variable} {a : α}
    (h : x ≠ v) : ((v, a) :: bindings).lookup x = bindings.lookup x := by
  have hxv : (x == v) = false := by simpa using h
  simp [List.lookup, hxv]

end DartLang
