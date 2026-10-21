module
public import DartSemantics.Bind
public import DartSemantics.PrimitiveLaws

/-!
# Semantic typing

A *semantic* typing judgment for `LoweredExpr`s, defined with the program logic. An expression is
semantically well typed in a context if, whenever it starts running in a state where everything
the context promises holds:
- it can't get stuck, and
- if it completes normally, its value satisfies the expression's static type (that is, the value's
  dynamic type is a subtype of it; see `interpVal`), and everything that the context promises for
  afterwards holds.

The typing rules say that an expression *is semantically well typed with type `T`* (`SemTyped`).
That's a claim about how the expression behaves when it runs, not just about the static type it is
annotated with. (The Iris literature calls a typing judgment defined like this a *logical
relation*. The README's "Reading the Iris parts" section explains the Iris notation used here.)

The judgment is *flow-sensitive*, as flow analysis is: a context records what is known about
variables and fields, and evaluating an expression can add to that knowledge. For a condition, what
is known afterwards can depend on whether it evaluated to `true` or `false`.

The facts after an expression are a *guarantee*: they hold afterwards, but other facts may hold
too. So different rules for the same expression can guarantee different facts (for example,
`SemTyped.nullCheck` and the more specific `SemTyped.nullCheck_var`), and weakening
(`SemTyped.weaken`) can drop facts from a guarantee.

`Compat.lean` proves one *compatibility lemma* for each kind of expression: a typing rule, proved
sound with respect to the semantics. `Safety.lean` derives the safety theorem from adequacy: an
expression that is semantically well typed doesn't get stuck. Since a promotion check that fails
gets stuck when `SemanticParams.promotionChecks` is `PromotionChecks.verify`, this includes the
guarantee that every promotion it relies on is sound.

Everything is stated for an arbitrary type representation `τ`, assuming only the laws in
`TypeLaws`, and for every choice of `SemanticParams`.

## Connection to flow analysis

Contexts (`Ctx`, lists of `Fact`s) are deliberately simpler than flow analysis's models: they
record only what a running program can rely on. The intended next step is to translate each flow
model to the facts it implies (an ordinary Lean function), and prove that the `LoweredExpr` that
flow analysis produces for each construct is semantically well typed, from the facts of the model
before it to the facts of the model after it. That is the soundness theorem for flow analysis.
Keeping the translation separate keeps the program logic out of reasoning about models (joins,
demotions, and so on), and keeps this file independent of how flow analysis represents them.

## Local variables' cells

A local variable's cell can change (an assignment stores a new value in it), so a context's
promises about a variable can't be backed by a persistent points-to for its cell. Instead, the
judgment owns the cells of the variables in scope exclusively (`interpEnv`), and describes their
contents with an *environment* (`Env`), a function from variables to cells. The facts
(`interpFact`) are persistent statements about the environment. Until the semantics has closures
or `async`, a local variable's cell is never shared, so exclusive ownership is enough: no iris
invariants or ghost state are needed.

The semantics doesn't have assignments to instance variables yet, so a fact about an instance
variable is still backed by persistent points-tos for its cell and its object's own cell.

## Simplifications

A property read is only typed when its receiver is a variable `x`, and the context promises that
`x` refers to an object with an instance variable of that name (`Fact.field`). Reading a property
whose getter is user code, or of an object that isn't held in a variable, waits for the semantics
to have class declarations and calls (see `SemanticParams.getterImpl`).
-/

namespace DartSemantics

open DartLang Iris Iris.BI Iris.ProgramLogic Iris.Std

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

local notation "Variable" => Variable (τ := τ)
local notation "Property" => Property (τ := τ)
local notation "Value" => Value (τ := τ)
local notation "LoweredExpr" => LoweredExpr (τ := τ)
local notation "Cell" => Cell (τ := τ)

variable (τ) in
/--
Laws about the type representation that the typing rules rely on. They hold in Dart, and for
`SimpleType` (see the tests), but don't follow from `DartTypeRepr`, whose special types are
otherwise unrelated constants.
-/
public structure TypeLaws : Prop where
  /-- `bool` isn't nullable, so the null object isn't a boolean (for conditionals). -/
  not_null_le_bool : ¬ Γ.Null ≤ Γ.bool
  /-- A non-nullable subtype of `T` is a subtype of `NonNull T` (for null checks). -/
  le_nonNull {S T : τ} : ¬ Γ.Null ≤ S → S ≤ T → S ≤ Γ.NonNull T

/--
What the typing rules need to know about a value whose dynamic type is `S`, besides `S` itself: if
the value is an object (other than the null object and booleans), its class isn't nullable, and
isn't a subtype of `bool`. (In Dart, `bool` can't be extended or implemented.)
-/
@[expose]
public def ValOk : Value → τ → Prop
  | .obj _, S => ¬ Γ.Null ≤ S ∧ ¬ S ≤ Γ.bool
  | _, _ => True

/--
A fact that a context records: what is known about a variable at a point in the program.
-/
public inductive Fact where
  /--
  Variable `x` is in scope: it is bound to a cell. (This survives joins that lose what `x` holds:
  after `int x; if (b) { x = 1; }`, `x` may not be assigned, but it can still be assigned to.)
  -/
  | decl (x : Variable)
  /--
  Variable `x` is in scope, and hasn't been assigned (its cell is uninitialized). A `final`
  variable can only be assigned when this holds.
  -/
  | uninit (x : Variable)
  /-- Variable `x` holds a value that satisfies `T`. -/
  | var (x : Variable) (T : τ)
  /--
  Following the *property path* `path` (a list of instance variable names, in order from `x`
  outward, like flow analysis's promotion keys) from the object that variable `x` refers to reaches
  an instance variable holding a value that satisfies `T`. For example, `.field x ["_y", "_z"] T`
  says that `x._y._z` is an instance variable whose value satisfies `T`. (An empty path would just
  mean what `Fact.var x T` means; see `Fact.atPath`.)
  -/
  | field (x : Variable) (path : List String) (T : τ)
  deriving DecidableEq

local notation "Fact" => Fact (τ := τ)

/--
The fact that the value reached by following property path `path` from variable `x` satisfies `T`:
`Fact.var x T` for the empty path, and `Fact.field x path T` otherwise. This lets rules about
variables and about their properties be stated once.
-/
@[expose]
public def Fact.atPath (x : Variable) : List String → τ → Fact
  | [], T => .var x T
  | path@(_ :: _), T => .field x path T

/-- The variable that a fact is about. -/
@[expose]
public def Fact.variable : Fact → Variable
  | .decl x => x
  | .uninit x => x
  | .var x _ => x
  | .field x _ _ => x

/-- A context: facts that hold at a point in the program (not necessarily all of them). -/
public abbrev Ctx := List Fact

local notation "Ctx" => Ctx (τ := τ)

/--
Forget the facts about variable `v` (when a declaration of `v` shadows it, or it goes out of
scope).
-/
@[expose]
public def Ctx.forget (Δ : Ctx) (v : Variable) : Ctx := Δ.filter (fun f => f.variable ≠ v)

/--
The facts guaranteed after a condition, as a function of its value: `Δt` if it evaluated to `true`,
and `Δf` otherwise.
-/
@[expose]
public def Ctx.byCondition (Δt Δf : Ctx) : Value → Ctx
  | .bool true => Δt
  | _ => Δf

omit Γ in
/-- After a condition that evaluated to `true`, the facts guaranteed are `Δt`. -/
@[simp]
public theorem Ctx.byCondition_true (Δt Δf : Ctx) : Ctx.byCondition Δt Δf (.bool true) = Δt := rfl

omit Γ in
/-- After a condition that evaluated to `false`, the facts guaranteed are `Δf`. -/
@[simp]
public theorem Ctx.byCondition_false (Δt Δf : Ctx) : Ctx.byCondition Δt Δf (.bool false) = Δf :=
  rfl

/--
An environment: the contents of the cells of the variables in scope (see the module doc).

It's a total function (`Variable → Cell`, not `Variable → Option Cell`), although only the
variables in scope have cells. That's harmless, because its values at other variables never
matter:
- every use of an environment is guarded by a lookup in `bindings`: `interpEnv` only looks at the
  variables that `bindings` binds, and `interpFact` looks at `env x` only together with
  `bindings.lookup x = some ℓ`. Since `SemTyped` quantifies over every environment, the typing
  rules can't depend on its values at other variables either; and
- the one place that builds an environment from scratch (`envOf`, which `safety` uses to start
  from a state) reads each bound variable's cell from the state, and picks `.uninit`, arbitrarily,
  for every other variable.
-/
public abbrev Env := Variable → Cell

local notation "Env" => Env (τ := τ)

/-- The environment `env`, with variable `x`'s cell holding `c`. -/
@[expose]
public def Env.set (env : Env) (x : Variable) (c : Cell) : Env :=
  fun y => if y = x then c else env y

/-- In `env.set x c`, `x`'s cell holds `c`. -/
@[simp]
public theorem Env.set_self (env : Env) (x : Variable) (c : Cell) : env.set x c x = c := by
  simp [Env.set]

/-- In `env.set x c`, the cell of a variable `y` other than `x` (`h`) holds what it did in `env`. -/
public theorem Env.set_ne {env : Env} {x y : Variable} (h : y ≠ x) (c : Cell) :
    env.set x c y = env y := by
  simp [Env.set, h]

/--
Setting a variable's cell to what it already holds doesn't change an environment
(`env.set x (env x) = env`).
-/
public theorem Env.set_eq_self (env : Env) (x : Variable) : env.set x (env x) = env := by
  funext y
  by_cases h : y = x
  · subst h
    simp
  · exact Env.set_ne h _

section Interp

variable {hlc : HasLC} {GF : BundledGFunctors} [DartGS τ hlc GF]

/--
The value interpretation of type `T`: the values that *satisfy* `T`, that is, whose dynamic types
are subtypes of `T` (see the README's documentation conventions), and that also meet `ValOk`, which
the typing rules need. The docs below say "satisfies `T`" for this.
-/
@[expose, reducible]
public def interpVal (T : τ) (v : Value) : IProp GF :=
  iprop(∃ S, HasDynamicType v S ∗ ⌜S ≤ T ∧ ValOk v S⌝)

/-- `interpVal T v` is persistent: it's built from persistent knowledge of `v`'s dynamic type. -/
public instance interpVal_persistent (T : τ) (v : Value) :
    Persistent (interpVal (GF := GF) T v) := by
  unfold interpVal
  infer_instance

/--
Ownership of the cell of a local variable at `ℓ`, holding `c`, which must be a variable's cell (a
value, or uninitialized), not an object's own cell.
-/
@[expose, reducible]
public def interpCell (ℓ : Loc) (c : Cell) : IProp GF :=
  iprop(⌜∀ C fs, c ≠ .object C fs⌝ ∗ ℓ ↦ c)

/--
The interpretation of an environment: exclusive ownership of the cell of each variable in
`bindings`, holding what `env` says. (The judgment only uses lists of bindings that bind each
variable at most once; see `SemTyped`.)
-/
@[expose]
public def interpEnv : List (Variable × Loc) → Env → IProp GF
  | [], _ => iprop(emp)
  | (x, ℓ) :: bs, env => iprop(interpCell ℓ (env x) ∗ interpEnv bs env)

/--
Following property path `path` from value `v` reaches value `w`: for the empty path, `w` is `v`;
for `name :: path`, `v` refers to an object whose instance variable `name` holds a value `v'`, and
following `path` from `v'` reaches `w`. The object's own cell and the instance variable's cell are
owned persistently, since they never change.
-/
@[expose, reducible]
public def interpFieldPath : List String → Value → Value → IProp GF
  | [], v, w => iprop(⌜v = w⌝)
  | name :: path, v, w => iprop(∃ ℓo C fs ℓf v',
      ⌜v = .obj ℓo ∧ fs.lookup name = some ℓf⌝ ∗
      ℓo ↦{.discard} (.object C fs : Cell) ∗ ℓf ↦{.discard} (.val v' : Cell) ∗
      interpFieldPath path v' w)

/-- `interpFieldPath path v w` is persistent: it's built from persistent points-tos. -/
public instance interpFieldPath_persistent (path : List String) (v w : Value) :
    Persistent (interpFieldPath (GF := GF) path v w) := by
  induction path generalizing v with
  | nil => unfold interpFieldPath; infer_instance
  | cons name path ih => unfold interpFieldPath; infer_instance

omit Γ in
/--
Following the concatenation of two property paths from `v` reaches `w`
(`interpFieldPath (p₁ ++ p₂) v w`) if and only if following `p₁` from `v` reaches some `u`, and
following `p₂` from `u` reaches `w` (`∃ u, interpFieldPath p₁ v u ∗ interpFieldPath p₂ u w`).
-/
public theorem interpFieldPath_append (p₁ p₂ : List String) (v w : Value) :
    interpFieldPath (GF := GF) (p₁ ++ p₂) v w ⊣⊢
      ∃ u, interpFieldPath p₁ v u ∗ interpFieldPath p₂ u w := by
  induction p₁ generalizing v with
  | nil =>
    simp only [List.nil_append, interpFieldPath]
    constructor
    · iintro H
      iexists v
      isplitr
      · ipureintro
        rfl
      · iexact H
    · iintro ⟨%u, %h, H⟩
      subst h
      iexact H
  | cons name p ih =>
    simp only [List.cons_append, interpFieldPath]
    constructor
    · iintro ⟨%ℓo, %C, %fs, %ℓf, %v', %h, Ho, Hf, H⟩
      icases (ih v').1 $$ H with ⟨%u, H₁, H₂⟩
      iexists u
      isplitl [Ho Hf H₁]
      · iexists ℓo, C, fs, ℓf, v'
        isplitr
        · ipureintro
          exact h
        isplitl [Ho]
        · iexact Ho
        isplitl [Hf]
        · iexact Hf
        · iexact H₁
      · iexact H₂
    · iintro ⟨%u, ⟨%ℓo, %C, %fs, %ℓf, %v', %h, Ho, Hf, H₁⟩, H₂⟩
      iexists ℓo, C, fs, ℓf, v'
      isplitr
      · ipureintro
        exact h
      isplitl [Ho]
      · iexact Ho
      isplitl [Hf]
      · iexact Hf
      · iapply (ih v').2
        iexists u
        isplitl [H₁]
        · iexact H₁
        · iexact H₂

omit Γ in
/--
Following a property path is deterministic: if following `path` from `v` reaches both `w₁` and
`w₂`, then they're the same (`w₁ = w₂`). The objects' own cells and the instance variables' cells
along the way never change, so two walks see the same cells.
-/
public theorem interpFieldPath_agree (path : List String) {v w₁ w₂ : Value} :
    interpFieldPath (GF := GF) path v w₁ ∗ interpFieldPath path v w₂ ⊢ ⌜w₁ = w₂⌝ := by
  induction path generalizing v with
  | nil =>
    simp only [interpFieldPath]
    iintro ⟨%h₁, %h₂⟩
    ipureintro
    exact h₁.symm.trans h₂
  | cons name path ih =>
    simp only [interpFieldPath]
    iintro ⟨⟨%ℓo, %C, %fs, %ℓf, %v₁, ⟨%hv, %hf⟩, Ho, Hf, H⟩,
      ⟨%ℓo', %C', %fs', %ℓf', %v₂, ⟨%hv', %hf'⟩, Ho', Hf', H'⟩⟩
    obtain rfl : ℓo = ℓo' := by rw [hv] at hv'; exact Value.obj.inj hv'
    ihave %ho : ⌜(.object C fs : Cell) = .object C' fs'⌝ $$ [Ho Ho']
    · iapply pointsTo_agree
      isplitl [Ho]
      · iexact Ho
      · iexact Ho'
    obtain ⟨rfl, rfl⟩ := Cell.object.inj ho
    obtain rfl : ℓf = ℓf' := by rw [hf] at hf'; exact Option.some.inj hf'
    ihave %hw : ⌜(.val v₁ : Cell) = .val v₂⌝ $$ [Hf Hf']
    · iapply pointsTo_agree
      isplitl [Hf]
      · iexact Hf
      · iexact Hf'
    obtain rfl := Cell.val.inj hw
    iapply ih
    isplitl [H]
    · iexact H
    · iexact H'

/--
The interpretation of a fact, given the cells that variables are bound to (`bindings`), and what
they hold (`env`). The cells of instance variables, and objects' own cells, are owned
persistently: they never change.
-/
@[expose, reducible]
public def interpFact (bindings : List (Variable × Loc)) (env : Env) : Fact → IProp GF
  | .decl x => iprop(⌜∃ ℓ, bindings.lookup x = some ℓ⌝)
  | .uninit x => iprop(⌜∃ ℓ, bindings.lookup x = some ℓ ∧ env x = .uninit⌝)
  | .var x T => iprop(∃ ℓ v, ⌜bindings.lookup x = some ℓ ∧ env x = .val v⌝ ∗ interpVal T v)
  | .field x path T => iprop(∃ ℓ v w, ⌜bindings.lookup x = some ℓ ∧ env x = .val v⌝ ∗
      interpFieldPath path v w ∗ interpVal T w)

/--
Each fact's meaning (`interpFact`) is persistent, so a context's facts can be relied on any number
of times.
-/
public instance interpFact_persistent (bindings : List (Variable × Loc)) (env : Env) (f : Fact) :
    Persistent (interpFact (GF := GF) bindings env f) := by
  cases f <;> unfold interpFact <;> infer_instance

/-- The interpretation of a context: every fact in it holds. -/
@[expose]
public def interpCtx (bindings : List (Variable × Loc)) (env : Env) (Δ : Ctx) : IProp GF :=
  iprop(□ ∀ f, ⌜f ∈ Δ⌝ → interpFact bindings env f)

/-- A context's meaning (`interpCtx`) is persistent, by its `□` (persistently) modality. -/
public instance interpCtx_persistent (bindings : List (Variable × Loc)) (env : Env) (Δ : Ctx) :
    Persistent (interpCtx (GF := GF) bindings env Δ) := by
  unfold interpCtx
  infer_instance

/--
What an expression of static type `T` promises when it completes with outcome `o`: if it completes
normally with value `v`, then `v` satisfies `T`, and for some environment `env'` (what the
variables' cells hold afterwards), the cells are owned, and the facts `Δa v` hold. If it throws,
nothing.
-/
@[expose]
public def interpOutcome (bindings : List (Variable × Loc)) (T : τ) (Δa : Value → Ctx) :
    DartLang.Outcome (τ := τ) → IProp GF
  | .normal v => iprop(∃ env', interpEnv bindings env' ∗ interpVal T v ∗
      interpCtx bindings env' (Δa v))
  | .throwing _ => iprop(True)

variable [SemanticParams τ]

variable (GF) in
/--
The semantic typing judgment `SemTyped Δb m T Δa`: whatever cells the variables in scope are bound
to (`bindings`, which binds each variable at most once), and whatever those cells hold (`env`), if
the cells are owned and the facts in `Δb` hold before, then running `m` doesn't get stuck, and if
it completes normally with value `v`, then `v` satisfies `T`, and afterwards the cells are owned
and the facts `Δa v` hold.
-/
@[expose]
public def SemTyped (Δb : Ctx) (m : LoweredExpr) (T : τ) (Δa : Value → Ctx) : Prop :=
  ∀ bindings, (bindings.map (·.1)).Nodup → ∀ env,
    interpEnv (GF := GF) bindings env ∗ interpCtx bindings env Δb ⊢
      WP (m.bindVariables bindings) {{ o, interpOutcome bindings T Δa o }}

/-! ### The value interpretation -/

omit [SemanticParams τ] in
/-- A value that satisfies `T` also satisfies every supertype `T'` of `T` (`h`). -/
public theorem interpVal_mono {T T' : τ} {v : Value} (h : T ≤ T') :
    interpVal (GF := GF) T v ⊢ interpVal T' v := by
  unfold interpVal
  iintro ⟨%S, #Hty, %hS, %hok⟩
  iexists S
  isplitr
  · iexact Hty
  · ipureintro
    exact ⟨le_trans hS h, hok⟩

omit [SemanticParams τ] in
/-- The null object satisfies every supertype `T` of `Null` (`h`). -/
public theorem interpVal_null {T : τ} (h : Γ.Null ≤ T) : ⊢ interpVal (GF := GF) T .null := by
  unfold interpVal
  iexists Γ.Null
  isplitr
  · iapply HasDynamicType.null
  · ipureintro
    exact ⟨h, trivial⟩

omit [SemanticParams τ] in
/-- A boolean `b` satisfies every supertype `T` of `bool` (`h`). -/
public theorem interpVal_bool {T : τ} (b : Bool) (h : Γ.bool ≤ T) :
    ⊢ interpVal (GF := GF) T (.bool b) := by
  unfold interpVal
  iexists Γ.bool
  isplitr
  · iapply HasDynamicType.bool
  · ipureintro
    exact ⟨h, trivial⟩

omit [SemanticParams τ] in
/-- A value that satisfies `bool` is a boolean (`∃ b, v = .bool b`). -/
public theorem interpVal_bool_inv (L : TypeLaws τ) {v : Value} :
    interpVal (GF := GF) Γ.bool v ⊢ ⌜∃ b, v = .bool b⌝ := by
  unfold interpVal
  cases v with
  | null =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, %hS, -⟩
    subst h
    exact absurd hS L.not_null_le_bool
  | bool b =>
    iintro -
    ipureintro
    exact ⟨b, rfl⟩
  | obj ℓ =>
    iintro ⟨%S, -, %hS, %hok⟩
    exact absurd hS hok.2
  | error e =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim
  | cont k =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim

omit [SemanticParams τ] in
/-- A value other than the null object (`hv`) that satisfies `T` also satisfies `NonNull T`. -/
public theorem interpVal_nonNull (L : TypeLaws τ) {T : τ} {v : Value} (hv : v ≠ .null) :
    interpVal (GF := GF) T v ⊢ interpVal (Γ.NonNull T) v := by
  unfold interpVal
  cases v with
  | null => exact absurd rfl hv
  | bool b =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, %hS, %hok⟩
    subst h
    iexists Γ.bool
    isplitr
    · ipureintro
      rfl
    · ipureintro
      exact ⟨L.le_nonNull L.not_null_le_bool hS, hok⟩
  | obj ℓ =>
    iintro ⟨%S, #Hty, %hS, %hok⟩
    iexists S
    isplitr
    · iexact Hty
    · ipureintro
      exact ⟨L.le_nonNull hok.1 hS, hok⟩
  | error e =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim
  | cont k =>
    simp only [HasDynamicType]
    iintro ⟨%S, %h, -⟩
    exact h.elim

/-! ### Contexts -/

omit [SemanticParams τ] in
/--
A fact about `x` only depends on the cell that `x` is bound to, and what it holds: `f` holds for
`bindings'` and `env'` if it holds for `bindings` and `env`, and:
- `bindings` and `bindings'` bind `f`'s variable to the same cell (`h`); and
- `env` and `env'` agree on what that cell holds (`he`).
-/
public theorem interpFact_congr {bindings bindings' : List (Variable × Loc)} {env env' : Env}
    {f : Fact} (h : bindings.lookup f.variable = bindings'.lookup f.variable)
    (he : env f.variable = env' f.variable) :
    interpFact (GF := GF) bindings env f ⊢ interpFact bindings' env' f := by
  cases f <;> simp only [Fact.variable] at h he <;> simp only [interpFact, h, he] <;> exact .rfl

omit [SemanticParams τ] in
/-- If a context `Δ₀` holds, every context `Δ` with fewer facts (`h`) holds too. -/
public theorem interpCtx_mono {bindings : List (Variable × Loc)} {env : Env} {Δ Δ₀ : Ctx}
    (h : ∀ f ∈ Δ, f ∈ Δ₀) : interpCtx (GF := GF) bindings env Δ₀ ⊢ interpCtx bindings env Δ := by
  unfold interpCtx
  iintro #H
  imodintro
  iintro %f %hf
  iapply H
  ipureintro
  exact h f hf

omit [SemanticParams τ] in
/-- A fact `f` in a context `Δ` (`h`) holds if the whole context holds. -/
public theorem interpCtx_elim {bindings : List (Variable × Loc)} {env : Env} {Δ : Ctx} {f : Fact}
    (h : f ∈ Δ) : interpCtx (GF := GF) bindings env Δ ⊢ interpFact bindings env f := by
  unfold interpCtx
  iintro #H
  iapply H
  ipureintro
  exact h

omit [SemanticParams τ] in
/-- The empty context promises nothing. -/
public theorem interpCtx_nil (bindings : List (Variable × Loc)) (env : Env) :
    ⊢ interpCtx (GF := GF) bindings env ([] : Ctx) := by
  unfold interpCtx
  imodintro
  iintro %f %hf
  exact absurd hf List.not_mem_nil

omit [SemanticParams τ] in
/--
A context holds (`interpCtx bindings env (f :: Δ)`) if one of its facts holds
(`interpFact bindings env f`) and the rest of it holds (`interpCtx bindings env Δ`).
-/
public theorem interpCtx_cons {bindings : List (Variable × Loc)} {env : Env} {f : Fact} {Δ : Ctx} :
    interpFact (GF := GF) bindings env f ∗ interpCtx bindings env Δ ⊢
      interpCtx bindings env (f :: Δ) := by
  unfold interpCtx
  iintro ⟨#Hf, #H⟩
  imodintro
  iintro %f' %hf'
  rcases List.mem_cons.1 hf' with rfl | h
  · iexact Hf
  · iapply H
    ipureintro
    exact h

omit [SemanticParams τ] in
/--
A context only depends on the cells that the variables it has facts about are bound to, and what
they hold: `Δ` holds for `bindings'` and `env'` if it holds for `bindings` and `env`, and, for each
of its facts `f`:
- `bindings` and `bindings'` bind `f`'s variable to the same cell (`h`); and
- `env` and `env'` agree on what that variable's cell holds (`he`).
-/
public theorem interpCtx_congr {bindings bindings' : List (Variable × Loc)} {env env' : Env}
    {Δ : Ctx} (h : ∀ f ∈ Δ, bindings.lookup f.variable = bindings'.lookup f.variable)
    (he : ∀ f ∈ Δ, env f.variable = env' f.variable) :
    interpCtx (GF := GF) bindings env Δ ⊢ interpCtx bindings' env' Δ := by
  unfold interpCtx
  iintro #H
  imodintro
  iintro %f %hf
  iapply interpFact_congr (h f hf) (he f hf)
  iapply H
  ipureintro
  exact hf

/-! ### Environments -/

omit Γ [SemanticParams τ] in
/--
The interpretation of an environment only depends on what it says about the variables bound: it's
the same for `env` and `env'` if they agree on every variable in `bindings` (`h`).
-/
public theorem interpEnv_congr {bindings : List (Variable × Loc)} {env env' : Env}
    (h : ∀ b ∈ bindings, env b.1 = env' b.1) :
    interpEnv (GF := GF) bindings env = interpEnv bindings env' := by
  induction bindings with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨x, ℓ⟩ := b
    simp only [interpEnv, h (x, ℓ) (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

omit [SemanticParams τ] in
/--
Access to the cell of variable `x`, bound to `ℓ` (`hl`: `bindings.lookup x = some ℓ`), when each
variable is bound at most once (`hnd`): the interpretation of the environment
(`interpEnv bindings env`) gives
- the ownership of `x`'s cell, holding what `env` says (`interpCell ℓ (env x)`); and
- a way to get back the interpretation of the environment updated with whatever cell `c` the
  ownership is returned with (`∀ c, interpCell ℓ c -∗ interpEnv bindings (env.set x c)`).
-/
public theorem interpEnv_acc {bindings : List (Variable × Loc)} {env : Env} {x : Variable}
    {ℓ : Loc} (hnd : (bindings.map (·.1)).Nodup) (hl : bindings.lookup x = some ℓ) :
    interpEnv (GF := GF) bindings env ⊢
      interpCell ℓ (env x) ∗ (∀ c, interpCell ℓ c -∗ interpEnv bindings (env.set x c)) := by
  induction bindings with
  | nil => simp at hl
  | cons b bs ih =>
    obtain ⟨y, ℓy⟩ := b
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases hxy : x = y
    · subst hxy
      simp only [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      have hrest : ∀ c, interpEnv (GF := GF) bs (env.set x c) = interpEnv bs env := fun c =>
        interpEnv_congr fun b hb => Env.set_ne (fun h => hnd.1 (List.mem_map.2 ⟨b, hb, h⟩)) c
      simp only [interpEnv]
      iintro ⟨Hc, Hrest⟩
      iframe Hc
      iintro %c Hc
      rw [hrest c, Env.set_self]
      iframe Hc
      iexact Hrest
    · rw [lookup_cons_ne hxy] at hl
      simp only [interpEnv]
      iintro ⟨Hy, Hrest⟩
      icases ih hnd.2 hl $$ Hrest with ⟨Hc, Hback⟩
      iframe Hc
      iintro %c Hc
      rw [Env.set_ne (Ne.symm hxy)]
      iframe Hy
      iapply Hback $$ Hc

omit [SemanticParams τ] in
/--
Access to the cell of variable `x`, bound to `ℓ` (`hl`: `bindings.lookup x = some ℓ`), for reading
it, when each variable is bound at most once (`hnd`): the interpretation of the environment
(`interpEnv bindings env`) gives
- the ownership of `x`'s cell, holding what `env` says (`interpCell ℓ (env x)`); and
- a way to get back the interpretation of the same environment when the ownership is returned
  unchanged (`interpCell ℓ (env x) -∗ interpEnv bindings env`).
-/
public theorem interpEnv_acc_read {bindings : List (Variable × Loc)} {env : Env} {x : Variable}
    {ℓ : Loc} (hnd : (bindings.map (·.1)).Nodup) (hl : bindings.lookup x = some ℓ) :
    interpEnv (GF := GF) bindings env ⊢
      interpCell ℓ (env x) ∗ (interpCell ℓ (env x) -∗ interpEnv bindings env) := by
  refine (interpEnv_acc (env := env) hnd hl).trans (sep_mono_right ?_)
  have h : (∀ c, interpCell (GF := GF) ℓ c -∗ interpEnv bindings (env.set x c)) ⊢
      (interpCell ℓ (env x) -∗ interpEnv bindings (env.set x (env x))) := forall_elim (env x)
  rw [Env.set_eq_self] at h
  exact h

omit [SemanticParams τ] in
/--
The interpretation of an environment (`interpEnv bindings env`) is equivalent to the separating
conjunction of:
- the part for the bindings of `v` (`interpEnv (bindings.filter (fun b => b.1 = v)) env`); and
- the part for the others (`interpEnv (bindings.filter (fun b => b.1 ≠ v)) env`).
-/
public theorem interpEnv_split (bindings : List (Variable × Loc)) (env : Env) (v : Variable) :
    interpEnv (GF := GF) bindings env ⊣⊢
      interpEnv (bindings.filter (fun b => b.1 = v)) env ∗
        interpEnv (bindings.filter (fun b => b.1 ≠ v)) env := by
  induction bindings with
  | nil => exact emp_sep.symm
  | cons b bs ih =>
    obtain ⟨y, ℓ⟩ := b
    by_cases hy : y = v
    · simp only [List.filter_cons, hy, decide_true, ne_eq, not_true_eq_false, decide_false,
        interpEnv]
      exact (sep_congr .rfl ih).trans sep_assoc.symm
    · simp only [List.filter_cons, hy, decide_false, ne_eq, not_false_eq_true, decide_true,
        interpEnv]
      refine (sep_congr .rfl ih).trans ?_
      exact sep_left_comm

/-! ### Structural rules -/

/--
Weakening: an expression that is semantically well typed with type `T` given facts `Δb` before and
guaranteeing facts `Δa` after (`h`) is also semantically well typed with every supertype `T'` of
`T` (`hT`) given more facts `Δb'` before (`hin`), guaranteeing fewer facts `Δa'` after (`hout`).
Requiring more before and guaranteeing less after both make the claim weaker, as for the
precondition and postcondition of a Hoare triple.
-/
public theorem SemTyped.weaken {Δb Δb' : Ctx} {m : LoweredExpr} {T T' : τ}
    {Δa Δa' : Value → Ctx} (h : SemTyped GF Δb m T Δa) (hin : ∀ f ∈ Δb, f ∈ Δb')
    (hT : T ≤ T') (hout : ∀ v, ∀ f ∈ Δa' v, f ∈ Δa v) : SemTyped GF Δb' m T' Δa' := by
  intro bindings hnd env
  refine (sep_mono_right (interpCtx_mono hin)).trans
    ((h bindings hnd env).trans (wp_mono fun o => ?_))
  cases o with
  | normal v =>
    simp only [interpOutcome]
    iintro ⟨%env', He, #Hv, #H⟩
    iexists env'
    iframe He
    isplitr
    · iapply interpVal_mono hT $$ Hv
    · iapply interpCtx_mono (hout v) $$ H
  | throwing _ => exact .rfl

/--
Running an evaluation context item `Ki` around an expression `e` satisfies a postcondition `Ψ`
(`WP (Ki.fill e) {{ Ψ }}`), given `P`, if:
- given `P`, `e` satisfies the typing postcondition for static type `T` and guaranteed facts `Δa`
  afterwards (`H`);
- for each value `v` that `e` can complete normally with, running `Ki` around `v` satisfies `Ψ`,
  given the ownership of the cells (`interpEnv bindings env'`), the fact that `v` satisfies `T`
  (`interpVal T v`), and the guaranteed facts (`interpCtx bindings env' (Δa v)`) (`Hn`); and
- `Ψ` holds of throwing any exception (`Ht`): an exception thrown by `e` propagates out of `Ki`.
-/
public theorem wp_fill_typed {P : IProp GF} {Ki : EctxItem (τ := τ)} {e : LoweredExpr}
    {bindings : List (Variable × Loc)} {T : τ} {Δa : Value → Ctx}
    {Ψ : DartLang.Outcome (τ := τ) → IProp GF}
    (H : P ⊢ WP e {{ o, interpOutcome bindings T Δa o }})
    (Hn : ∀ v env', interpEnv bindings env' ∗ interpVal T v ∗ interpCtx bindings env' (Δa v) ⊢
      WP (Ki.fill (.val v)) {{ Ψ }})
    (Ht : ∀ v, ⊢ Ψ (.throwing v)) : P ⊢ WP (Ki.fill e) {{ Ψ }} := by
  refine H.trans ((wp_mono fun o => ?_).trans (wp_bind_item Ki))
  cases o with
  | normal v =>
    simp only [interpOutcome, DartLang.Outcome.toExpr]
    iintro ⟨%env', H⟩
    iapply Hn v env' $$ H
  | throwing v =>
    refine .trans ?_ (wp_bubble Ki v)
    iintro -
    inext
    iapply Ht

end Interp

end DartSemantics
