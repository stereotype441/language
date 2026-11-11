module
public import DartLang.Lowered
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public meta import Lean.Elab.Command

/-!
# Printing constructors in leading-dot form

When Lean displays a term, for example in a goal in the InfoView, a constructor application such as
`LoweredExpr.block [LoweredExpr.val (Value.int 0), LoweredExpr.val Value.null]` is shown with each
constructor's full name. Where the type is known from context, Lean accepts the shorter
*leading-dot* form `.block [.val (.int 0), .val .null]` as input, and that is how the code in this
project writes such terms. (Where a file has a `local notation "LoweredExpr" => …`, the full names
are even noisier: the notation makes `LoweredExpr` a token, so Lean quotes it as `«LoweredExpr»`.)

This file makes Lean display the constructors of the types that terms of the semantics are built
from in leading-dot form too, so that goals read like the code. The command `pp_dot_ctors T₁ T₂ …`
does this for each constructor of the inductive types `Tᵢ`; it's applied below to the types in
`DartLang.Lowered`, and in `DartSemantics.State` to `Cell`. Setting the option `dart.pp.dotCtors`
to `false` (`set_option dart.pp.dotCtors false`) turns this off, so that full names are displayed
again; so does `set_option pp.all true`.

## How it works

Lean's pretty printer first turns an `Expr` (the internal representation of a term) into `Syntax`
(a parse tree), and then formats that as text. The first stage is called *delaboration*, the
inverse of elaboration. A *delaborator* is a function that does this for some kind of `Expr`; the
`delab` attribute registers one, keyed by what it handles, and Lean tries the delaborators for an
expression's key before its default one. For an application `f a₁ … aₙ` of a constant `f`, the key
is `app.f`.

`delabDotCtor` is registered (by `pp_dot_ctors`) for each constructor `c` of the given types. It
runs Lean's default delaborator for applications (`delabApp`), which produces `T.c a₁ … aₙ`
(omitting implicit arguments such as the type representation `τ`), and replaces the head `T.c` with
`.c`. It does this only when the constructor is applied to all its arguments: a partial
application such as `LoweredExpr.seq m` is a function, and `.seq m` would only be accepted as input
where a `LoweredExpr` is expected, so it's left in full. It also leaves the result alone if the
default delaborator produced something other than a plain application of the constructor's name:
for example, Lean's field notation `m₁.seq m₂` for `LoweredExpr.seq m₁ m₂` (see the option
`pp.fieldNotation`), or `@T.c τ …` with `set_option pp.explicit true`, which shows implicit
arguments.

All the code here is `meta`: under Lean's module system, code that runs at compile time (such as a
delaborator or a command) is marked `meta`, and its imports are `meta import`s.
-/

public meta section

namespace DartLang.PrettyPrint

open Lean Elab Command PrettyPrinter Delaborator SubExpr

/--
The option `dart.pp.dotCtors`: whether to display the constructors of the types that
`pp_dot_ctors` was applied to in leading-dot form (`.c a₁ … aₙ`, rather than `T.c a₁ … aₙ`).
-/
register_option dart.pp.dotCtors : Bool := {
  defValue := true
  descr := "(pretty printer) display constructors of the Dart semantics' types in leading-dot \
    form, such as `.val (.int 0)` rather than `LoweredExpr.val (Value.int 0)`"
}

/--
Whether the option `dart.pp.dotCtors` is on, in options `o`. If it isn't set, it's on unless
`pp.all` is.
-/
def getPPDotCtors (o : Options) : Bool :=
  o.get dart.pp.dotCtors.name (!getPPAll o)

/--
The delaborator that displays an application of a constructor `T.c` to all its arguments as
`.c a₁ … aₙ`, when the option `dart.pp.dotCtors` is on. Otherwise it fails, which tells Lean to
use its default delaborator instead.
-/
def delabDotCtor : Delab :=
  whenPPOption getPPDotCtors do
    -- The expression being displayed, `T.c a₁ … aₙ`. (`failure` gives up, so that Lean falls back
    -- to its default delaborator.)
    let e ← getExpr
    let .const c _ := e.getAppFn | failure
    let .ctorInfo info ← getConstInfo c | failure
    -- Only a full application: all the type's parameters (such as `τ`), and all the constructor's
    -- own arguments.
    unless e.getAppNumArgs == info.numParams + info.numFields do failure
    let stx ← delabApp
    -- `.c`, keeping the position information of the head `T.c`, which links the printed name to
    -- the constructor (for example, for hovering over it in the InfoView).
    let dot (fn : Syntax) : Term :=
      ⟨mkNode ``Parser.Term.dotIdent
        #[mkAtomFrom fn ".", mkIdentFrom fn (.mkSimple c.lastComponentAsString)]⟩
    -- The patterns are syntax quotations: `($fn:ident) matches a name on its own (a constructor
    -- without arguments), and `($fn:ident $_*) a name applied to arguments.
    match stx with
    | `($fn:ident) => return dot fn
    | `($fn:ident $_*) => return ⟨stx.raw.setArg 0 (dot fn)⟩
    | _ => failure

/--
`pp_dot_ctors T₁ T₂ …` makes Lean display each constructor of the inductive types `Tᵢ` in
leading-dot form, by registering `delabDotCtor` as the delaborator for applications of it: for each
constructor `T.c`, it runs the command `attribute [delab app.T.c] delabDotCtor`.
-/
syntax (name := ppDotCtors) "pp_dot_ctors" (ppSpace ident)+ : command

@[inherit_doc ppDotCtors, command_elab ppDotCtors]
def elabPPDotCtors : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let T ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let .inductInfo info ← getConstInfo T
      | throwErrorAt id "pp_dot_ctors: {T} isn't an inductive type"
    for c in info.ctors do
      elabCommand (← `(attribute [delab $(mkIdent (`app ++ c))] DartLang.PrettyPrint.delabDotCtor))

end DartLang.PrettyPrint

end

pp_dot_ctors DartLang.LoweredExpr DartLang.Value DartLang.EctxItem DartLang.Outcome
  DartLang.ConstValue DartLang.DynamicError DartLang.CheckKind DartLang.IntBinOp DartLang.IntMode
