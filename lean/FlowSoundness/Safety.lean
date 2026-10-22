module
public import FlowSoundness.Statements
public import FlowAnalysis.AlgorithmTheorems
public import DartSemantics.Safety

/-!
# Soundness of flow analysis, end to end

`elabStmtImpl_safe`: a program in the property-free subset of Dart that flow analysis accepts never
gets stuck when it runs. In particular, with `PromotionChecks.verify`, every read of a promoted
variable passes its promotion check: the promotions that flow analysis makes are sound.

The proof chains the correctness of the flow analysis algorithm (`elabStmtImpl.sound_initial`), the
soundness of statement elaboration (`ElabStmts.semTyped`), and the safety of semantically well
typed programs (`DartSemantics.safety`).
-/

namespace FlowSoundness

open DartLang DartSemantics FlowAnalysis Iris Iris.ProgramLogic

variable {τ : Type} [Γ : DartRuntimeTypeRepr τ]

/--
**Soundness of flow analysis**, for the property-free subset of Dart (`hnp`). If the flow
analysis algorithm accepts the block of statements `ss`, analyzed as a whole program (at the root
AST path, in the empty scope, from the initial state), and lowers it to `m` (`hok`), then `m`,
started in any state `σ`, never gets stuck (`.NotStuck`), and every outcome it completes with is
consistent with `Null` (`OutcomeOk Γ.Null o`). This needs the type representation to obey
`TypeLaws` (`L`).
-/
public theorem elabStmtImpl_safe [SemanticParams τ] {GF : BundledGFunctors} [DartGpreS τ GF]
    (L : TypeLaws τ) {ss : List (Stmt (τ := τ))} {m : LoweredExpr (τ := τ)} {sI}
    (hnp : Stmt.NoPropertiesList ss)
    (hok : elabStmtImpl (.block ss) ⟨[], []⟩ AlgState.initial = Except.ok (m, sI))
    (σ : State (τ := τ)) :
    adequate .NotStuck m σ (fun o _ => OutcomeOk Γ.Null o) := by
  obtain ⟨fm, helab⟩ := elabStmtImpl.sound_initial hok
  cases helab with
  | block hs =>
    have hscope : Scope.WellFormedAt [0] ([] : Scope (τ := τ)) := ⟨⟨by simp, by simp⟩, by simp⟩
    have h := safety (GF := GF) σ [] (ElabStmts.semTyped L hs hnp hscope)
      ⟨by simp, by simp, by simp⟩ (fun f hf => by simp [ctxOf] at hf)
    simpa [LoweredExpr.bindVariables] using h

end FlowSoundness
