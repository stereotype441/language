module

namespace FlowAnalysis

-- TODO: this is a placeholder.
public structure SsaNode where

namespace SsaNode

public def join (ssa₁? ssa₂? : Option SsaNode) : Option SsaNode :=
  match ssa₁?, ssa₂? with
    | none, none => none
    | _,    _    => some ⟨⟩

/-- The join operation is idempotent (`join ssa? ssa? = ssa?`). -/
@[simp]
public theorem join_self (ssa? : Option SsaNode) : join ssa? ssa? = ssa? := by
  cases ssa? <;> rfl

public instance join.instIdempotentOp : Std.IdempotentOp join where
  idempotent := join_self

/-- The join operation is commutative (`join ssa?₁ ssa?₂ = join ssa?₂ ssa?₁`). -/
public theorem join_comm (ssa?₁ ssa?₂ : Option SsaNode) : join ssa?₁ ssa?₂ = join ssa?₂ ssa?₁ := by
  cases ssa?₁ <;> cases ssa?₂ <;> rfl

public instance join.instCommutative : Std.Commutative join where
  comm := join_comm

/--
The join operation is associative (`join (join ssa?₁ ssa?₂) ssa?₃ = join ssa?₁ (join ssa?₂ ssa?₃)`).
-/
public theorem join_assoc (ssa?₁ ssa?₂ ssa?₃ : Option SsaNode) :
    join (join ssa?₁ ssa?₂) ssa?₃ = join ssa?₁ (join ssa?₂ ssa?₃) := by
  cases ssa?₁ <;> cases ssa?₂ <;> cases ssa?₃ <;> rfl

public instance join.instAssociative : Std.Associative join where
  assoc := join_assoc

end SsaNode
end FlowAnalysis
