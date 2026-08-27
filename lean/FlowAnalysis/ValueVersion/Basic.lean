module

namespace FlowAnalysis

-- TODO: this is a placeholder.
public structure ValueVersion where

namespace ValueVersion

public def join (version₁? version₂? : Option ValueVersion) : Option ValueVersion :=
  match version₁?, version₂? with
    | none, none => none
    | _,    _    => some ⟨⟩

/-- The join operation is idempotent (`join version? version? = version?`). -/
@[simp]
public theorem join_self (version? : Option ValueVersion) : join version? version? = version? := by
  cases version? <;> rfl

public instance join.instIdempotentOp : Std.IdempotentOp join where
  idempotent := join_self

/-- The join operation is commutative (`join version?₁ version?₂ = join version?₂ version?₁`). -/
public theorem join_comm (version?₁ version?₂ : Option ValueVersion) : join version?₁ version?₂ = join version?₂ version?₁ := by
  cases version?₁ <;> cases version?₂ <;> rfl

public instance join.instCommutative : Std.Commutative join where
  comm := join_comm

/--
The join operation is associative (`join (join version?₁ version?₂) version?₃ = join version?₁ (join version?₂ version?₃)`).
-/
public theorem join_assoc (version?₁ version?₂ version?₃ : Option ValueVersion) :
    join (join version?₁ version?₂) version?₃ = join version?₁ (join version?₂ version?₃) := by
  cases version?₁ <;> cases version?₂ <;> cases version?₃ <;> rfl

public instance join.instAssociative : Std.Associative join where
  assoc := join_assoc

end ValueVersion
end FlowAnalysis
