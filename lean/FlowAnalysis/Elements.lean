module
public import FlowAnalysis.Types

namespace FlowAnalysis

variable {τ : Type} [DartTypeRepr τ]

-- A local variable or function parameter.
public structure Variable where
  name : String
  type : τ
  deriving Repr, BEq, DecidableEq

local notation "Variable" => Variable (τ := τ)

public instance Variable.instHashable : Hashable Variable where
  hash v := hash v.name

-- Establish some properties of the `Variable` type so that it can be used as the key for a hashmap.
public instance Variable.instLawfulBEq : LawfulBEq Variable where
  rfl := by
    intro v
    simp [BEq.beq, instBEqVariable.beq]

  eq_of_beq := by
    rintro ⟨n, T⟩ ⟨n', T'⟩
    simp [BEq.beq, instBEqVariable.beq]

public instance Variable.instLawfulHashable : LawfulHashable Variable where
  hash_eq := by simp_all
