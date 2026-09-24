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

/--
A property (a getter or field) that can be read from an object. Mirrors the `propertyMember` passed
to Dart's `propertyGet`, together with the information flow analysis needs about it.
-/
public structure Property where
  name : String
  /-- The static type of the property. -/
  type : τ
  /--
  Whether the property is promotable. Mirrors Dart's
  `operations.isPropertyPromotable(propertyMember) && fieldPromotionEnabled`.
  -/
  isPromotable : Bool
  deriving Repr, BEq, DecidableEq
