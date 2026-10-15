module
public import FlowAnalysis.PromotionChain.Basic
public import FlowAnalysis.PromotionChain.JoinImpl
public import FlowAnalysis.ValueVersion.Basic
public import FlowAnalysis.PromotionModel.JoinTestedImpl
public import DartLang.Types

namespace FlowAnalysis
open DartLang

open PromotionChain

variable {τ : Type} [Γ : DartTypeRepr τ] {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "ValueVersion" => ValueVersion (ℓ := ℓ)

/-- The state of a promotable value at a particular point in a function's execution. -/
@[ext]
public structure PromotionModel where
  promotedTypes : PromotionChain
  tested : Finset τ
  assigned : Bool
  unassigned : Bool
  version? : Option ValueVersion
  /--
  Whether flow analysis has given up on tracking this value, because it may be written by a closure
  or a local function at a point flow analysis can't see.
  -/
  writeCaptured : Bool
  /--
  A write-captured value has no promotions: the write that flow analysis can't see might have
  replaced it with a value of the declared type.
  -/
  writeCaptured_promotedTypes : writeCaptured → promotedTypes = ∅
  /--
  Flow analysis tracks a value version precisely when it hasn't given up on the location.  Write
  capture is the only reason it gives up, so the two conditions coincide.
  -/
  version?_eq_none_iff : version? = none ↔ writeCaptured
  /-- A location can't be both definitely assigned and definitely unassigned. -/
  not_assigned_and_unassigned : ¬(assigned ∧ unassigned)
  /--
  A write-captured location isn't definitely unassigned: write capture means an unseen write might
  have happened.
  -/
  not_writeCaptured_and_unassigned : ¬(writeCaptured ∧ unassigned)

local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := ℓ)

namespace «PromotionModel»

/--
The promotion model of a freshly declared variable: unpromoted, untested, not write captured, and
holding the value `version`. It is definitely assigned if the declaration initializes the variable
(`initialized`), and definitely unassigned otherwise.

This is a smart constructor rather than a literal because the invariants on `PromotionModel` are
carried as proof fields, and it is tidier to discharge them once here than at each construction
site.
-/
@[expose]
public def declared (initialized : Bool) (version : ValueVersion) : PromotionModel where
  promotedTypes := ∅
  tested := ∅
  assigned := initialized
  unassigned := !initialized
  version? := some version
  writeCaptured := false
  writeCaptured_promotedTypes := by simp
  version?_eq_none_iff := by simp
  not_assigned_and_unassigned := by cases initialized <;> simp
  not_writeCaptured_and_unassigned := by simp

/--
Mirrors Dart's `PromotionModel.fresh(version: version)`: the promotion model that
`FlowModel.infoFor` supplies for a reference that has no promotion model yet. It is unpromoted,
untested, not write captured, and holds the value `version`.

As in Dart, where `assigned` defaults to `false` and `unassigned` is `!assigned`, it is definitely
unassigned. Nothing modelled so far consults definite assignment for properties.
-/
@[expose]
public def fresh (version : ValueVersion) : PromotionModel where
  promotedTypes := ∅
  tested := ∅
  assigned := false
  unassigned := true
  version? := some version
  writeCaptured := false
  writeCaptured_promotedTypes := by simp
  version?_eq_none_iff := by simp
  not_assigned_and_unassigned := by simp
  not_writeCaptured_and_unassigned := by simp

@[expose]
public def currentType (pm : PromotionModel) (baseType : τ) :=
  match pm.promotedTypes.val.getLast? with
  | none => baseType
  | some T => if T ≤ baseType then T else baseType

/--
`pm.tryPromote T h` promotes to `T`, if doing so yields a valid promotion chain, and is the identity
otherwise.

The hypothesis `h` is what re-establishes `writeCaptured_promotedTypes`: a write-captured value has
no promotions, so it can't acquire one.  Flow analysis never tries to promote a write-captured
location, so every caller has `h` to hand.
-/
@[expose]
public def tryPromote (pm : PromotionModel) (T : τ) (h : ¬pm.writeCaptured) : PromotionModel :=
  { pm with
    promotedTypes := pm.promotedTypes.tryPromote T
    writeCaptured_promotedTypes := fun hwc => absurd hwc h }

omit [DecidableEq ℓ] in
/-- Promoting doesn't change whether a variable is write-captured. -/
@[simp]
public theorem writeCaptured_tryPromote {pm : PromotionModel} {T : τ} {h : ¬pm.writeCaptured} :
    (pm.tryPromote T h).writeCaptured = pm.writeCaptured := rfl

/--
The promotion model after a value of static type `writtenType` is assigned, giving the location
the new value version `newVersion`. Mirrors the specification's `assign(x, E, M)` (in the flow
analysis specification's "Promotion" section), apart from promotion to a type of interest, which
isn't modeled yet: the promoted types are demoted (`PromotionChain.demote`), and the location
becomes definitely assigned, and not definitely unassigned. A write-captured location keeps no
value version (and has no promotions to demote).

TODO: promote to a type of interest (the specification's `toi_promote`), once `tested` is tracked.
-/
@[expose]
public def write (pm : PromotionModel) (writtenType : τ) (newVersion : ValueVersion) :
    PromotionModel where
  promotedTypes := pm.promotedTypes.demote writtenType
  tested := pm.tested
  assigned := true
  unassigned := false
  version? := if pm.writeCaptured then none else some newVersion
  writeCaptured := pm.writeCaptured
  writeCaptured_promotedTypes := by
    intro hwc
    simp [pm.writeCaptured_promotedTypes hwc]
  version?_eq_none_iff := by split <;> simp_all
  not_assigned_and_unassigned := by simp
  not_writeCaptured_and_unassigned := by simp

@[expose]
public def join (pm₁ pm₂ : PromotionModel) : PromotionModel where
  promotedTypes := pm₁.promotedTypes.join pm₂.promotedTypes
  tested := pm₁.tested ∪ pm₂.tested
  assigned := pm₁.assigned ∧ pm₂.assigned
  unassigned := pm₁.unassigned ∧ pm₂.unassigned
  version? := ValueVersion.join? pm₁.version? pm₂.version?
  writeCaptured := pm₁.writeCaptured ∨ pm₂.writeCaptured
  writeCaptured_promotedTypes := by
    -- The join of two promotion chains is a sublist of each, so if either side has given up all of
    -- its promotions, so does the join.
    intro hwc
    rcases Bool.or_eq_true _ _ |>.mp (by simpa using hwc) with hwc₁ | hwc₂
    · simp [pm₁.writeCaptured_promotedTypes hwc₁]
    · simp [pm₂.writeCaptured_promotedTypes hwc₂]
  version?_eq_none_iff := by
    simp [ValueVersion.join?, Option.map₂_eq_none_iff, pm₁.version?_eq_none_iff,
      pm₂.version?_eq_none_iff]
  not_assigned_and_unassigned := by
    have := pm₁.not_assigned_and_unassigned; simp_all
  not_writeCaptured_and_unassigned := by
    have := pm₁.not_writeCaptured_and_unassigned
    have := pm₂.not_writeCaptured_and_unassigned
    grind

/-- The join operation is idempotent (`join pm pm = pm`). -/
@[simp]
public theorem join_self (pm : PromotionModel) : pm.join pm = pm := by
  ext1 <;> simp [join]

public instance join.instIdempotentOp :
    Std.IdempotentOp (join (τ := τ) (ℓ := ℓ)) where
  idempotent := join_self

/-- The join operation is commutative (`join pm₁ pm₂ = join pm₂ pm₁`). -/
public theorem join_comm (pm₁ pm₂ : PromotionModel) : pm₁.join pm₂ = pm₂.join pm₁ := by
  ext1 <;>
    simp [join, PromotionChain.join_comm, Finset.union_comm, Bool.and_comm, Bool.or_comm,
      ValueVersion.join?_comm]

public instance join.instCommutative : Std.Commutative (join (τ := τ) (ℓ := ℓ)) where
  comm := join_comm

/-- The join operation is associative (`join (join pm₁ pm₂) pm₃ = join pm₁ (join pm₂ pm₃)`). -/
public theorem join_assoc (pm₁ pm₂ pm₃ : PromotionModel) :
    (pm₁.join pm₂).join pm₃ = pm₁.join (pm₂.join pm₃) := by
  ext1 <;>
    simp [join, PromotionChain.join_assoc, Finset.union_assoc, Bool.and_assoc, Bool.or_assoc,
      ValueVersion.join?_assoc]

public instance join.instAssociative : Std.Associative (join (τ := τ) (ℓ := ℓ)) where
  assoc := join_assoc

end «PromotionModel»

open «PromotionModel»

public structure PromotionModelImpl where
  promotedTypes : List τ
  tested : List τ
  assigned : Bool
  unassigned : Bool
  version? : Option ValueVersion

local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ) (ℓ := ℓ)

@[expose]
public def PromotionModelImpl.join (pmI₁ pmI₂ : PromotionModelImpl) : PromotionModelImpl :=
  ⟨(joinPromotedTypesImpl pmI₁.promotedTypes pmI₂.promotedTypes : Id _).run,
    joinTestedImpl pmI₁.tested pmI₂.tested,
    pmI₁.assigned ∧ pmI₂.assigned,
    pmI₁.unassigned ∧ pmI₂.unassigned,
    ValueVersion.join? pmI₁.version? pmI₂.version?
  ⟩

/--
Mirrors Dart's `PromotionModel.fresh(version: version)`: unpromoted, untested, not definitely
assigned, definitely unassigned, and holding the value `version`.
-/
@[expose]
public def PromotionModelImpl.fresh (version : ValueVersion) : PromotionModelImpl :=
  ⟨[], [], false, true, some version⟩

@[expose]
public def PromotionModelImpl.promotedType? (pmI : PromotionModelImpl) : Option τ :=
  pmI.promotedTypes.getLast?

@[expose]
public def PromotionModelImpl.currentType (pmI : PromotionModelImpl) (baseType : τ) :
    τ :=
  match pmI.promotedType? with
  | none => baseType
  | some T => if T ≤ baseType then T else baseType

/--
Whether flow analysis has given up on tracking this value.

Unlike the specification's `PromotionModel.writeCaptured`, this is *derived* rather than stored:
the implementation records write capture by dropping the value version, and reads it back with the
getter `bool get writeCaptured => version == null`.  The specification's invariant
`version?_eq_none_iff` is what makes the two agree.

Note that `join` therefore needs no `writeCaptured` component: `ValueVersion.join?` is `none`
exactly when either operand is, which is the `||` the implementation computes.
-/
@[expose]
public def PromotionModelImpl.writeCaptured (pmI : PromotionModelImpl) : Bool :=
  pmI.version?.isNone

/--
Mirrors Dart's `PromotionModel.write` (without promotion to a type of interest, which isn't
modeled yet): the promotion model after a value of static type `writtenType` is assigned, giving
the location the new value version `newVersion`.
-/
@[expose]
public def PromotionModelImpl.write (pmI : PromotionModelImpl) (writtenType : τ)
    (newVersion : ValueVersion) : PromotionModelImpl :=
  if pmI.writeCaptured then { pmI with assigned := true, unassigned := false }
  else ⟨demoteViaAssignmentImpl writtenType pmI.promotedTypes, pmI.tested, true, false,
    some newVersion⟩

-- Decidable equality of labels is only needed in order to join value versions, so omit it from the
-- refinement definitions and lemmas below; `PromotionModelImpl.refines.join` reintroduces it
-- explicitly.
omit [DecidableEq ℓ]

public structure PromotionModelImpl.refines (pmI : PromotionModelImpl) (pm : PromotionModel) :
    Prop where
  promotedTypes : pmI.promotedTypes = pm.promotedTypes.val
  tested : ∀ T, T ∈ pmI.tested ↔ T ∈ pm.tested
  assigned : pmI.assigned = pm.assigned
  unassigned : pmI.unassigned = pm.unassigned
  version? : pmI.version? = pm.version?

/-- Simp form of `refines.promotedTypes`: given `h`, the promoted types agree. -/
@[simp]
public theorem PromotionModelImpl.refines.promotedTypes' {pmI : PromotionModelImpl}
    {pm : PromotionModel} (h : PromotionModelImpl.refines pmI pm) :
    (pmI.promotedTypes = pm.promotedTypes.val) ↔ True := by
  simp [h.promotedTypes]

/-- Simp form of `refines.tested`: given `h`, the tested types agree. -/
@[simp]
public theorem PromotionModelImpl.refines.tested' {pmI : PromotionModelImpl} {pm : PromotionModel}
    (h : PromotionModelImpl.refines pmI pm) : (∀ T, T ∈ pmI.tested ↔ T ∈ pm.tested) ↔ True := by
  simp [h.tested]

/-- Simp form of `refines.assigned`: given `h`, the definite-assignment flags agree. -/
@[simp]
public theorem PromotionModelImpl.refines.assigned' {pmI : PromotionModelImpl} {pm : PromotionModel}
    (h : PromotionModelImpl.refines pmI pm) : (pmI.assigned = pm.assigned) ↔ True := by
  simp [h.assigned]

/-- Simp form of `refines.unassigned`: given `h`, the definite-unassignment flags agree. -/
@[simp]
public theorem PromotionModelImpl.refines.unassigned' {pmI : PromotionModelImpl} {pm : PromotionModel}
    (h : PromotionModelImpl.refines pmI pm) : (pmI.unassigned = pm.unassigned) ↔ True := by
  simp [h.unassigned]

/-- Simp form of `refines.version?`: given `h`, the value versions agree. -/
@[simp]
public theorem PromotionModelImpl.refines.version?' {pmI : PromotionModelImpl} {pm : PromotionModel}
    (h : PromotionModelImpl.refines pmI pm) : (pmI.version? = pm.version?) ↔ True := by
  simp [h.version?]

/--
The algorithm and the specification agree about write capture: if `pmI` refines `pm` (`h`), then
`pmI.writeCaptured = pm.writeCaptured`.

This is a *consequence* of refinement rather than a clause of it, because the algorithm derives
write capture from the absence of a value version, and the specification's `version?_eq_none_iff`
invariant says its stored flag agrees with the same test.
-/
public theorem PromotionModelImpl.refines.writeCaptured {pmI : PromotionModelImpl}
    {pm : PromotionModel} (h : PromotionModelImpl.refines pmI pm) :
    pmI.writeCaptured = pm.writeCaptured := by
  have hiff := pm.version?_eq_none_iff
  simp only [PromotionModelImpl.writeCaptured, h.version?]
  cases hv : pm.version? <;> simp_all

/--
The promotion model that the algorithm creates for a freshly declared variable refines the
promotion model that the specification creates for it.
-/
@[simp]
public theorem PromotionModelImpl.refines.declared (initialized : Bool) (version : ValueVersion) :
    (⟨[], [], initialized, !initialized, some version⟩ : PromotionModelImpl).refines
      (PromotionModel.declared initialized version) := by
  constructor <;> simp [PromotionModel.declared]

/--
The fresh promotion model that the algorithm creates for a reference with no promotion model refines
the one the specification creates.
-/
@[simp]
public theorem PromotionModelImpl.refines.fresh (version : ValueVersion) :
    (PromotionModelImpl.fresh version : PromotionModelImpl).refines
      (PromotionModel.fresh version) := by
  constructor <;> simp [PromotionModelImpl.fresh, PromotionModel.fresh]

/--
An algorithm promotion model refines at most one specification promotion model: if `pmI` refines
both `pm₁` and `pm₂`, then `pm₁ = pm₂`.
-/
public theorem PromotionModelImpl.refines.unique {pmI : PromotionModelImpl}
    {pm₁ pm₂ : PromotionModel} :
    pmI.refines pm₁ → pmI.refines pm₂ → pm₁ = pm₂ := by
  intro h₁ h₂
  ext1
  case promotedTypes => ext1; rw [←h₁.promotedTypes, ←h₂.promotedTypes]
  case tested => ext; rw [←h₁.tested, ←h₂.tested]
  case assigned => rw [←h₁.assigned, ←h₂.assigned]
  case unassigned => rw [←h₁.unassigned, ←h₂.unassigned]
  case version? => rw [←h₁.version?, ←h₂.version?]
  case writeCaptured => rw [←h₁.writeCaptured, ←h₂.writeCaptured]

/--
If `pmI` refines `pm`, they agree about a variable's current type, for any declared type `baseType`
(`pmI.currentType baseType = pm.currentType baseType`).
-/
public theorem PromotionModelImpl.refines.currentTypes {pmI : PromotionModelImpl} {pm : PromotionModel}
    {baseType : τ} : pmI.refines pm → pmI.currentType baseType = pm.currentType baseType := by
  intro hrefines
  simp [PromotionModelImpl.currentType, PromotionModelImpl.promotedType?, PromotionModel.currentType]
  rw [hrefines.promotedTypes]

/--
Refinement (`hrefines`) implies that `pmI` and `pm` agree about whether a promotion to `T` is
possible: appending `T` to `pmI`'s list of promoted types produces a valid promotion chain
(`isPromotionChain (pmI.promotedTypes ++ [T])`) iff `pm`'s promotion chain strictly bounds `T`
(`pm.promotedTypes.strictly_bounds T`).
-/
public theorem PromotionModelImpl.refines.strictly_bounds_iff {pmI : PromotionModelImpl}
    {pm : PromotionModel} {T : τ} (hrefines : pmI.refines pm) :
    isPromotionChain (pmI.promotedTypes ++ [T]) ↔ pm.promotedTypes.strictly_bounds T := by
  rw [PromotionChain.strictly_bounds, hrefines.promotedTypes]

/--
The algorithm promotes a variable to `T` by appending `T` to its list of promoted types, but only
when the resulting list is a valid promotion chain (`hchain`). This theorem shows that, if `pmI`
refines `pm` (`hrefines`) and the variable isn't write-captured (`hwc`), doing so refines
`PromotionModel.tryPromote`, which appends `T` under precisely the same circumstances.
-/
public theorem PromotionModelImpl.refines.promote {pmI : PromotionModelImpl} {pm : PromotionModel}
    {T : τ} (hrefines : pmI.refines pm) (hchain : isPromotionChain (pmI.promotedTypes ++ [T]))
    (hwc : ¬pm.writeCaptured) :
    {pmI with promotedTypes := pmI.promotedTypes ++ [T]}.refines (pm.tryPromote T hwc) := by
  have hbounds : pm.promotedTypes.strictly_bounds T := hrefines.strictly_bounds_iff.mp hchain
  constructor <;> simp_all [PromotionModel.tryPromote]

/--
Conversely, if `pmI` refines `pm` (`hrefines`), then in the circumstances in which the algorithm
declines to promote a variable to `T` (that is, when appending `T` to its list of promoted types
wouldn't produce a valid promotion chain, `hchain`), `PromotionModel.tryPromote` is a no-op
(`pm.tryPromote T hwc = pm`).
-/
public theorem PromotionModelImpl.refines.tryPromote_eq_self {pmI : PromotionModelImpl}
    {pm : PromotionModel} {T : τ} (hrefines : pmI.refines pm)
    (hchain : ¬isPromotionChain (pmI.promotedTypes ++ [T])) {hwc : ¬pm.writeCaptured} :
    pm.tryPromote T hwc = pm := by
  have hbounds : ¬pm.promotedTypes.strictly_bounds T := hrefines.strictly_bounds_iff.not.mp hchain
  ext1 <;> simp [PromotionModel.tryPromote, hbounds]

/--
Joins preserve refinement: if `pmI₁` refines `pm₁` and `pmI₂` refines `pm₂`, then
`pmI₁.join pmI₂` refines `pm₁.join pm₂`.
-/
public theorem PromotionModelImpl.refines.join [DecidableEq ℓ] {pmI₁ pmI₂ : PromotionModelImpl}
    {pm₁ pm₂ : PromotionModel} :
    pmI₁.refines pm₁ → pmI₂.refines pm₂ → (pmI₁.join pmI₂).refines (pm₁.join pm₂) := by
  rintro hrefines₁ hrefines₂
  simp [PromotionModelImpl.join, PromotionModel.join]
  constructor
  case promotedTypes =>
    simp [hrefines₁.promotedTypes, hrefines₂.promotedTypes]
    rw [joinPromotedTypesImpl_pure_correct pm₁.promotedTypes pm₂.promotedTypes]
  case tested =>
    intro T; simp [joinTestedImpl, List.mem_union_iff, hrefines₁.tested, hrefines₂.tested]
  case assigned => simp [hrefines₁.assigned, hrefines₂.assigned]
  case unassigned => simp [hrefines₁.unassigned, hrefines₂.unassigned]
  case version? => simp [hrefines₁.version?, hrefines₂.version?]

/--
The algorithm's update of a promotion model for an assignment refines the specification's: if `pmI`
refines `pm` (`hrefines`), then `pmI.write writtenType newVersion` refines
`pm.write writtenType newVersion` (`PromotionModel.write`). On a promotion chain,
`demoteViaAssignmentImpl` computes `PromotionChain.demote` (`demoteViaAssignmentImpl_correct`).
-/
public theorem PromotionModelImpl.refines.write {pmI : PromotionModelImpl} {pm : PromotionModel}
    (hrefines : pmI.refines pm) (writtenType : τ) (newVersion : ValueVersion) :
    (pmI.write writtenType newVersion).refines (pm.write writtenType newVersion) := by
  have hwc := hrefines.writeCaptured
  by_cases h : pm.writeCaptured
  · have hpt := pm.writeCaptured_promotedTypes h
    have hv : pm.version? = none := pm.version?_eq_none_iff.2 h
    constructor <;>
      simp_all [PromotionModelImpl.write, PromotionModel.write, hrefines.promotedTypes,
        hrefines.tested, hrefines.version?]
  · constructor <;>
      simp_all [PromotionModelImpl.write, PromotionModel.write, hrefines.promotedTypes,
        hrefines.tested, demoteViaAssignmentImpl_correct]

end FlowAnalysis
