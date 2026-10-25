module
public import FlowAnalysis.PromotionModel.Basic
public import FlowAnalysis.PromotionChain.JoinImpl
public import FlowAnalysis.PromotionModel.JoinTestedImpl
public import Mathlib.Data.List.DropRight

/-!
# The algorithm's representation of promotion models

This file defines `PromotionModelImpl`, the representation of a promotion model used by the
algorithmic model of flow analysis (`FlowAnalysis.Algorithm`), which mirrors the data structures of
the Dart implementation more closely than the specification's `PromotionModel` does. It also
defines the refinement relation `PromotionModelImpl.refines`, which relates each algorithm promotion
model to the specification promotion model it represents, and proves that the algorithm's
operations on promotion models refine the specification's.
-/

namespace FlowAnalysis
open DartLang

open PromotionChain

variable {τ : Type} [Γ : DartTypeRepr τ] {ℓ : Type} [DecidableEq ℓ]

local notation "PromotionChain" => PromotionChain (τ := τ)
local notation "ValueVersion" => ValueVersion (ℓ := ℓ)
local notation "PromotionModel" => PromotionModel (τ := τ) (ℓ := ℓ)

/--
Mirrors Dart's `PromotionModel._demoteViaAssignment`: drops promoted types from the end of
`promotedTypes` until reaching one that `writtenType` is a subtype of (or none are left).
-/
@[expose]
public def demoteViaAssignmentImpl (writtenType : τ) (promotedTypes : List τ) : List τ :=
  promotedTypes.rdropWhile (fun T => !decide (writtenType ≤ T))

omit [DecidableEq ℓ] in
/--
On a promotion chain, `demoteViaAssignmentImpl` computes `PromotionChain.demote`. In a promotion
chain, each type is a strict subtype of the ones before it, so if `writtenType` is a subtype of a
type, it's a subtype of all the types before it too: the types it's a subtype of form a prefix,
which dropping types from the end finds.
-/
public theorem demoteViaAssignmentImpl_correct (writtenType : τ) (c : PromotionChain) :
    demoteViaAssignmentImpl writtenType c.val = (c.demote writtenType).val := by
  obtain ⟨l, hl⟩ := c
  simp only [demoteViaAssignmentImpl, PromotionChain.val_demote]
  rw [isPromotionChain.iff_isChain, List.isChain_iff_pairwise] at hl
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih =>
    rw [List.pairwise_append] at hl
    obtain ⟨hl, -, hx⟩ := hl
    have hx : ∀ T ∈ l, x < T := fun T hT => hx T hT x (List.mem_singleton_self x)
    by_cases hw : writtenType ≤ x
    · rw [List.rdropWhile_concat_neg _ _ x (by simpa using hw), List.filter_append,
        List.filter_eq_self.2 (fun T hT => by simpa using le_trans hw (hx T hT).le)]
      simp [hw]
    · rw [List.rdropWhile_concat_pos _ _ x (by simpa using hw), List.filter_append, ih hl]
      simp [hw]

open «PromotionModel»

/--
Mirrors Dart's `PromotionModel`: what flow analysis knows about one promotable location, with the
promoted and tested types as plain lists, as in Dart. Related to the specification's
`PromotionModel` by `PromotionModelImpl.refines`.
-/
public structure PromotionModelImpl where
  /-- The types the value has been promoted to, in the order of promotion. -/
  promotedTypes : List τ
  /-- The types the value has been tested against. -/
  tested : List τ
  /-- Whether the location is definitely assigned. -/
  assigned : Bool
  /-- Whether the location is definitely unassigned. -/
  unassigned : Bool
  /--
  The value version the location holds, or `none` if flow analysis has given up on tracking it
  (see `PromotionModelImpl.writeCaptured`).
  -/
  version? : Option ValueVersion

local notation "PromotionModelImpl" => PromotionModelImpl (τ := τ) (ℓ := ℓ)

/--
Mirrors Dart's `PromotionModel.join`: the promotion model where two control flow paths come
together. The promoted types are joined with `joinPromotedTypesImpl` (Dart's `joinPromotedTypes`)
and the tested types with `joinTestedImpl`.
-/
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

/-- The most recent promotion, if any: the last element of `promotedTypes`. -/
@[expose]
public def PromotionModelImpl.promotedType? (pmI : PromotionModelImpl) : Option τ :=
  pmI.promotedTypes.getLast?

/--
The type of a read of the location, given that its declared type is `baseType`: its most recent
promotion, if any (and if it's a subtype of `baseType`), and otherwise `baseType`. Agrees with the
specification's `PromotionModel.currentType` (`refines.currentTypes`).
-/
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

/--
`pmI.refines pm` says that the algorithm's promotion model `pmI` faithfully represents the
specification's promotion model `pm`: each component agrees, with the promoted types compared as
lists and the tested types compared by membership (the algorithm's list may contain duplicates, or
be in a different order). Write capture isn't compared, since the algorithm derives it from the
value version (`refines.writeCaptured`).
-/
public structure PromotionModelImpl.refines (pmI : PromotionModelImpl) (pm : PromotionModel) :
    Prop where
  /-- The promoted types agree. -/
  promotedTypes : pmI.promotedTypes = pm.promotedTypes.val
  /-- The tested types agree, as sets. -/
  tested : ∀ T, T ∈ pmI.tested ↔ T ∈ pm.tested
  /-- The definite-assignment flags agree. -/
  assigned : pmI.assigned = pm.assigned
  /-- The definite-unassignment flags agree. -/
  unassigned : pmI.unassigned = pm.unassigned
  /-- The value versions agree. -/
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
public theorem PromotionModelImpl.refines.unassigned' {pmI : PromotionModelImpl}
    {pm : PromotionModel} (h : PromotionModelImpl.refines pmI pm) :
    (pmI.unassigned = pm.unassigned) ↔ True := by
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
both `pm₁` (`h₁`) and `pm₂` (`h₂`), then `pm₁ = pm₂`.
-/
public theorem PromotionModelImpl.refines.unique {pmI : PromotionModelImpl}
    {pm₁ pm₂ : PromotionModel} (h₁ : pmI.refines pm₁) (h₂ : pmI.refines pm₂) : pm₁ = pm₂ := by
  ext1
  case promotedTypes => ext1; rw [←h₁.promotedTypes, ←h₂.promotedTypes]
  case tested => ext; rw [←h₁.tested, ←h₂.tested]
  case assigned => rw [←h₁.assigned, ←h₂.assigned]
  case unassigned => rw [←h₁.unassigned, ←h₂.unassigned]
  case version? => rw [←h₁.version?, ←h₂.version?]
  case writeCaptured => rw [←h₁.writeCaptured, ←h₂.writeCaptured]

/--
If `pmI` refines `pm` (`hrefines`), they agree about a variable's current type, for any declared
type `baseType` (`pmI.currentType baseType = pm.currentType baseType`).
-/
public theorem PromotionModelImpl.refines.currentTypes {pmI : PromotionModelImpl}
    {pm : PromotionModel} {baseType : τ} (hrefines : pmI.refines pm) :
    pmI.currentType baseType = pm.currentType baseType := by
  simp only [PromotionModelImpl.currentType, PromotionModelImpl.promotedType?,
    PromotionModel.currentType, hrefines.promotedTypes]
  cases pm.promotedTypes.val.getLast? <;> rfl

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
Joins preserve refinement: if `pmI₁` refines `pm₁` (`hrefines₁`) and `pmI₂` refines `pm₂`
(`hrefines₂`), then `pmI₁.join pmI₂` refines `pm₁.join pm₂`.
-/
public theorem PromotionModelImpl.refines.join [DecidableEq ℓ] {pmI₁ pmI₂ : PromotionModelImpl}
    {pm₁ pm₂ : PromotionModel} (hrefines₁ : pmI₁.refines pm₁) (hrefines₂ : pmI₂.refines pm₂) :
    (pmI₁.join pmI₂).refines (pm₁.join pm₂) := by
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
