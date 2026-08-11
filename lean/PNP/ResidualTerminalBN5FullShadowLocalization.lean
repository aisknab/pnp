/-
Copyright (c) 2026 PNP Labs.

Executable finite full-shadow localization above BN4 activation-exact
cancellation.  This module reconstructs the combinatorial core of the pinned
manuscript's Section 11.4 theorem `BN5-FullShadowLocalization` uniformly for
arbitrary finite carrier sizes and arbitrary finite shadow ledgers.

A negative BN4 residual mass is refined into canonically indexed unit full
atoms.  Every atom and quotient candidate retains one complete shadow
coordinate: the BN4 activation-exact key together with frontier, charge-owner,
obligation, origin/kernel, and mode-projection records.  Equality of shadow
coordinates is therefore equality of every field named at this boundary.

The executable classifier compares exact-coordinate multiplicities.  It
returns either complete multiplicity coverage or a proof-bearing Hall deficit
whose exact-coordinate quotient neighborhood is strictly smaller than its
full-unit subset.  A total wrapper rejects a malformed unit refinement,
computes cut silence from the activation code, and sends every cut-active Hall
deficit to the named local X1 Hall route.  Thus a refined cut-active negative
unit cannot disappear through an unclassified silent branch.

The full-unit payloads and quotient shadow candidates remain explicit finite
inputs.  This module does not derive them from four-corner bases, turn complete
coverage into a contradiction with the BN4 ledger, diagnose the complete
CritC/Q/E/L/X2/X3/X4 route family, construct PkgC or BN6, prove polynomial
generation or runtime, complete global routing, prove ZeroSlack or PCCMin, put
SAT in P, or prove P = NP.
-/

import PNP.ResidualTerminalBN4ActivationCancellation

namespace PNP
namespace DirectWire

/-! ## Complete full-shadow coordinates -/

/-- The records beyond the BN4 activation-exact key that the pinned BN5 shadow
    graph requires an edge to preserve.  These are typed data, not caller-
    supplied correctness certificates. -/
structure TerminalBN5ShadowPayload
    (Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type) where
  frontier : Frontier
  chargeOwner : ChargeOwner
  obligation : Obligation
  originKernel : OriginKernel
  modeProjection : ModeProjection
deriving DecidableEq

/-- One complete BN5 shadow coordinate.  The nested BN4 key already retains
    the activation atom, semantic signature, and transport type. -/
structure TerminalBN5ShadowCoordinate
    (Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type) where
  key : TerminalBN4ActivationKey Atom SemanticSignature TransportType
  frontier : Frontier
  chargeOwner : ChargeOwner
  obligation : Obligation
  originKernel : OriginKernel
  modeProjection : ModeProjection
deriving DecidableEq

/-- Attach one explicit BN5 payload to the exact negative BN4 key. -/
def TerminalBN5ShadowPayload.toCoordinate
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    (payload : TerminalBN5ShadowPayload
      Frontier ChargeOwner Obligation OriginKernel ModeProjection)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType) :
    TerminalBN5ShadowCoordinate Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection :=
  { key := key
    frontier := payload.frontier
    chargeOwner := payload.chargeOwner
    obligation := payload.obligation
    originKernel := payload.originKernel
    modeProjection := payload.modeProjection }

/-- Coordinate equality preserves every field named by the finite BN5 edge
    relation. -/
theorem terminalBN5ShadowCoordinate_eq_iff
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    (left right : TerminalBN5ShadowCoordinate Atom SemanticSignature
      TransportType Frontier ChargeOwner Obligation OriginKernel
      ModeProjection) :
    left = right ↔
      left.key = right.key ∧
      left.frontier = right.frontier ∧
      left.chargeOwner = right.chargeOwner ∧
      left.obligation = right.obligation ∧
      left.originKernel = right.originKernel ∧
      left.modeProjection = right.modeProjection := by
  constructor
  · intro equal
    subst right
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨keyEqual, frontierEqual, chargeEqual, obligationEqual,
      originKernelEqual, modeEqual⟩
    cases left
    cases right
    cases keyEqual
    cases frontierEqual
    cases chargeEqual
    cases obligationEqual
    cases originKernelEqual
    cases modeEqual
    rfl

/-! ## Canonically indexed unit atoms and quotient shadows -/

/-- One unit of negative full residual mass.  The ordinal is generated from
    list position and is not accepted independently from a caller. -/
structure TerminalBN5FullUnit (Coordinate : Type) where
  ordinal : Nat
  coordinate : Coordinate
deriving DecidableEq

/-- One unit quotient-shadow candidate.  Its ordinal is likewise generated
    from canonical list position. -/
structure TerminalBN5QuotientShadow (Coordinate : Type) where
  ordinal : Nat
  coordinate : Coordinate
deriving DecidableEq

/-- Index a full-coordinate list from an explicit starting ordinal. -/
def terminalBN5IndexFullUnitsFrom {Coordinate : Type} :
    Nat -> List Coordinate -> List (TerminalBN5FullUnit Coordinate)
  | _, [] => []
  | start, coordinate :: tail =>
      { ordinal := start, coordinate := coordinate } ::
        terminalBN5IndexFullUnitsFrom start.succ tail

/-- Index a quotient-coordinate list from an explicit starting ordinal. -/
def terminalBN5IndexQuotientShadowsFrom {Coordinate : Type} :
    Nat -> List Coordinate -> List (TerminalBN5QuotientShadow Coordinate)
  | _, [] => []
  | start, coordinate :: tail =>
      { ordinal := start, coordinate := coordinate } ::
        terminalBN5IndexQuotientShadowsFrom start.succ tail

/-- Canonical unit full atoms at one exact negative BN4 key. -/
def terminalBN5FullUnits
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (payloads : List (TerminalBN5ShadowPayload
      Frontier ChargeOwner Obligation OriginKernel ModeProjection)) :
    List (TerminalBN5FullUnit (TerminalBN5ShadowCoordinate Atom
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection)) :=
  terminalBN5IndexFullUnitsFrom 0
    (payloads.map fun payload => payload.toCoordinate key)

/-- Canonical quotient-shadow units from the explicit candidate coordinates. -/
def terminalBN5QuotientShadows {Coordinate : Type}
    (coordinates : List Coordinate) :
    List (TerminalBN5QuotientShadow Coordinate) :=
  terminalBN5IndexQuotientShadowsFrom 0 coordinates

theorem terminalBN5IndexFullUnitsFrom_length
    {Coordinate : Type} (start : Nat) (coordinates : List Coordinate) :
    (terminalBN5IndexFullUnitsFrom start coordinates).length =
      coordinates.length := by
  induction coordinates generalizing start with
  | nil => rfl
  | cons coordinate tail ih =>
      simp [terminalBN5IndexFullUnitsFrom, ih]

theorem terminalBN5IndexQuotientShadowsFrom_length
    {Coordinate : Type} (start : Nat) (coordinates : List Coordinate) :
    (terminalBN5IndexQuotientShadowsFrom start coordinates).length =
      coordinates.length := by
  induction coordinates generalizing start with
  | nil => rfl
  | cons coordinate tail ih =>
      simp [terminalBN5IndexQuotientShadowsFrom, ih]

theorem terminalBN5IndexFullUnitsFrom_coordinates
    {Coordinate : Type} (start : Nat) (coordinates : List Coordinate) :
    (terminalBN5IndexFullUnitsFrom start coordinates).map
        TerminalBN5FullUnit.coordinate = coordinates := by
  induction coordinates generalizing start with
  | nil => rfl
  | cons coordinate tail ih =>
      simp [terminalBN5IndexFullUnitsFrom, ih]

theorem terminalBN5IndexQuotientShadowsFrom_coordinates
    {Coordinate : Type} (start : Nat) (coordinates : List Coordinate) :
    (terminalBN5IndexQuotientShadowsFrom start coordinates).map
        TerminalBN5QuotientShadow.coordinate = coordinates := by
  induction coordinates generalizing start with
  | nil => rfl
  | cons coordinate tail ih =>
      simp [terminalBN5IndexQuotientShadowsFrom, ih]

/-- Unit refinement preserves the exact supplied negative mass length. -/
theorem terminalBN5FullUnits_length
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (payloads : List (TerminalBN5ShadowPayload
      Frontier ChargeOwner Obligation OriginKernel ModeProjection)) :
    (terminalBN5FullUnits key payloads).length = payloads.length := by
  unfold terminalBN5FullUnits
  rw [terminalBN5IndexFullUnitsFrom_length]
  simp

/-- Every generated full unit retains the one exact negative BN4 key. -/
theorem terminalBN5FullUnits_key_eq
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (payloads : List (TerminalBN5ShadowPayload
      Frontier ChargeOwner Obligation OriginKernel ModeProjection))
    (unit : TerminalBN5FullUnit (TerminalBN5ShadowCoordinate Atom
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection))
    (member : unit ∈ terminalBN5FullUnits key payloads) :
    unit.coordinate.key = key := by
  have coordinateMember :
      unit.coordinate ∈
        (terminalBN5FullUnits key payloads).map
          TerminalBN5FullUnit.coordinate :=
    List.mem_map.mpr ⟨unit, member, rfl⟩
  unfold terminalBN5FullUnits at coordinateMember
  rw [terminalBN5IndexFullUnitsFrom_coordinates] at coordinateMember
  obtain ⟨payload, _, coordinateEqual⟩ :=
    List.mem_map.mp coordinateMember
  calc
    unit.coordinate.key = (payload.toCoordinate key).key :=
      congrArg TerminalBN5ShadowCoordinate.key coordinateEqual.symm
    _ = key := rfl

/-! ## Exact-coordinate multiplicity matching -/

/-- The BN5 shadow graph has an edge exactly when every complete coordinate
    field agrees. -/
def TerminalBN5ShadowEdge {Coordinate : Type}
    (fullUnit : TerminalBN5FullUnit Coordinate)
    (shadow : TerminalBN5QuotientShadow Coordinate) : Prop :=
  fullUnit.coordinate = shadow.coordinate

/-- Number of full units at one complete coordinate. -/
def terminalBN5FullMultiplicity {Coordinate : Type}
    [DecidableEq Coordinate]
    (fullUnits : List (TerminalBN5FullUnit Coordinate))
    (coordinate : Coordinate) : Nat :=
  (fullUnits.filter fun unit => decide (unit.coordinate = coordinate)).length

/-- Number of quotient candidates at one complete coordinate. -/
def terminalBN5ShadowMultiplicity {Coordinate : Type}
    [DecidableEq Coordinate]
    (shadows : List (TerminalBN5QuotientShadow Coordinate))
    (coordinate : Coordinate) : Nat :=
  (shadows.filter fun shadow =>
    decide (shadow.coordinate = coordinate)).length

/-- Complete multiplicity coverage for the equality-fibre shadow graph.  For
    every full unit, there are at least as many exact-coordinate quotient
    shadows as full units in its fibre. -/
def TerminalBN5CompleteMultiplicityMatching {Coordinate : Type}
    [DecidableEq Coordinate]
    (fullUnits : List (TerminalBN5FullUnit Coordinate))
    (shadows : List (TerminalBN5QuotientShadow Coordinate)) : Prop :=
  ∀ unit, unit ∈ fullUnits ->
    terminalBN5FullMultiplicity fullUnits unit.coordinate ≤
      terminalBN5ShadowMultiplicity shadows unit.coordinate

/-- A Hall witness for one exact-coordinate fibre.  Its full subset and
    quotient neighborhood are computed by equality with `coordinate`. -/
structure TerminalBN5HallDeficit {Coordinate : Type}
    [DecidableEq Coordinate]
    (fullUnits : List (TerminalBN5FullUnit Coordinate))
    (shadows : List (TerminalBN5QuotientShadow Coordinate)) where
  coordinate : Coordinate
  fullUnit : TerminalBN5FullUnit Coordinate
  fullMember : fullUnit ∈ fullUnits
  fullCoordinate : fullUnit.coordinate = coordinate
  strictDeficit :
    terminalBN5ShadowMultiplicity shadows coordinate <
      terminalBN5FullMultiplicity fullUnits coordinate

def TerminalBN5HallDeficit.fullSubset
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {shadows : List (TerminalBN5QuotientShadow Coordinate)}
    (deficit : TerminalBN5HallDeficit fullUnits shadows) :
    List (TerminalBN5FullUnit Coordinate) :=
  fullUnits.filter fun unit => decide (unit.coordinate = deficit.coordinate)

def TerminalBN5HallDeficit.neighborShadows
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {shadows : List (TerminalBN5QuotientShadow Coordinate)}
    (deficit : TerminalBN5HallDeficit fullUnits shadows) :
    List (TerminalBN5QuotientShadow Coordinate) :=
  shadows.filter fun shadow =>
    decide (shadow.coordinate = deficit.coordinate)

/-- The returned witness is a literal Hall deficit: its exact-coordinate
    neighborhood is strictly smaller than its full-unit subset. -/
theorem TerminalBN5HallDeficit.neighbor_card_lt_full_card
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {shadows : List (TerminalBN5QuotientShadow Coordinate)}
    (deficit : TerminalBN5HallDeficit fullUnits shadows) :
    deficit.neighborShadows.length < deficit.fullSubset.length := by
  exact deficit.strictDeficit

/-- Every member of the deficient full subset has the witness coordinate. -/
theorem TerminalBN5HallDeficit.fullSubset_coordinate_eq
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {shadows : List (TerminalBN5QuotientShadow Coordinate)}
    (deficit : TerminalBN5HallDeficit fullUnits shadows)
    (unit : TerminalBN5FullUnit Coordinate)
    (member : unit ∈ deficit.fullSubset) :
    unit.coordinate = deficit.coordinate := by
  simp [TerminalBN5HallDeficit.fullSubset] at member
  exact member.2

/-- Every neighbor in the Hall witness preserves the same complete coordinate. -/
theorem TerminalBN5HallDeficit.neighbor_coordinate_eq
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {shadows : List (TerminalBN5QuotientShadow Coordinate)}
    (deficit : TerminalBN5HallDeficit fullUnits shadows)
    (shadow : TerminalBN5QuotientShadow Coordinate)
    (member : shadow ∈ deficit.neighborShadows) :
    shadow.coordinate = deficit.coordinate := by
  simp [TerminalBN5HallDeficit.neighborShadows] at member
  exact member.2

private inductive TerminalBN5UnitCoverage
    {Coordinate : Type} [DecidableEq Coordinate]
    (fullUnits : List (TerminalBN5FullUnit Coordinate))
    (shadows : List (TerminalBN5QuotientShadow Coordinate)) :
    List (TerminalBN5FullUnit Coordinate) -> Type where
  | covered {units}
      (coverage : ∀ unit, unit ∈ units ->
        terminalBN5FullMultiplicity fullUnits unit.coordinate ≤
          terminalBN5ShadowMultiplicity shadows unit.coordinate) :
      TerminalBN5UnitCoverage fullUnits shadows units
  | deficit {units}
      (unit : TerminalBN5FullUnit Coordinate)
      (member : unit ∈ units)
      (strictDeficit :
        terminalBN5ShadowMultiplicity shadows unit.coordinate <
          terminalBN5FullMultiplicity fullUnits unit.coordinate) :
      TerminalBN5UnitCoverage fullUnits shadows units

private def classifyTerminalBN5UnitCoverage
    {Coordinate : Type} [DecidableEq Coordinate]
    (fullUnits : List (TerminalBN5FullUnit Coordinate))
    (shadows : List (TerminalBN5QuotientShadow Coordinate)) :
    (units : List (TerminalBN5FullUnit Coordinate)) ->
      TerminalBN5UnitCoverage fullUnits shadows units
  | [] => .covered (by simp)
  | unit :: tail =>
      if strictDeficit :
          terminalBN5ShadowMultiplicity shadows unit.coordinate <
            terminalBN5FullMultiplicity fullUnits unit.coordinate then
        .deficit unit (by simp) strictDeficit
      else
        match classifyTerminalBN5UnitCoverage fullUnits shadows tail with
        | .deficit found member foundDeficit =>
            .deficit found (by simp [member]) foundDeficit
        | .covered tailCoverage =>
            .covered (by
              intro found member
              simp only [List.mem_cons] at member
              cases member with
              | inl equal =>
                  subst found
                  omega
              | inr tailMember =>
                  exact tailCoverage found tailMember)

/-- Proof-bearing result of the executable exact-coordinate shadow scan. -/
inductive TerminalBN5ShadowMatchingOutcome
    {Coordinate : Type} [DecidableEq Coordinate]
    (fullUnits : List (TerminalBN5FullUnit Coordinate))
    (shadows : List (TerminalBN5QuotientShadow Coordinate)) where
  | matched
      (matching : TerminalBN5CompleteMultiplicityMatching fullUnits shadows)
  | hallDeficit (deficit : TerminalBN5HallDeficit fullUnits shadows)

/-- Scan the complete coordinate of every full unit.  The first deficient
    coordinate in full-unit order is returned; otherwise every equality fibre
    has enough quotient multiplicity. -/
def classifyTerminalBN5ShadowMatching
    {Coordinate : Type} [DecidableEq Coordinate]
    (fullUnits : List (TerminalBN5FullUnit Coordinate))
    (shadows : List (TerminalBN5QuotientShadow Coordinate)) :
    TerminalBN5ShadowMatchingOutcome fullUnits shadows :=
  match classifyTerminalBN5UnitCoverage fullUnits shadows fullUnits with
  | .covered coverage => .matched coverage
  | .deficit unit member strictDeficit =>
      .hallDeficit
        { coordinate := unit.coordinate
          fullUnit := unit
          fullMember := member
          fullCoordinate := rfl
          strictDeficit := strictDeficit }

/-- There is no third matching result outside complete multiplicity coverage
    or a concrete Hall deficit. -/
theorem classifyTerminalBN5ShadowMatching_exhaustive
    {Coordinate : Type} [DecidableEq Coordinate]
    (fullUnits : List (TerminalBN5FullUnit Coordinate))
    (shadows : List (TerminalBN5QuotientShadow Coordinate)) :
    Nonempty (TerminalBN5ShadowMatchingOutcome fullUnits shadows) :=
  ⟨classifyTerminalBN5ShadowMatching fullUnits shadows⟩

/-! ## BN4-consuming total localization wrapper -/

/-- Extract the strictly positive residual mass exactly when BN4 returned its
    negative branch. -/
def TerminalBN4KeyCancellation.negativeResidualMass?
    {positiveMass negativeMass : Nat}
    (cancellation : TerminalBN4KeyCancellation positiveMass negativeMass) :
    Option Nat :=
  match cancellation with
  | .negative mass _ _ => some mass
  | _ => none

/-- Every extracted negative BN4 residual mass is strictly positive. -/
theorem TerminalBN4KeyCancellation.negativeResidualMass?_positive
    {positiveMass negativeMass mass : Nat}
    (cancellation : TerminalBN4KeyCancellation positiveMass negativeMass)
    (found : cancellation.negativeResidualMass? = some mass) :
    0 < mass := by
  cases cancellation with
  | balanced exact =>
      simp [TerminalBN4KeyCancellation.negativeResidualMass?] at found
  | positive residual positive exact =>
      simp [TerminalBN4KeyCancellation.negativeResidualMass?] at found
  | negative residual positive exact =>
      simp [TerminalBN4KeyCancellation.negativeResidualMass?] at found
      subst mass
      exact positive

/-- The one named local route that is justified solely by a proved Hall
    deficit at this boundary.  More specific coordinate diagnoses remain a
    downstream global-route obligation. -/
inductive TerminalBN5NamedLocalRoute where
  | x1Hall
deriving DecidableEq, Repr

/-- A Hall deficit deterministically emits the named X1 route; callers cannot
    relabel it. -/
def TerminalBN5HallDeficit.namedLocalRoute
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {shadows : List (TerminalBN5QuotientShadow Coordinate)}
    (_ : TerminalBN5HallDeficit fullUnits shadows) :
    TerminalBN5NamedLocalRoute :=
  .x1Hall

@[simp] theorem TerminalBN5HallDeficit.namedLocalRoute_eq_x1Hall
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {shadows : List (TerminalBN5QuotientShadow Coordinate)}
    (deficit : TerminalBN5HallDeficit fullUnits shadows) :
    deficit.namedLocalRoute = .x1Hall :=
  rfl

/-- Total result for one BN4 cancellation key, one cut, one proposed unit-mass
    refinement, and one explicit quotient-shadow universe. -/
inductive TerminalBN5FullShadowLocalizationOutcome
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {positiveMass negativeMass : Nat}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    (cancellation : TerminalBN4KeyCancellation positiveMass negativeMass)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (cut : List Atom)
    (payloads : List (TerminalBN5ShadowPayload
      Frontier ChargeOwner Obligation OriginKernel ModeProjection))
    (shadowCoordinates : List (TerminalBN5ShadowCoordinate Atom
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection)) where
  | noNegativeResidual
      (exact : cancellation.negativeResidualMass? = none)
  | invalidUnitRefinement
      (mass : Nat)
      (negativeExact : cancellation.negativeResidualMass? = some mass)
      (massPositive : 0 < mass)
      (lengthMismatch : payloads.length ≠ mass)
  | cutSilent
      (mass : Nat)
      (negativeExact : cancellation.negativeResidualMass? = some mass)
      (massPositive : 0 < mass)
      (refinesMass : payloads.length = mass)
      (inactive : ¬ TerminalBN4CodeActive
        (terminalBN4ActivationCode key.atom) cut)
  | matched
      (mass : Nat)
      (negativeExact : cancellation.negativeResidualMass? = some mass)
      (massPositive : 0 < mass)
      (refinesMass : payloads.length = mass)
      (active : TerminalBN4CodeActive
        (terminalBN4ActivationCode key.atom) cut)
      (matching : TerminalBN5CompleteMultiplicityMatching
        (terminalBN5FullUnits key payloads)
        (terminalBN5QuotientShadows shadowCoordinates))
  | localized
      (mass : Nat)
      (negativeExact : cancellation.negativeResidualMass? = some mass)
      (massPositive : 0 < mass)
      (refinesMass : payloads.length = mass)
      (active : TerminalBN4CodeActive
        (terminalBN4ActivationCode key.atom) cut)
      (deficit : TerminalBN5HallDeficit
        (terminalBN5FullUnits key payloads)
        (terminalBN5QuotientShadows shadowCoordinates))

private def terminalBN5CodeActiveDecidable
    {Atom : Type} [DecidableEq Atom]
    (atom : Atom) (cut : List Atom) :
    Decidable (TerminalBN4CodeActive (terminalBN4ActivationCode atom) cut) := by
  unfold TerminalBN4CodeActive terminalBN4ActivationCode
    terminalBN3MinimalConsumer
  infer_instance

/-- Validate the negative-unit refinement, compute cut silence, then run the
    exact-coordinate shadow classifier. -/
def classifyTerminalBN5FullShadowLocalization
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {positiveMass negativeMass : Nat}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    (cancellation : TerminalBN4KeyCancellation positiveMass negativeMass)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (cut : List Atom)
    (payloads : List (TerminalBN5ShadowPayload
      Frontier ChargeOwner Obligation OriginKernel ModeProjection))
    (shadowCoordinates : List (TerminalBN5ShadowCoordinate Atom
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection)) :
    TerminalBN5FullShadowLocalizationOutcome cancellation key cut payloads
      shadowCoordinates :=
  match cancellation with
  | .balanced _ => .noNegativeResidual rfl
  | .positive _ _ _ => .noNegativeResidual rfl
  | .negative mass massPositive _ =>
      if refinesMass : payloads.length = mass then
        letI : Decidable (TerminalBN4CodeActive
            (terminalBN4ActivationCode key.atom) cut) :=
          terminalBN5CodeActiveDecidable key.atom cut
        if active : TerminalBN4CodeActive
            (terminalBN4ActivationCode key.atom) cut then
          match classifyTerminalBN5ShadowMatching
              (terminalBN5FullUnits key payloads)
              (terminalBN5QuotientShadows shadowCoordinates) with
          | .matched matching =>
              .matched mass rfl massPositive refinesMass active
                matching
          | .hallDeficit deficit =>
              .localized mass rfl massPositive refinesMass active
                deficit
        else
          .cutSilent mass rfl massPositive refinesMass active
      else
        .invalidUnitRefinement mass rfl massPositive refinesMass

/-- Valid cut-active negative refinements cannot enter the no-negative,
    malformed-refinement, or cut-silent branches. -/
def TerminalBN5FullShadowLocalizationOutcome.ActiveMatchedOrLocalized
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {positiveMass negativeMass : Nat}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    {cancellation : TerminalBN4KeyCancellation positiveMass negativeMass}
    {key : TerminalBN4ActivationKey Atom SemanticSignature TransportType}
    {cut : List Atom}
    {payloads : List (TerminalBN5ShadowPayload
      Frontier ChargeOwner Obligation OriginKernel ModeProjection)}
    {shadowCoordinates : List (TerminalBN5ShadowCoordinate Atom
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection)}
    (outcome : TerminalBN5FullShadowLocalizationOutcome cancellation key cut
      payloads shadowCoordinates) : Prop :=
  match outcome with
  | .matched .. => True
  | .localized .. => True
  | _ => False

/-- This is the reconstructed finite `negativeFullResidualLocalized` core: an
    exact, cut-active negative-mass refinement is either completely covered or
    exposes a proof-bearing Hall deficit. -/
theorem classifyTerminalBN5FullShadowLocalization_active
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {positiveMass negativeMass mass : Nat}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    (cancellation : TerminalBN4KeyCancellation positiveMass negativeMass)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (cut : List Atom)
    (payloads : List (TerminalBN5ShadowPayload
      Frontier ChargeOwner Obligation OriginKernel ModeProjection))
    (shadowCoordinates : List (TerminalBN5ShadowCoordinate Atom
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection))
    (negativeExact : cancellation.negativeResidualMass? = some mass)
    (refinesMass : payloads.length = mass)
    (active : TerminalBN4CodeActive
      (terminalBN4ActivationCode key.atom) cut) :
    (classifyTerminalBN5FullShadowLocalization cancellation key cut payloads
      shadowCoordinates).ActiveMatchedOrLocalized := by
  cases cancellation with
  | balanced exact =>
      simp [TerminalBN4KeyCancellation.negativeResidualMass?] at negativeExact
  | positive residual residualPositive exact =>
      simp [TerminalBN4KeyCancellation.negativeResidualMass?] at negativeExact
  | negative residual residualPositive exact =>
      simp [TerminalBN4KeyCancellation.negativeResidualMass?] at negativeExact
      subst mass
      cases matchingResult : classifyTerminalBN5ShadowMatching
          (terminalBN5FullUnits key payloads)
          (terminalBN5QuotientShadows shadowCoordinates) with
      | matched matching =>
          simp [classifyTerminalBN5FullShadowLocalization,
            negativeExact.symm, active, matchingResult,
            TerminalBN5FullShadowLocalizationOutcome.ActiveMatchedOrLocalized]
      | hallDeficit deficit =>
          simp [classifyTerminalBN5FullShadowLocalization,
            negativeExact.symm, active, matchingResult,
            TerminalBN5FullShadowLocalizationOutcome.ActiveMatchedOrLocalized]

/-- Every localized Hall obstruction has a named route and a strict Hall
    inequality, so an unmatched full unit cannot be silently discarded. -/
theorem TerminalBN5HallDeficit.unmatchedShadowNotSilent
    {Coordinate : Type} [DecidableEq Coordinate]
    {fullUnits : List (TerminalBN5FullUnit Coordinate)}
    {shadows : List (TerminalBN5QuotientShadow Coordinate)}
    (deficit : TerminalBN5HallDeficit fullUnits shadows) :
    deficit.namedLocalRoute = .x1Hall ∧
      deficit.neighborShadows.length < deficit.fullSubset.length :=
  ⟨rfl, deficit.neighbor_card_lt_full_card⟩

/-- No sixth unclassified local BN5 result exists. -/
theorem classifyTerminalBN5FullShadowLocalization_exhaustive
    {Atom SemanticSignature TransportType
      Frontier ChargeOwner Obligation OriginKernel ModeProjection : Type}
    {positiveMass negativeMass : Nat}
    [DecidableEq Atom] [DecidableEq SemanticSignature]
    [DecidableEq TransportType] [DecidableEq Frontier]
    [DecidableEq ChargeOwner] [DecidableEq Obligation]
    [DecidableEq OriginKernel] [DecidableEq ModeProjection]
    (cancellation : TerminalBN4KeyCancellation positiveMass negativeMass)
    (key : TerminalBN4ActivationKey Atom SemanticSignature TransportType)
    (cut : List Atom)
    (payloads : List (TerminalBN5ShadowPayload
      Frontier ChargeOwner Obligation OriginKernel ModeProjection))
    (shadowCoordinates : List (TerminalBN5ShadowCoordinate Atom
      SemanticSignature TransportType Frontier ChargeOwner Obligation
      OriginKernel ModeProjection)) :
    Nonempty (TerminalBN5FullShadowLocalizationOutcome cancellation key cut
      payloads shadowCoordinates) :=
  ⟨classifyTerminalBN5FullShadowLocalization cancellation key cut payloads
    shadowCoordinates⟩

end DirectWire
end PNP
