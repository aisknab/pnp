/-
Copyright (c) 2026 PNP Labs.

Deterministic coherence classification for the four canonical optimum
realizers attached to every finite computed terminal support square.  The
classifier follows the four physical square legs, compares semantics only at
outputs retained by both endpoints, and compares profile observations in the
canonical ten-role and coordinate order.  Full mode also rejects the first
open obligation.  Quotient mode checks only retained profile coordinates and
remains comparison-only; a separate fail-closed query reports the first
forgotten mismatch that prevents treating it as a full-profile transport.

This reconstructs the next part of the `BN2-CoherentOptimum` paragraph in
Section 11.1 of the pinned manuscript: either the independently attained
side-tight optima form one checked square tuple, or the finite classifier
returns the exact first obstruction.  It does not prove that the coherent
branch always occurs, identify an obstruction with a later no-outcome route,
prove `sideTightCompletionExists`, establish BN2 square legitimacy, or prove
SaturatePositive, BCELReady, ZeroSlack, polynomial runtime, SAT in P, or
P = NP.
-/

import PNP.ResidualTerminalFourCornerOptimumCompatibility

namespace PNP
namespace DirectWire

/-- The profile discipline used by one optimum-coherence classification. -/
inductive TerminalOptimumCoherenceMode where
  | full
  | quotient
  deriving Repr, DecidableEq

/-- The four directed inclusions in the terminal support square. -/
inductive TerminalOptimumSquareLeg where
  | meetLeft
  | meetRight
  | leftJoin
  | rightJoin
  deriving Repr, DecidableEq

/-- Deterministic manuscript order for the four directed square legs. -/
def allTerminalOptimumSquareLegs : List TerminalOptimumSquareLeg :=
  [.meetLeft, .meetRight, .leftJoin, .rightJoin]

/-- Source corner of one directed square leg. -/
def TerminalOptimumSquareLeg.source :
    TerminalOptimumSquareLeg -> TerminalSupportSquareCorner
  | .meetLeft => .meet
  | .meetRight => .meet
  | .leftJoin => .left
  | .rightJoin => .right

/-- Target corner of one directed square leg. -/
def TerminalOptimumSquareLeg.target :
    TerminalOptimumSquareLeg -> TerminalSupportSquareCorner
  | .meetLeft => .left
  | .meetRight => .right
  | .leftJoin => .join
  | .rightJoin => .join

/-- Canonical transport data contains only the selected square leg.  Its
    support, profile, coordinate, and output actions are derived below from
    the computed carrier; no transport certificate is supplied by a caller. -/
structure TerminalOptimumLegTransport
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (_carrier : TerminalFourCornerCarrier system) where
  leg : TerminalOptimumSquareLeg

/-- Derive one square-leg transport from the computed carrier. -/
def TerminalFourCornerCarrier.optimumLegTransport
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (leg : TerminalOptimumSquareLeg) :
    TerminalOptimumLegTransport carrier :=
  ⟨leg⟩

/-- Every canonical optimum leg is backed by the corresponding computed
    support inclusion. -/
theorem TerminalOptimumLegTransport.recordsSubset
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (transport : TerminalOptimumLegTransport carrier) :
    TerminalRawSupport.Subset
      (fun record => record ∈ carrier.square.records transport.leg.source)
      (fun record => record ∈ carrier.square.records transport.leg.target) := by
  cases transport with
  | mk leg =>
      cases leg with
      | meetLeft => exact carrier.square.meetRecords_subset_left
      | meetRight => exact carrier.square.meetRecords_subset_right
      | leftJoin => exact carrier.square.leftRecords_subset_join
      | rightJoin => exact carrier.square.rightRecords_subset_join

/-- Profile coordinates move unchanged along every directed square leg. -/
theorem TerminalOptimumLegTransport.profileTransport
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (transport : TerminalOptimumLegTransport carrier)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth)
    (member : coordinate ∈
      (carrier.support transport.leg.source).frontier.profiles role) :
    coordinate ∈
      (carrier.support transport.leg.target).frontier.profiles role := by
  cases transport with
  | mk leg =>
      cases leg with
      | meetLeft =>
          exact (carrier.meet_profile_transport role coordinate).1 member |>.1
      | meetRight =>
          exact (carrier.meet_profile_transport role coordinate).1 member |>.2
      | leftJoin =>
          exact carrier.side_profile_transport .left role coordinate member
      | rightJoin =>
          exact carrier.side_profile_transport .right role coordinate member

/-- Physical transport uses the exact common ambient coordinate. -/
def TerminalOptimumLegTransport.ambientCoordinate
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (_transport : TerminalOptimumLegTransport carrier) :
    Fin (inputs + gates) -> Fin (inputs + gates) :=
  fun coordinate => coordinate

/-- Ambient physical coordinates are retained literally, not renumbered. -/
@[simp] theorem TerminalOptimumLegTransport.ambientCoordinate_exact
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (transport : TerminalOptimumLegTransport carrier)
    (coordinate : Fin (inputs + gates)) :
    transport.ambientCoordinate coordinate = coordinate :=
  rfl

/-- Locate the target output carrying the same ambient producer as one source
    output.  `none` is the exact internalized-output case. -/
def TerminalOptimumLegTransport.retainedOutput?
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (transport : TerminalOptimumLegTransport carrier)
    (sourceIndex :
      Fin (carrier.extracted transport.leg.source).interface.length) :
    Option (Fin (carrier.extracted transport.leg.target).interface.length) :=
  carrier.interfaceIndex? transport.leg.target
    ((carrier.extracted transport.leg.source).interface.get sourceIndex)

/-- A retained output has exactly the same ambient gate producer at the two
    endpoints. -/
theorem TerminalOptimumLegTransport.retainedOutput?_eq_some_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (transport : TerminalOptimumLegTransport carrier)
    (sourceIndex :
      Fin (carrier.extracted transport.leg.source).interface.length)
    (targetIndex :
      Fin (carrier.extracted transport.leg.target).interface.length) :
    transport.retainedOutput? sourceIndex = some targetIndex ↔
      (carrier.extracted transport.leg.target).interface.get targetIndex =
        (carrier.extracted transport.leg.source).interface.get sourceIndex :=
  carrier.interfaceIndex?_eq_some_iff transport.leg.target _ targetIndex

/-- Exact fail-closed definition of an internalized source output. -/
def TerminalOptimumLegTransport.OutputInternalized
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (transport : TerminalOptimumLegTransport carrier)
    (sourceIndex :
      Fin (carrier.extracted transport.leg.source).interface.length) : Prop :=
  transport.retainedOutput? sourceIndex = none

/-- Every source output is deterministically retained or internalized. -/
theorem TerminalOptimumLegTransport.retained_or_internalized
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    (transport : TerminalOptimumLegTransport carrier)
    (sourceIndex :
      Fin (carrier.extracted transport.leg.source).interface.length) :
    (∃ targetIndex, transport.retainedOutput? sourceIndex = some targetIndex) ∨
      transport.OutputInternalized sourceIndex := by
  cases found : transport.retainedOutput? sourceIndex with
  | none => exact Or.inr found
  | some targetIndex => exact Or.inl ⟨targetIndex, rfl⟩

/-- The two routes around the square commute on the common physical carrier. -/
theorem TerminalFourCornerCarrier.optimumTransportTheta
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (coordinate : Fin (inputs + gates)) :
    (carrier.optimumLegTransport .leftJoin).ambientCoordinate
        ((carrier.optimumLegTransport .meetLeft).ambientCoordinate coordinate) =
      (carrier.optimumLegTransport .rightJoin).ambientCoordinate
        ((carrier.optimumLegTransport .meetRight).ambientCoordinate coordinate) :=
  rfl

/-- Select the concrete canonical optimum implementation at one corner and
    in one profile mode. -/
def TerminalFourCornerOptimumFamily.implementationAt
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    {carrier : TerminalFourCornerCarrier system}
    {observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth}
    (family : TerminalFourCornerOptimumFamily carrier observe)
    (mode : TerminalOptimumCoherenceMode)
    (corner : TerminalSupportSquareCorner) :
    Implementation (inputs + gates) gates :=
  match mode with
  | .full => (family.fullBasis.at corner).realization.implementation
  | .quotient => (family.quotientBasis.at corner).realization.implementation

/-- Exact finite reason that a canonical four-corner optimum tuple failed a
    coherence or mode-firewall check. -/
inductive TerminalFourCornerOptimumFailure
    (ambientInputs gates profileWidth : Nat) where
  | openObligation
      (corner : TerminalSupportSquareCorner)
      (coordinate : Fin profileWidth)
      (actual : Bool)
  | semanticMismatch
      (leg : TerminalOptimumSquareLeg)
      (input : BoolTuple ambientInputs)
      (producer : Fin gates)
      (sourceValue targetValue : Bool)
  | profileMismatch
      (leg : TerminalOptimumSquareLeg)
      (role : TerminalProfileRole)
      (coordinate : Fin profileWidth)
      (sourceValue targetValue : Bool)
  | chargeProfileMismatch
      (leg : TerminalOptimumSquareLeg)
      (coordinate : Fin profileWidth)
      (sourceValue targetValue : Bool)
  | modeMismatch
      (leg : TerminalOptimumSquareLeg)
      (role : TerminalProfileRole)
      (coordinate : Fin profileWidth)
      (sourceValue targetValue : Bool)

/-- Semantic content carried by an emitted failure. -/
def TerminalFourCornerOptimumFailure.Sound
    {ambientInputs gates profileWidth : Nat} :
    TerminalFourCornerOptimumFailure ambientInputs gates profileWidth -> Prop
  | .openObligation _ _ actual => actual = true
  | .semanticMismatch _ _ _ sourceValue targetValue =>
      sourceValue ≠ targetValue
  | .profileMismatch _ _ _ sourceValue targetValue =>
      sourceValue ≠ targetValue
  | .chargeProfileMismatch _ _ sourceValue targetValue =>
      sourceValue ≠ targetValue
  | .modeMismatch _ _ _ sourceValue targetValue =>
      sourceValue ≠ targetValue

private structure TerminalOptimumCheck
    (ambientInputs gates profileWidth : Nat) where
  failure : TerminalFourCornerOptimumFailure
    ambientInputs gates profileWidth
  agrees : Bool
  failureSound : agrees = false -> failure.Sound

private theorem boolEqual_false_sound (left right : Bool)
    (checked : boolEqual left right = false) : left ≠ right := by
  intro equal
  cases equal
  cases left <;> cases checked

private def openObligationCheck
    {ambientInputs gates profileWidth : Nat}
    (corner : TerminalSupportSquareCorner)
    (coordinate : Fin profileWidth) (actual : Bool) :
    TerminalOptimumCheck ambientInputs gates profileWidth :=
  { failure := .openObligation corner coordinate actual
    agrees := !actual
    failureSound := by
      intro checked
      cases actual with
      | false => cases checked
      | true => rfl }

private def semanticCheck
    {ambientInputs gates profileWidth : Nat}
    (leg : TerminalOptimumSquareLeg) (input : BoolTuple ambientInputs)
    (producer : Fin gates) (sourceValue targetValue : Bool) :
    TerminalOptimumCheck ambientInputs gates profileWidth :=
  { failure := .semanticMismatch leg input producer sourceValue targetValue
    agrees := boolEqual sourceValue targetValue
    failureSound := boolEqual_false_sound sourceValue targetValue }

private def profileCheck
    {ambientInputs gates profileWidth : Nat}
    (leg : TerminalOptimumSquareLeg) (role : TerminalProfileRole)
    (coordinate : Fin profileWidth) (sourceValue targetValue : Bool) :
    TerminalOptimumCheck ambientInputs gates profileWidth :=
  { failure := match role with
      | .charge => .chargeProfileMismatch leg coordinate sourceValue targetValue
      | _ => .profileMismatch leg role coordinate sourceValue targetValue
    agrees := boolEqual sourceValue targetValue
    failureSound := by
      intro checked
      cases role <;>
        exact boolEqual_false_sound sourceValue targetValue checked }

private def modeCheck
    {ambientInputs gates profileWidth : Nat}
    (leg : TerminalOptimumSquareLeg) (role : TerminalProfileRole)
    (coordinate : Fin profileWidth) (sourceValue targetValue : Bool) :
    TerminalOptimumCheck ambientInputs gates profileWidth :=
  { failure := .modeMismatch leg role coordinate sourceValue targetValue
    agrees := boolEqual sourceValue targetValue
    failureSound := boolEqual_false_sound sourceValue targetValue }

private def terminalOptimumCornerOrder : List TerminalSupportSquareCorner :=
  [.meet, .left, .right, .join]

private def TerminalFourCornerCarrier.obligationChecks
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    List (TerminalOptimumCheck (inputs + gates) gates profileWidth) :=
  match mode with
  | .quotient => []
  | .full => terminalOptimumCornerOrder.flatMap fun corner =>
      (allFin profileWidth).flatMap fun coordinate =>
        if system.profileSystem.role coordinate = .obligation then
          [openObligationCheck corner coordinate
            (observe
              ((carrier.canonicalOptimumFamily observe).implementationAt
                .full corner) coordinate)]
        else
          []

private def TerminalFourCornerCarrier.semanticChecks
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (transport : TerminalOptimumLegTransport carrier) :
    List (TerminalOptimumCheck (inputs + gates) gates profileWidth) :=
  (allFin (carrier.extracted transport.leg.source).interface.length).flatMap
    fun sourceIndex =>
      match transport.retainedOutput? sourceIndex with
      | none => []
      | some _targetIndex =>
          let producer :=
            (carrier.extracted transport.leg.source).interface.get sourceIndex
          (allBoolTuples (inputs + gates)).map fun input =>
            semanticCheck transport.leg input producer
              (((carrier.canonicalOptimumFamily observe).implementationAt
                mode transport.leg.source).candidate.semantics
                  input.toValuation producer)
              (((carrier.canonicalOptimumFamily observe).implementationAt
                mode transport.leg.target).candidate.semantics
                  input.toValuation producer)

private def TerminalFourCornerCarrier.profileChecks
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (transport : TerminalOptimumLegTransport carrier) :
    List (TerminalOptimumCheck (inputs + gates) gates profileWidth) :=
  allTerminalProfileRoles.flatMap fun role =>
    ((carrier.support transport.leg.source).frontier.profiles role).flatMap
      fun coordinate =>
        let kept := match mode with
          | .full => true
          | .quotient => carrier.projection.keep coordinate
        if kept then
          [profileCheck transport.leg role coordinate
            (observe
              ((carrier.canonicalOptimumFamily observe).implementationAt
                mode transport.leg.source) coordinate)
            (observe
              ((carrier.canonicalOptimumFamily observe).implementationAt
                mode transport.leg.target) coordinate)]
        else
          []

private def TerminalFourCornerCarrier.forgottenModeChecks
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (transport : TerminalOptimumLegTransport carrier) :
    List (TerminalOptimumCheck (inputs + gates) gates profileWidth) :=
  allTerminalProfileRoles.flatMap fun role =>
    ((carrier.support transport.leg.source).frontier.profiles role).flatMap
      fun coordinate =>
        if carrier.projection.keep coordinate then
          []
        else
          [modeCheck transport.leg role coordinate
            (observe
              ((carrier.canonicalOptimumFamily observe).implementationAt
                .quotient transport.leg.source) coordinate)
            (observe
              ((carrier.canonicalOptimumFamily observe).implementationAt
                .quotient transport.leg.target) coordinate)]

private def TerminalFourCornerCarrier.coherenceChecks
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    List (TerminalOptimumCheck (inputs + gates) gates profileWidth) :=
  carrier.obligationChecks observe mode ++
    allTerminalOptimumSquareLegs.flatMap fun leg =>
      let transport := carrier.optimumLegTransport leg
      carrier.semanticChecks observe mode transport ++
        carrier.profileChecks observe mode transport

private def firstFailedCheck
    {ambientInputs gates profileWidth : Nat} :
    List (TerminalOptimumCheck ambientInputs gates profileWidth) ->
      Option (TerminalFourCornerOptimumFailure
        ambientInputs gates profileWidth)
  | [] => none
  | check :: tail =>
      if check.agrees then firstFailedCheck tail else some check.failure

private theorem firstFailedCheck_sound
    {ambientInputs gates profileWidth : Nat}
    (checks : List (TerminalOptimumCheck ambientInputs gates profileWidth))
    (failure : TerminalFourCornerOptimumFailure
      ambientInputs gates profileWidth)
    (found : firstFailedCheck checks = some failure) : failure.Sound := by
  induction checks with
  | nil => cases found
  | cons check tail ih =>
      unfold firstFailedCheck at found
      cases agreed : check.agrees with
      | false =>
          rw [agreed] at found
          cases found
          exact check.failureSound agreed
      | true =>
          rw [agreed] at found
          exact ih found

/-- First coherence failure in the exact obligation, leg, valuation, output,
    role, and coordinate order documented above. -/
def TerminalFourCornerCarrier.firstOptimumCoherenceFailure?
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    Option (TerminalFourCornerOptimumFailure
      (inputs + gates) gates profileWidth) :=
  firstFailedCheck (carrier.coherenceChecks observe mode)

/-- The first emitted coherence failure is a genuine Boolean mismatch or an
    actually open obligation. -/
theorem TerminalFourCornerCarrier.firstOptimumCoherenceFailure?_sound
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (failure : TerminalFourCornerOptimumFailure
      (inputs + gates) gates profileWidth)
    (found : carrier.firstOptimumCoherenceFailure? observe mode =
      some failure) : failure.Sound :=
  firstFailedCheck_sound (carrier.coherenceChecks observe mode) failure found

/-- First forgotten quotient-profile mismatch.  This query is deliberately
    separate from quotient coherence: it diagnoses why comparison-only
    evidence cannot be promoted to full transport. -/
def TerminalFourCornerCarrier.firstOptimumModeMismatch?
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth) :
    Option (TerminalFourCornerOptimumFailure
      (inputs + gates) gates profileWidth) :=
  firstFailedCheck <|
    allTerminalOptimumSquareLegs.flatMap fun leg =>
      carrier.forgottenModeChecks observe (carrier.optimumLegTransport leg)

/-- Every reported quotient mode mismatch is exact. -/
theorem TerminalFourCornerCarrier.firstOptimumModeMismatch?_sound
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (failure : TerminalFourCornerOptimumFailure
      (inputs + gates) gates profileWidth)
    (found : carrier.firstOptimumModeMismatch? observe = some failure) :
    failure.Sound :=
  firstFailedCheck_sound
    (allTerminalOptimumSquareLegs.flatMap fun leg =>
      carrier.forgottenModeChecks observe (carrier.optimumLegTransport leg))
    failure found

/-- A checked square-coherent canonical tuple.  The structure retains the
    exact side-tight size and incidence facts independently of the selected
    comparison mode. -/
structure TerminalFourCornerCoherentOptimumTuple
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) : Prop where
  carrierCompatible :
    (carrier.canonicalOptimumFamily observe).Compatible
  noFailure : carrier.firstOptimumCoherenceFailure? observe mode = none
  fullSizes :
    (carrier.canonicalOptimumFamily observe).fullBasis.sizes =
      (carrier.optimizationCorners observe).fullMinimumSizes
  quotientSizes :
    (carrier.canonicalOptimumFamily observe).quotientBasis.sizes =
      (carrier.optimizationCorners observe).quotientMinimumSizes
  fullSideTight :
    (carrier.canonicalOptimumFamily observe).fullBasis.sizes.NumericallySideTight
      (carrier.optimizationCorners observe).fullMinimumSizes
  quotientSideTight :
    (carrier.canonicalOptimumFamily
      observe).quotientBasis.sizes.NumericallySideTight
        (carrier.optimizationCorners observe).quotientMinimumSizes
  fullIncidenceValue :
    (carrier.canonicalOptimumFamily observe).fullBasis.sizes.tightValue?
        (carrier.optimizationCorners observe).fullMinimumSizes =
      some (carrier.optimizationCorners observe).fullDelta
  quotientIncidenceValue :
    (carrier.canonicalOptimumFamily observe).quotientBasis.sizes.tightValue?
        (carrier.optimizationCorners observe).quotientMinimumSizes =
      some (carrier.optimizationCorners observe).quotientDelta
  theta : ∀ coordinate,
    (carrier.optimumLegTransport .leftJoin).ambientCoordinate
        ((carrier.optimumLegTransport .meetLeft).ambientCoordinate coordinate) =
      (carrier.optimumLegTransport .rightJoin).ambientCoordinate
        ((carrier.optimumLegTransport .meetRight).ambientCoordinate coordinate)

private def coherentOptimumTupleOfNoFailure
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode)
    (noneFound : carrier.firstOptimumCoherenceFailure? observe mode = none) :
    TerminalFourCornerCoherentOptimumTuple carrier observe mode :=
  { carrierCompatible := carrier.fourCornerOptimaCarrierCompatible observe
    noFailure := noneFound
    fullSizes := (carrier.optimizationCorners observe).canonicalFullBasis_sizes
    quotientSizes :=
      (carrier.optimizationCorners observe).canonicalQuotientBasis_sizes
    fullSideTight :=
      (carrier.optimizationCorners observe).canonicalFullBasis_numericallySideTight
    quotientSideTight :=
      (carrier.optimizationCorners
        observe).canonicalQuotientBasis_numericallySideTight
    fullIncidenceValue :=
      (carrier.optimizationCorners observe).canonicalFullBasis_tightValue?
    quotientIncidenceValue :=
      (carrier.optimizationCorners observe).canonicalQuotientBasis_tightValue?
    theta := carrier.optimumTransportTheta }

/-- A total classification result carries either the checked coherent tuple
    or the exact first failing coordinate together with its defining query. -/
inductive TerminalFourCornerOptimumClassification
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) where
  | coherent
      (tuple : TerminalFourCornerCoherentOptimumTuple carrier observe mode)
  | failure
      (reason : TerminalFourCornerOptimumFailure
        (inputs + gates) gates profileWidth)
      (first : carrier.firstOptimumCoherenceFailure? observe mode = some reason)

/-- Execute the complete finite coherence classifier. -/
def TerminalFourCornerCarrier.classifyOptimumCoherence
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    TerminalFourCornerOptimumClassification carrier observe mode :=
  match found : carrier.firstOptimumCoherenceFailure? observe mode with
  | none => .coherent (coherentOptimumTupleOfNoFailure carrier observe mode found)
  | some reason => .failure reason found

/-- Absence of a failure is equivalent to existence of the complete checked
    coherent tuple. -/
theorem TerminalFourCornerCarrier.noFailure_iff_coherentOptimumTuple
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    carrier.firstOptimumCoherenceFailure? observe mode = none ↔
      Nonempty (TerminalFourCornerCoherentOptimumTuple carrier observe mode) := by
  constructor
  · intro noneFound
    exact ⟨coherentOptimumTupleOfNoFailure carrier observe mode noneFound⟩
  · rintro ⟨tuple⟩
    exact tuple.noFailure

/-- The executable classifier is exhaustive for every finite carrier,
    observer, projection, and selected mode. -/
theorem TerminalFourCornerCarrier.classifyOptimumCoherence_exhaustive
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    Nonempty (TerminalFourCornerCoherentOptimumTuple carrier observe mode) ∨
      ∃ failure,
        carrier.firstOptimumCoherenceFailure? observe mode = some failure ∧
          failure.Sound := by
  cases found : carrier.firstOptimumCoherenceFailure? observe mode with
  | none =>
      exact Or.inl
        ⟨coherentOptimumTupleOfNoFailure carrier observe mode found⟩
  | some failure =>
      exact Or.inr ⟨failure, rfl,
        carrier.firstOptimumCoherenceFailure?_sound observe mode failure found⟩

/-- Universal Section 11.1 coherence dichotomy: the four exact canonical
    side-tight optima either commute as a checked tuple in the chosen mode, or
    the deterministic finite procedure returns the first exact obstruction. -/
theorem TerminalFourCornerCarrier.fourCornerOptimumCoherenceDichotomy
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (carrier : TerminalFourCornerCarrier system)
    (observe : Implementation (inputs + gates) gates ->
      TerminalProfile profileWidth)
    (mode : TerminalOptimumCoherenceMode) :
    Nonempty (TerminalFourCornerCoherentOptimumTuple carrier observe mode) ∨
      ∃ failure,
        carrier.firstOptimumCoherenceFailure? observe mode = some failure ∧
          failure.Sound :=
  carrier.classifyOptimumCoherence_exhaustive observe mode

end DirectWire
end PNP
