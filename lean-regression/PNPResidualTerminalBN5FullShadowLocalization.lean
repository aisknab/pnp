import PNP.ResidualTerminalBN5FullShadowLocalization

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

abbrev BN5RegressionCoordinate := TerminalBN5ShadowCoordinate
  Bool Bool Bool Bool Bool Bool Bool Bool

def bn5RegressionKey : TerminalBN4ActivationKey Bool Bool Bool :=
  { atom := true
    semanticSignature := false
    transportType := false }

def bn5RegressionPayload0 :
    TerminalBN5ShadowPayload Bool Bool Bool Bool Bool :=
  { frontier := false
    chargeOwner := false
    obligation := false
    originKernel := false
    modeProjection := false }

def bn5RegressionPayloadFrontierMismatch :
    TerminalBN5ShadowPayload Bool Bool Bool Bool Bool :=
  { frontier := true
    chargeOwner := false
    obligation := false
    originKernel := false
    modeProjection := false }

def bn5RegressionCoordinate0 : BN5RegressionCoordinate :=
  bn5RegressionPayload0.toCoordinate bn5RegressionKey

def bn5RegressionCoordinateFrontierMismatch : BN5RegressionCoordinate :=
  bn5RegressionPayloadFrontierMismatch.toCoordinate bn5RegressionKey

/-- Two negative full units at one exact coordinate and one quotient shadow
    give the canonical one-versus-two Hall deficit. -/
def bn5RegressionFullUnits : List (TerminalBN5FullUnit BN5RegressionCoordinate) :=
  terminalBN5FullUnits bn5RegressionKey
    [bn5RegressionPayload0, bn5RegressionPayload0]

def bn5RegressionOneShadow :
    List (TerminalBN5QuotientShadow BN5RegressionCoordinate) :=
  terminalBN5QuotientShadows [bn5RegressionCoordinate0]

def bn5RegressionHallSummary : Nat × Nat × Nat :=
  match classifyTerminalBN5ShadowMatching bn5RegressionFullUnits
      bn5RegressionOneShadow with
  | .matched _matching => (0, 0, 0)
  | .hallDeficit deficit =>
      (1, deficit.neighborShadows.length, deficit.fullSubset.length)

example : bn5RegressionHallSummary = (1, 1, 2) := by decide

/-- Two exact-coordinate quotient candidates cover the two full units. -/
def bn5RegressionMatchedSummary : Nat :=
  match classifyTerminalBN5ShadowMatching bn5RegressionFullUnits
      (terminalBN5QuotientShadows
        [bn5RegressionCoordinate0, bn5RegressionCoordinate0]) with
  | .matched _matching => 1
  | .hallDeficit _deficit => 0

example : bn5RegressionMatchedSummary = 1 := by decide

/-- A shadow with only a frontier mismatch cannot enter the exact-coordinate
    neighborhood. -/
def bn5RegressionMismatchSummary : Nat × Nat :=
  match classifyTerminalBN5ShadowMatching
      (terminalBN5FullUnits bn5RegressionKey [bn5RegressionPayload0])
      (terminalBN5QuotientShadows
        [bn5RegressionCoordinateFrontierMismatch]) with
  | .matched _matching => (0, 0)
  | .hallDeficit deficit =>
      (deficit.neighborShadows.length, deficit.fullSubset.length)

example : bn5RegressionMismatchSummary = (0, 1) := by decide

def bn5RegressionNegativeCancellation :
    TerminalBN4KeyCancellation 0 2 :=
  .negative 2 (by decide) (by decide)

def bn5RegressionLocalizedSummary : Nat × Nat × Nat :=
  match classifyTerminalBN5FullShadowLocalization
      bn5RegressionNegativeCancellation bn5RegressionKey [true]
      [bn5RegressionPayload0, bn5RegressionPayload0]
      [bn5RegressionCoordinate0] with
  | .noNegativeResidual _exact => (0, 0, 0)
  | .invalidUnitRefinement _mass _exact _positive _mismatch => (1, 0, 0)
  | .cutSilent _mass _exact _positive _refines _inactive => (2, 0, 0)
  | .matched _mass _exact _positive _refines _active _matching => (3, 0, 0)
  | .localized _mass _exact _positive _refines _active deficit =>
      (4, deficit.neighborShadows.length, deficit.fullSubset.length)

example : bn5RegressionLocalizedSummary = (4, 1, 2) := by decide

/-- The same deficit on an inactive cut is classified as proved cut silence. -/
def bn5RegressionCutSilentSummary : Nat :=
  match classifyTerminalBN5FullShadowLocalization
      bn5RegressionNegativeCancellation bn5RegressionKey []
      [bn5RegressionPayload0, bn5RegressionPayload0]
      [bn5RegressionCoordinate0] with
  | .cutSilent _mass _exact _positive _refines _inactive => 1
  | _ => 0

example : bn5RegressionCutSilentSummary = 1 := by decide

/-- A one-unit payload cannot purport to refine negative mass two. -/
def bn5RegressionInvalidRefinementSummary : Nat :=
  match classifyTerminalBN5FullShadowLocalization
      bn5RegressionNegativeCancellation bn5RegressionKey [true]
      [bn5RegressionPayload0] [bn5RegressionCoordinate0] with
  | .invalidUnitRefinement _mass _exact _positive _mismatch => 1
  | _ => 0

example : bn5RegressionInvalidRefinementSummary = 1 := by decide

def bn5RegressionBalancedCancellation :
    TerminalBN4KeyCancellation 2 2 :=
  .balanced rfl

def bn5RegressionNoNegativeSummary : Nat :=
  match classifyTerminalBN5FullShadowLocalization
      bn5RegressionBalancedCancellation bn5RegressionKey [true]
      ([] : List (TerminalBN5ShadowPayload Bool Bool Bool Bool Bool))
      ([] : List BN5RegressionCoordinate) with
  | .noNegativeResidual _exact => 1
  | _ => 0

example : bn5RegressionNoNegativeSummary = 1 := by decide

#print axioms terminalBN5ShadowCoordinate_eq_iff
#print axioms terminalBN5FullUnits_key_eq
#print axioms TerminalBN5HallDeficit.neighbor_card_lt_full_card
#print axioms classifyTerminalBN5ShadowMatching_exhaustive
#print axioms classifyTerminalBN5FullShadowLocalization_active
#print axioms TerminalBN5HallDeficit.unmatchedShadowNotSilent
#print axioms classifyTerminalBN5FullShadowLocalization_exhaustive

end DirectWire
end PNP
