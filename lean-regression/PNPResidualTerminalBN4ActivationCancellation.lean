import PNP.ResidualTerminalBN4ActivationCancellation

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PNP
namespace DirectWire

/-- The same concrete two-anchor nucleus used by the BN3 regression, repeated
    here so the BN4 test has no dependency on another regression file. -/
def bn4CancellationGate0 : Fin 3 := ⟨0, by decide⟩
def bn4CancellationGate1 : Fin 3 := ⟨1, by decide⟩
def bn4CancellationGate2 : Fin 3 := ⟨2, by decide⟩
def bn4CancellationEarlierGate0 : Fin 2 := ⟨0, by decide⟩
def bn4CancellationEarlierGate1 : Fin 2 := ⟨1, by decide⟩

def bn4CancellationProgram : Program 0 3 :=
  .snoc
    (.snoc
      (.snoc .empty
        { left := .constant true, right := .constant true })
      { left := .constant true, right := .constant true })
    { left := .gate bn4CancellationEarlierGate0,
      right := .gate bn4CancellationEarlierGate1 }

def bn4CancellationWord : DirectWireWord 0 3 1 :=
  ⟨fun _output => .gate bn4CancellationGate2⟩

def bn4CancellationCandidate : Candidate 0 3 1 :=
  Candidate.ofDirectWireWord bn4CancellationProgram bn4CancellationWord

def bn4CancellationProfileSystem : TerminalProfileSystem 0 1 1 :=
  { role := fun _coordinate => .kernel
    observe := fun _implementation _coordinate => false }

def bn4CancellationObserver
    (implementation : Implementation 3 3) : TerminalProfile 1 :=
  fun _coordinate => decide (2 <= implementation.gateCount)

def bn4CancellationSaturationSystem : TerminalSaturationSystem 0 3 1 1 :=
  { profileSystem := bn4CancellationProfileSystem
    requires := fun _kind _dependent _required => false }

def bn4CancellationSeed : List (TerminalPrimitiveRecord 0 3 1 1) :=
  [.gate bn4CancellationGate0, .gate bn4CancellationGate1]

def bn4CancellationSupport : TerminalProperPositiveSupport
    bn4CancellationCandidate bn4CancellationSaturationSystem :=
  { seed := bn4CancellationSeed
    governed := by decide
    proper := by
      unfold TerminalSupportProper
      decide
    positive := by
      unfold TerminalSupportPositive
      decide }

def bn4CancellationForgetAll : TerminalProfileProjection 1 :=
  { keep := fun _coordinate => false }

def bn4CancellationProblem : TerminalBCELAnchorProblem
    bn4CancellationCandidate bn4CancellationSaturationSystem :=
  { support := bn4CancellationSupport
    projection := bn4CancellationForgetAll
    observe := bn4CancellationObserver }

theorem bn4CancellationWholePositive :
    0 < bn4CancellationProblem.familyDefect
      bn4CancellationProblem.anchorRecords := by
  decide

abbrev BN4RegressionAtom := TerminalPrimitiveRecord 0 3 1 1
abbrev BN4RegressionCell :=
  TerminalBN4ActivationCell BN4RegressionAtom Bool Bool

def bn4CancellationKey0 :
    TerminalBN4ActivationKey BN4RegressionAtom Bool Bool :=
  { atom := .gate bn4CancellationGate0
    semanticSignature := false
    transportType := false }

/-- Same activation atom but a different semantic signature: it must not
    cancel against `bn4CancellationKey0`. -/
def bn4CancellationSemanticKey :
    TerminalBN4ActivationKey BN4RegressionAtom Bool Bool :=
  { atom := .gate bn4CancellationGate0
    semanticSignature := true
    transportType := false }

/-- Same activation atom and semantic signature but a different transport
    type: it must also remain a separate cancellation class. -/
def bn4CancellationTransportKey :
    TerminalBN4ActivationKey BN4RegressionAtom Bool Bool :=
  { atom := .gate bn4CancellationGate0
    semanticSignature := false
    transportType := true }

def bn4CancellationKey1 :
    TerminalBN4ActivationKey BN4RegressionAtom Bool Bool :=
  { atom := .gate bn4CancellationGate1
    semanticSignature := false
    transportType := false }

def bn4CancellationCells : List BN4RegressionCell :=
  [ { key := bn4CancellationKey0, sign := .positive, mass := 7 },
    { key := bn4CancellationKey0, sign := .negative, mass := 2 },
    { key := bn4CancellationKey0, sign := .negative, mass := 1 },
    { key := bn4CancellationSemanticKey, sign := .negative, mass := 5 },
    { key := bn4CancellationTransportKey, sign := .positive, mass := 3 },
    { key := bn4CancellationKey1, sign := .positive, mass := 2 },
    { key := bn4CancellationKey1, sign := .negative, mass := 2 } ]

example : terminalBN4InputSignedMass bn4CancellationCells
    bn4CancellationKey0 = 4 := by decide

def bn4CancellationResidualSummary
    (key : TerminalBN4ActivationKey BN4RegressionAtom Bool Bool) :
    Int × Nat :=
  match (terminalBN4CancelAtKey bn4CancellationCells key).residualCells key with
  | [] => (0, 0)
  | [cell] => (cell.signedContribution, cell.mass)
  | _ => (999, 999)

example : bn4CancellationResidualSummary bn4CancellationKey0 = (4, 4) := by
  decide

example : bn4CancellationResidualSummary bn4CancellationSemanticKey =
    (-5, 5) := by
  decide

example : bn4CancellationResidualSummary bn4CancellationTransportKey =
    (3, 3) := by
  decide

example : bn4CancellationResidualSummary bn4CancellationKey1 = (0, 0) := by
  decide

example : (terminalBN4CanonicalKeys bn4CancellationCells).length = 4 := by
  decide

/-- The concrete BN3-ready fixture accepts its canonical atoms and reaches the
    finite BN4 cancellation package. -/
def bn4CancellationReadyOutcome : Nat × Nat :=
  match classifyTerminalBN4ActivationCancellation bn4CancellationProblem
      bn4CancellationWholePositive bn4CancellationCells with
  | .insufficient _failure => (0, 0)
  | .algebraFailure _nucleus _first _failure => (1, 0)
  | .cutDefectFailure _nucleus _first _failure => (2, 0)
  | .cutRouteFailure _nucleus _first _failure => (3, 0)
  | .invalidAtomLedger _result _envelope _failure => (4, 0)
  | .ready _result _envelope _cancellation =>
      (5, (terminalBN4CanonicalKeys bn4CancellationCells).length)

example : bn4CancellationReadyOutcome = (5, 4) := by decide

/-- A cell naming the ambient third gate is rejected because that gate is not
    a canonical request atom in the successful two-anchor nucleus. -/
def bn4CancellationInvalidCells : List BN4RegressionCell :=
  [{ key :=
      { atom := .gate bn4CancellationGate2
        semanticSignature := false
        transportType := false },
     sign := .positive,
     mass := 1 }]

def bn4CancellationInvalidOutcome : Nat :=
  match classifyTerminalBN4ActivationCancellation bn4CancellationProblem
      bn4CancellationWholePositive bn4CancellationInvalidCells with
  | .insufficient _failure => 0
  | .algebraFailure _nucleus _first _failure => 1
  | .cutDefectFailure _nucleus _first _failure => 2
  | .cutRouteFailure _nucleus _first _failure => 3
  | .invalidAtomLedger _result _envelope _failure => 4
  | .ready _result _envelope _cancellation => 5

example : bn4CancellationInvalidOutcome = 4 := by decide

#print axioms terminalBN4ActivationCode_eq_iff_activation
#print axioms terminalBN4ActivationKey_eq_iff
#print axioms terminalBN4CancelAtKey_signedContribution_exact
#print axioms TerminalComputedBCELAnchorNucleus.computedBN4ActivationCancellation
#print axioms classifyTerminalBN4ActivationCancellation_exhaustive

end DirectWire
end PNP
