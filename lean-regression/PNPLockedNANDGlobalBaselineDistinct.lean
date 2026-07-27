import PNP

namespace PNP.DirectWire.LockedNANDGlobalBaselineDistinctRegression

open LockedNANDTrace
open LockedNANDGlobalCandidates

def negationProgram : Program 1 1 :=
  .snoc .empty
    { left := .input fin1Zero
      right := .input fin1Zero }

abbrev negationCircuit : Circuit 1 :=
  { gateCount := 1
    program := negationProgram
    outputGate := fin1Zero }

def constantTrueProgram : Program 0 1 :=
  .snoc .empty
    { left := .constant false
      right := .constant false }

abbrev constantTrueCircuit : Circuit 0 :=
  { gateCount := 1
    program := constantTrueProgram
    outputGate := fin1Zero }

example :
    ∀ output,
      OutputNonconstant (baselineCandidate negationCircuit) output :=
  baselineCandidate_outputNonconstant negationCircuit

example :
    ∀ output,
      OutputNotPositiveProjection
        (baselineCandidate negationCircuit) output :=
  baselineCandidate_outputNotPositiveProjection negationCircuit

example :
    OutputPairwiseDistinct (baselineCandidate negationCircuit) :=
  baselineCandidate_outputPairwiseDistinct negationCircuit

example :
    BaselineOutputConditions (baselineCandidate negationCircuit) :=
  baselineCandidate_outputConditions negationCircuit

example :
    referenceMinimum
        (Implementation.mk 42 (baselineCandidate negationCircuit)) =
      42 := by
  exact baselineCandidate_referenceMinimum negationCircuit

example :
    referenceMinimum
        (Implementation.mk 28 (baselineCandidate constantTrueCircuit)) =
      28 := by
  exact baselineCandidate_referenceMinimum constantTrueCircuit

end PNP.DirectWire.LockedNANDGlobalBaselineDistinctRegression
