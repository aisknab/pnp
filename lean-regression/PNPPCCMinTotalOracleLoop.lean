import PNP

namespace PNP
namespace DirectWire

/-- An exhaustive reference oracle used only to exercise the general loop
interface.  It is not a polynomial PCCOracle implementation. -/
def pccMinExhaustiveReferenceFixtureOracle : PCCMinTotalOracle where
  route := fun current =>
    if positive : 0 < residualSlack current then
      .gain (referenceMinimumImplementation current)
        (referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos
          positive)
    else
      .zeroSlack
        { minimum :=
            (residualSlack_eq_zero_iff_minimum current).mp
              (Nat.eq_zero_of_not_pos positive) }

/-- An exact-result oracle fixture exercises the other terminal constructor.
It also uses exhaustive reference minimization and carries no runtime claim. -/
def pccMinExactReferenceFixtureOracle : PCCMinTotalOracle where
  route := fun current =>
    .exact
      { result := referenceMinimumImplementation current
        equivalent := referenceMinimumImplementation_equivalent current
        minimum := referenceMinimumImplementation_isSemanticallyMinimum current }

example {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next) :
    PCCMinOracleOutcome current :=
  .gain next gain

example {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (exactResult : ExactMinimumResult current) :
    PCCMinOracleOutcome current :=
  .exact exactResult

example {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (zeroSlackResult : ZeroSlackResult current) :
    PCCMinOracleOutcome current :=
  .zeroSlack zeroSlackResult

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution :=
      runPCCMinTotalOracleLoop pccMinExhaustiveReferenceFixtureOracle current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current :=
  pccmin_total_oracle_loop_checked_complete
    pccMinExhaustiveReferenceFixtureOracle current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution :=
      runPCCMinTotalOracleLoop pccMinExactReferenceFixtureOracle current
    execution.result.gateCount = referenceMinimum current :=
  (runPCCMinTotalOracleLoop
    pccMinExactReferenceFixtureOracle current).result_gateCount_eq_referenceMinimum

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution :=
      runPCCMinTotalOracleLoop pccMinExactReferenceFixtureOracle current
    residualSlack execution.result = 0 :=
  (runPCCMinTotalOracleLoop
    pccMinExactReferenceFixtureOracle current).result_residualSlack_eq_zero

end DirectWire
end PNP
