import PNP

namespace PNP
namespace DirectWire

/-- Identity normalization fixture used only to exercise the two-stage control
flow. -/
def pccMinIdentityFixtureNormalizer : PCCMinTotalNormalizer where
  normalize := fun current =>
    .normal
      { result := current
        equivalent := Equivalent.refl
          current.candidate.program current.candidate.directWireWord
        gateCount_le := Nat.le_refl current.gateCount }

/-- Exhaustive reference normalizer fixture.  It is not a polynomial
NormalizeOrGain implementation. -/
def pccMinReferenceGainFixtureNormalizer : PCCMinTotalNormalizer where
  normalize := fun current =>
    if positive : 0 < residualSlack current then
      .gain (referenceMinimumImplementation current)
        (referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos
          positive)
    else
      .normal
        { result := current
          equivalent := Equivalent.refl
            current.candidate.program current.candidate.directWireWord
          gateCount_le := Nat.le_refl current.gateCount }

/-- Exhaustive reference-minimum normalization fixture.  It exercises
ZeroSlack transport after a nontrivial semantic normalization and carries no
runtime claim. -/
def pccMinReferenceMinimumFixtureNormalizer : PCCMinTotalNormalizer where
  normalize := fun current =>
    .normal
      { result := referenceMinimumImplementation current
        equivalent := referenceMinimumImplementation_equivalent current
        gateCount_le := by
          rw [referenceMinimumImplementation_gateCount_eq_referenceMinimum]
          exact referenceMinimum_le_target current }

/-- Exhaustive reference oracle fixture for gain and ZeroSlack branches. -/
def pccMinNormalizeReferenceFixtureOracle : PCCMinTotalOracle where
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

/-- Exact reference oracle fixture for the normalized exact branch. -/
def pccMinNormalizeExactFixtureOracle : PCCMinTotalOracle where
  route := fun current =>
    .exact
      { result := referenceMinimumImplementation current
        equivalent := referenceMinimumImplementation_equivalent current
        minimum := referenceMinimumImplementation_isSemanticallyMinimum current }

example {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next) :
    PCCMinNormalizeOutcome current :=
  .gain next gain

example {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    PCCMinNormalizeOutcome current :=
  .normal
    { result := current
      equivalent := Equivalent.refl
        current.candidate.program current.candidate.directWireWord
      gateCount_le := Nat.le_refl current.gateCount }

example {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    (normalized : PCCMinNormalizedResult current)
    (gain : StrictEquivalentGain normalized.result next) :
    StrictEquivalentGain current next :=
  normalized.liftStrictEquivalentGain gain

example {inputs outputs : Nat}
    {current next : Implementation inputs outputs}
    (normalized : PCCMinNormalizedResult current)
    (gain : StrictEquivalentGain normalized.result next) :
    residualSlack next < residualSlack current :=
  normalized.liftStrictEquivalentGain_strictResidualDescent gain

example {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (normalized : PCCMinNormalizedResult current)
    (exact : ExactMinimumResult normalized.result) :
    ExactMinimumResult current :=
  normalized.transportExactMinimum exact

example {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (normalized : PCCMinNormalizedResult current)
    (zeroSlack : ZeroSlackResult normalized.result) :
    ExactMinimumResult current :=
  normalized.exactMinimumOfZeroSlack zeroSlack

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeOracleLoop
      pccMinReferenceGainFixtureNormalizer
      pccMinNormalizeReferenceFixtureOracle current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current :=
  pccmin_normalize_oracle_loop_checked_complete
    pccMinReferenceGainFixtureNormalizer
    pccMinNormalizeReferenceFixtureOracle current

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeOracleLoop
      pccMinIdentityFixtureNormalizer
      pccMinNormalizeReferenceFixtureOracle current
    execution.result.gateCount = referenceMinimum current :=
  (runPCCMinNormalizeOracleLoop
    pccMinIdentityFixtureNormalizer
    pccMinNormalizeReferenceFixtureOracle current).result_gateCount_eq_referenceMinimum

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeOracleLoop
      pccMinIdentityFixtureNormalizer
      pccMinNormalizeExactFixtureOracle current
    residualSlack execution.result = 0 :=
  (runPCCMinNormalizeOracleLoop
    pccMinIdentityFixtureNormalizer
    pccMinNormalizeExactFixtureOracle current).result_residualSlack_eq_zero

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeOracleLoop
      pccMinReferenceMinimumFixtureNormalizer
      pccMinNormalizeReferenceFixtureOracle current
    IsSemanticallyMinimum execution.result :=
  (runPCCMinNormalizeOracleLoop
    pccMinReferenceMinimumFixtureNormalizer
    pccMinNormalizeReferenceFixtureOracle current).minimum

end DirectWire
end PNP
