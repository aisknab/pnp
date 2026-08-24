/-
Copyright (c) 2026 PNP Labs.

Proof-bearing composition of the two control-flow stages in the manuscript's
PCCMin loop: NormalizeOrGain followed by the rank-ordered PCCOracle.

This module does not construct either component.  It establishes the exact
typed boundary needed by the recursive loop: normalization preserves complete
semantics and cannot increase gate count, so a subsequent oracle gain is still
a strict gain from the pre-normalized implementation, while exact and
ZeroSlack oracle endpoints transport back through normalization.
-/

import PNP.PCCMinTotalOracleLoop

namespace PNP
namespace DirectWire

/-- A proof-bearing normal form for `current`.  Normalization may preserve or
reduce gate count, but it must preserve the complete multi-output semantics. -/
structure PCCMinNormalizedResult {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  result : Implementation inputs outputs
  equivalent : Equivalent
    result.candidate.program result.candidate.directWireWord
    current.candidate.program current.candidate.directWireWord
  gateCount_le : result.gateCount <= current.gateCount

/-- The two legitimate outcomes of the manuscript's NormalizeOrGain stage.
There is deliberately no unresolved or unchecked-success constructor. -/
inductive PCCMinNormalizeOutcome {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  | gain (next : Implementation inputs outputs)
      (gain : StrictEquivalentGain current next)
  | normal (normalized : PCCMinNormalizedResult current)

/-- A total proof-bearing normalizer for every finite direct-wire interface and
current implementation.  This is an explicit construction boundary. -/
structure PCCMinTotalNormalizer where
  normalize : {inputs outputs : Nat} ->
    (current : Implementation inputs outputs) ->
      PCCMinNormalizeOutcome current

/-- A gain found after normalization is a genuine gain from the implementation
that entered the two-stage iteration. -/
def PCCMinNormalizedResult.liftStrictEquivalentGain
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (normalized : PCCMinNormalizedResult current)
    {next : Implementation inputs outputs}
    (gain : StrictEquivalentGain normalized.result next) :
    StrictEquivalentGain current next :=
  { smaller := Nat.lt_of_lt_of_le gain.smaller normalized.gateCount_le
    equivalent := Equivalent.trans gain.equivalent normalized.equivalent }

/-- The lifted oracle gain strictly decreases the original residual slack. -/
theorem PCCMinNormalizedResult.liftStrictEquivalentGain_strictResidualDescent
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (normalized : PCCMinNormalizedResult current)
    {next : Implementation inputs outputs}
    (gain : StrictEquivalentGain normalized.result next) :
    residualSlack next < residualSlack current :=
  (normalized.liftStrictEquivalentGain gain).strictResidualDescent

/-- Transport an exact oracle endpoint through semantic normalization. -/
def PCCMinNormalizedResult.transportExactMinimum
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (normalized : PCCMinNormalizedResult current)
    (exact : ExactMinimumResult normalized.result) :
    ExactMinimumResult current :=
  { result := exact.result
    equivalent := Equivalent.trans exact.equivalent normalized.equivalent
    minimum := exact.minimum }

/-- A ZeroSlack endpoint for the normalized implementation is an exact result
for the implementation that entered normalization. -/
def PCCMinNormalizedResult.exactMinimumOfZeroSlack
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (normalized : PCCMinNormalizedResult current)
    (zeroSlack : ZeroSlackResult normalized.result) :
    ExactMinimumResult current :=
  { result := normalized.result
    equivalent := normalized.equivalent
    minimum := zeroSlack.minimum }

/-- Compose the manuscript's two proof-bearing stages into the total-oracle
interface consumed by the M189 well-founded loop. -/
def composePCCMinNormalizerOracle
    (normalizer : PCCMinTotalNormalizer)
    (oracle : PCCMinTotalOracle) : PCCMinTotalOracle where
  route := fun current =>
    match normalizer.normalize current with
    | .gain next gain => .gain next gain
    | .normal normalized =>
        match oracle.route normalized.result with
        | .gain next gain =>
            .gain next (normalized.liftStrictEquivalentGain gain)
        | .exact exact =>
            .exact (normalized.transportExactMinimum exact)
        | .zeroSlack zeroSlack =>
            .exact (normalized.exactMinimumOfZeroSlack zeroSlack)

/-- Run the complete proof-bearing NormalizeOrGain/PCCOracle control flow. -/
def runPCCMinNormalizeOracleLoop
    (normalizer : PCCMinTotalNormalizer)
    (oracle : PCCMinTotalOracle)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    PCCMinLoopExecution current :=
  runPCCMinTotalOracleLoop
    (composePCCMinNormalizerOracle normalizer oracle) current

/-- Public checked endpoint for the manuscript-faithful two-stage PCCMin
control-flow kernel.

The iteration ledger counts only proof-bearing strict gains.  It does not bound
the cost of constructing or executing either supplied stage. -/
theorem pccmin_normalize_oracle_loop_checked_complete
    (normalizer : PCCMinTotalNormalizer)
    (oracle : PCCMinTotalOracle)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeOracleLoop normalizer oracle current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current := by
  exact pccmin_total_oracle_loop_checked_complete
    (composePCCMinNormalizerOracle normalizer oracle) current

end DirectWire
end PNP
