/-
Copyright (c) 2026 PNP Labs.

General proof-bearing control flow for the report's PCCMin loop.

This module does not construct the oracle.  Instead, it makes the remaining
algorithmic boundary exact: every nonterminal response contains a checked
strict equivalent gain, and every terminal response contains either a checked
exact minimum or a checked ZeroSlack result.  The recursive loop is therefore
well-founded and exact for every implementation, while oracle construction and
all encoded-size polynomial bounds remain separate obligations.
-/

import PNP.ResidualGainStopping

namespace PNP
namespace DirectWire

/-- One proof-bearing result from a total PCCMin oracle at `current`.

There is deliberately no unresolved constructor.  Search failure can become a
terminal outcome only by carrying an exact-minimum or ZeroSlack proof. -/
inductive PCCMinOracleOutcome {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  | gain (next : Implementation inputs outputs)
      (gain : StrictEquivalentGain current next)
  | exact (result : ExactMinimumResult current)
  | zeroSlack (result : ZeroSlackResult current)

/-- A total typed oracle for every finite direct-wire interface and current
implementation.  This interface is an explicit proof boundary, not a
construction or runtime claim. -/
structure PCCMinTotalOracle where
  route : {inputs outputs : Nat} ->
    (current : Implementation inputs outputs) ->
      PCCMinOracleOutcome current

/-- Complete proof-bearing output of the recursive PCCMin control flow. -/
structure PCCMinLoopExecution {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  result : Implementation inputs outputs
  equivalent : Equivalent
    result.candidate.program result.candidate.directWireWord
    current.candidate.program current.candidate.directWireWord
  minimum : IsSemanticallyMinimum result
  gainIterations : Nat
  gainIterations_le_residualSlack :
    gainIterations <= residualSlack current

/-- Follow a proof-bearing total oracle until it returns exactness or
ZeroSlack.  Strict residual-slack descent is the termination measure. -/
def runPCCMinTotalOracleLoop (oracle : PCCMinTotalOracle)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    PCCMinLoopExecution current :=
  match oracle.route current with
  | .gain next gain =>
      let tail := runPCCMinTotalOracleLoop oracle next
      { result := tail.result
        equivalent := Equivalent.trans tail.equivalent gain.equivalent
        minimum := tail.minimum
        gainIterations := tail.gainIterations + 1
        gainIterations_le_residualSlack := by
          exact Nat.succ_le_of_lt
            (Nat.lt_of_le_of_lt tail.gainIterations_le_residualSlack
              gain.strictResidualDescent) }
  | .exact exactResult =>
      { result := exactResult.result
        equivalent := exactResult.equivalent
        minimum := exactResult.minimum
        gainIterations := 0
        gainIterations_le_residualSlack := Nat.zero_le _ }
  | .zeroSlack zeroSlackResult =>
      { result := current
        equivalent := Equivalent.refl
          current.candidate.program current.candidate.directWireWord
        minimum := zeroSlackResult.minimum
        gainIterations := 0
        gainIterations_le_residualSlack := Nat.zero_le _ }
termination_by residualSlack current
decreasing_by exact gain.strictResidualDescent

/-- Forget the iteration ledger and retain the exact-minimum result. -/
def PCCMinLoopExecution.toExactMinimumResult {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (execution : PCCMinLoopExecution current) : ExactMinimumResult current :=
  { result := execution.result
    equivalent := execution.equivalent
    minimum := execution.minimum }

/-- The loop output has the exact exhaustive reference-minimum gate count. -/
theorem PCCMinLoopExecution.result_gateCount_eq_referenceMinimum
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (execution : PCCMinLoopExecution current) :
    execution.result.gateCount = referenceMinimum current :=
  execution.toExactMinimumResult.gateCount_eq_referenceMinimum

/-- The loop output has zero residual slack. -/
theorem PCCMinLoopExecution.result_residualSlack_eq_zero
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (execution : PCCMinLoopExecution current) :
    residualSlack execution.result = 0 :=
  execution.toExactMinimumResult.result_zeroSlack

/-- Public checked endpoint for the general PCCMin control-flow kernel.

The iteration count covers only strict gain responses.  It is not a bound on
the cost of constructing or executing an oracle response. -/
theorem pccmin_total_oracle_loop_checked_complete
    (oracle : PCCMinTotalOracle)
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPCCMinTotalOracleLoop oracle current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current := by
  let execution := runPCCMinTotalOracleLoop oracle current
  exact ⟨execution.equivalent, execution.minimum,
    execution.result_gateCount_eq_referenceMinimum,
    execution.result_residualSlack_eq_zero,
    execution.gainIterations_le_residualSlack⟩

end DirectWire
end PNP
