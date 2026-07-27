/-
Copyright (c) 2026 PNP Labs.

The unsatisfiable branch of the locked-NAND `ZeroOutputConvention` from
Section 17 of the pinned legacy manuscript.  The candidate is the
answer-independent construction from `LockedNANDGlobalCandidates`; the
unsatisfiability proof is used only to derive its whole-carrier semantics.

This file does not prove the satisfiable final-lock separation law, construct
the complete conditional threshold package, or establish the global
locked-NAND threshold.
-/

import PNP.LockedNANDGlobalCandidates

namespace PNP
namespace DirectWire
namespace LockedNANDGlobalCandidates

open LockedNANDTrace

/-- If the source NAND circuit is unsatisfiable, the final coordinate of the
answer-independent full candidate is false on every carrier valuation,
including incoherent valuations. -/
theorem fullCandidate_final_eq_false_of_unsatisfiable
    {inputs : Nat} (circuit : Circuit inputs)
    (notSatisfiable : ¬ circuit.Satisfiable) :
    ∀ input,
      (fullCandidate circuit).semantics input
          (conditionalFinalOutput
            (lockedBaselineCount circuit.program)) =
        false := by
  intro input
  rw [fullCandidate_final_semantics_conjunction]
  generalize traceEqual :
      tracePredicate circuit.program (unflattenCarrier input) =
        traceValue
  cases traceValue with
  | false =>
      simp
  | true =>
      generalize outputEqual :
          input (traceSlot (inputs := inputs) circuit.outputGate) =
            outputValue
      cases outputValue with
      | false =>
          simp
      | true =>
          exact False.elim (notSatisfiable
            ((satisfiable_iff_trace_extension circuit).2
              ⟨unflattenCarrier input, traceEqual, outputEqual⟩))

private theorem projectedFullCandidate_equivalent_baseline
    {inputs : Nat} (circuit : Circuit inputs) :
    Equivalent
      (projectBaselineOutputs (fullCandidate circuit)).program
      (projectBaselineOutputs (fullCandidate circuit)).directWireWord
      (baselineCandidate circuit).program
      (baselineCandidate circuit).directWireWord := by
  intro input output
  change
    (projectBaselineOutputs (fullCandidate circuit)).semantics
        input output =
      (baselineCandidate circuit).semantics input output
  rw [projectBaselineOutputs_semantics]
  exact fullCandidate_initial_semantics circuit input output

private theorem projectedFullCandidate_conditions
    {inputs : Nat} (circuit : Circuit inputs) :
    BaselineOutputConditions
      (projectBaselineOutputs (fullCandidate circuit)) :=
  (baselineCandidate_outputConditions circuit).of_equivalent
    (projectedFullCandidate_equivalent_baseline circuit)

private theorem appendZeroFinalOutput_equivalent_fullCandidate_of_unsatisfiable
    {inputs : Nat} (circuit : Circuit inputs)
    (notSatisfiable : ¬ circuit.Satisfiable) :
    Equivalent
      (appendZeroFinalOutput (baselineCandidate circuit)).program
      (appendZeroFinalOutput
        (baselineCandidate circuit)).directWireWord
      (fullCandidate circuit).program
      (fullCandidate circuit).directWireWord := by
  intro input output
  change
    (appendZeroFinalOutput (baselineCandidate circuit)).semantics
        input output =
      (fullCandidate circuit).semantics input output
  cases finSum_decompose output with
  | inl initialCase =>
      rcases initialCase with ⟨initialOutput, outputEqual⟩
      subst output
      exact
        (appendZeroFinalOutput_initial_semantics
          (baselineCandidate circuit) input initialOutput).trans
            (fullCandidate_initial_semantics
              circuit input initialOutput).symm
  | inr finalCase =>
      rcases finalCase with ⟨finalIndex, outputEqual⟩
      rw [fin1_eq_fin1Zero finalIndex] at outputEqual
      subst output
      exact
        (appendZeroFinalOutput_final_semantics
          (baselineCandidate circuit) input).trans
            (fullCandidate_final_eq_false_of_unsatisfiable
              circuit notSatisfiable input).symm

/-- In the unsatisfiable branch, appending the identically-false final
coordinate costs no gates, while the retained square baseline still forces
the exhaustive reference minimum to be exactly its source-derived count. -/
theorem fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable
    {inputs : Nat} (circuit : Circuit inputs)
    (notSatisfiable : ¬ circuit.Satisfiable) :
    referenceMinimum
        (Implementation.mk
          (lockedBaselineCount circuit.program + 4)
          (fullCandidate circuit)) =
      lockedBaselineCount circuit.program := by
  apply Nat.le_antisymm
  · apply referenceMinimum_le_of_equivalent
      (Implementation.mk
        (lockedBaselineCount circuit.program + 4)
        (fullCandidate circuit))
      (appendZeroFinalOutput (baselineCandidate circuit))
    exact
      appendZeroFinalOutput_equivalent_fullCandidate_of_unsatisfiable
        circuit notSatisfiable
  · exact projectedOutputCount_le_referenceMinimum
      (fullCandidate circuit)
      (projectedFullCandidate_conditions circuit)

end LockedNANDGlobalCandidates
end DirectWire
end PNP
