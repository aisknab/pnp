/-
Copyright (c) 2026 PNP Labs.

Computed closure of constant propagation, NAND sharing and output-cone pruning.
Each selected pass is an actual whole-program construction and strictly saves
physical gates. The loop stops only when all three computed savings are zero on
the same final implementation. No normalizer, oracle or certificate is supplied.

This is quiescence for these three physical passes, not complete manuscript
normalization, a full-profile/support transport ledger, semantic minimality,
ZeroSlack or a polynomial-time PCCMin construction.
-/

import PNP.PCCMinConstantPropagation
import PNP.PCCMinConstructiveNANDSharing
import PNP.PCCMinOutputConePruning

namespace PNP
namespace DirectWire

/-- The fixed physical pass family, in deterministic priority order. -/
inductive PhysicalNormalizationPass where
  | constants
  | sharing
  | pruning
  deriving DecidableEq, Repr

def PhysicalNormalizationPass.priority : PhysicalNormalizationPass → Nat
  | .constants => 0
  | .sharing => 1
  | .pruning => 2

/-- Run an existing concrete pass, rather than an input optimization function. -/
def physicalNormalizationPassResult {inputs outputs : Nat}
    (pass : PhysicalNormalizationPass) (current : Implementation inputs outputs) :
    Implementation inputs outputs :=
  match pass with
  | .constants => constantPropagationImplementation current
  | .sharing => sharingImplementation current
  | .pruning => outputConeImplementation current

/-- Savings are the actual counts computed by the corresponding construction. -/
def physicalNormalizationPassSavings {inputs outputs : Nat}
    (pass : PhysicalNormalizationPass) (current : Implementation inputs outputs) : Nat :=
  match pass with
  | .constants => (compileNANDConstantPropagation current.candidate.program).eliminationCount
  | .sharing => (compileNANDSharing current.candidate.program).foldCount
  | .pruning => outputConeDeletedGateCount current

/-- Every member preserves the complete ordered output word for every input. -/
theorem physicalNormalizationPass_equivalent {inputs outputs : Nat}
    (pass : PhysicalNormalizationPass) (current : Implementation inputs outputs) :
    Equivalent (physicalNormalizationPassResult pass current).candidate.program
      (physicalNormalizationPassResult pass current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord := by
  cases pass with
  | constants => exact constantPropagationImplementation_equivalent current
  | sharing => exact sharingImplementation_equivalent current
  | pruning => exact outputConeImplementation_equivalent current

/-- Computed pass savings account for the exact physical gate difference. -/
theorem physicalNormalizationPass_exact_accounting {inputs outputs : Nat}
    (pass : PhysicalNormalizationPass) (current : Implementation inputs outputs) :
    (physicalNormalizationPassResult pass current).gateCount +
      physicalNormalizationPassSavings pass current = current.gateCount := by
  cases pass with
  | constants => exact compileNANDConstantPropagation_exact_accounting current.candidate.program
  | sharing => exact compileNANDSharing_exact_accounting current.candidate.program
  | pruning => exact outputConeImplementation_exact_accounting current

/-- All three constructions find zero saving on this same implementation.
This predicate says nothing about other physical or semantic routes. -/
def PhysicalNormalizationQuiescent {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Prop :=
  ∀ pass, physicalNormalizationPassSavings pass current = 0

/-- A selected actual pass with positive savings and no earlier available pass.
The step constructor below derives both proof fields from the input program. -/
structure PhysicalNormalizationGain {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  pass : PhysicalNormalizationPass
  positive : 0 < physicalNormalizationPassSavings pass current
  earlier_quiet : ∀ earlier, earlier.priority < pass.priority →
    physicalNormalizationPassSavings earlier current = 0

def PhysicalNormalizationGain.result {inputs outputs : Nat}
    {current : Implementation inputs outputs} (gain : PhysicalNormalizationGain current) :
    Implementation inputs outputs :=
  physicalNormalizationPassResult gain.pass current

def PhysicalNormalizationGain.savedGates {inputs outputs : Nat}
    {current : Implementation inputs outputs} (gain : PhysicalNormalizationGain current) : Nat :=
  physicalNormalizationPassSavings gain.pass current

def PhysicalNormalizationGain.strictGain {inputs outputs : Nat}
    {current : Implementation inputs outputs} (gain : PhysicalNormalizationGain current) :
    StrictEquivalentGain current gain.result where
  smaller := by
    have accounting := physicalNormalizationPass_exact_accounting gain.pass current
    have positive := gain.positive
    change (physicalNormalizationPassResult gain.pass current).gateCount < current.gateCount
    omega
  equivalent := physicalNormalizationPass_equivalent gain.pass current

/-- Every selected edge is the actual first available strict physical gain. -/
theorem PhysicalNormalizationGain.checked {inputs outputs : Nat}
    {current : Implementation inputs outputs} (gain : PhysicalNormalizationGain current) :
    StrictEquivalentGain current gain.result ∧
      gain.result.gateCount + gain.savedGates = current.gateCount ∧
      0 < gain.savedGates ∧
      ∀ earlier, earlier.priority < gain.pass.priority →
        physicalNormalizationPassSavings earlier current = 0 :=
  ⟨gain.strictGain, physicalNormalizationPass_exact_accounting gain.pass current,
    gain.positive, gain.earlier_quiet⟩

inductive PhysicalNormalizationStep {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  | gain (selected : PhysicalNormalizationGain current)
  | quiescent (quiet : PhysicalNormalizationQuiescent current)

/-- Compute the first positive pass. Each later branch establishes that the
earlier passes are quiet on the same current implementation. -/
def nextPhysicalNormalizationStep {inputs outputs : Nat}
    (current : Implementation inputs outputs) : PhysicalNormalizationStep current :=
  if constants : 0 < physicalNormalizationPassSavings .constants current then
    .gain
      { pass := .constants
        positive := constants
        earlier_quiet := by
          intro earlier precedes
          change earlier.priority < 0 at precedes
          omega }
  else if sharing : 0 < physicalNormalizationPassSavings .sharing current then
    .gain
      { pass := .sharing
        positive := sharing
        earlier_quiet := by
          intro earlier precedes
          cases earlier <;> simp only [PhysicalNormalizationPass.priority] at precedes
          · omega
          · omega
          · omega }
  else if pruning : 0 < physicalNormalizationPassSavings .pruning current then
    .gain
      { pass := .pruning
        positive := pruning
        earlier_quiet := by
          intro earlier precedes
          cases earlier <;> simp only [PhysicalNormalizationPass.priority] at precedes
          · omega
          · omega
          · omega }
  else
    .quiescent (by
      intro pass
      cases pass
      · omega
      · omega
      · omega)

/-- The computed selector never treats a failed individual pass as global
stopping; its terminal branch has zero savings for every member of the family. -/
theorem nextPhysicalNormalizationStep_checked {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    match nextPhysicalNormalizationStep current with
    | .gain selected =>
        StrictEquivalentGain current selected.result ∧
          selected.result.gateCount + selected.savedGates = current.gateCount ∧
          0 < selected.savedGates ∧
          ∀ earlier, earlier.priority < selected.pass.priority →
            physicalNormalizationPassSavings earlier current = 0
    | .quiescent _ => PhysicalNormalizationQuiescent current := by
  cases nextPhysicalNormalizationStep current with
  | gain selected => exact selected.checked
  | quiescent quiet => exact quiet

/-- A finite trace of actual priority-respecting strict passes, ending with
all three savings zero. This is not arbitrary-support Pull/Expand data. -/
inductive PhysicalNormalizationTrace {inputs outputs : Nat} :
    Implementation inputs outputs → Implementation inputs outputs → Type where
  | done (current : Implementation inputs outputs)
      (quiet : PhysicalNormalizationQuiescent current) :
      PhysicalNormalizationTrace current current
  | step {current final : Implementation inputs outputs}
      (gain : PhysicalNormalizationGain current)
      (tail : PhysicalNormalizationTrace gain.result final) :
      PhysicalNormalizationTrace current final

def PhysicalNormalizationTrace.gainIterations {inputs outputs : Nat}
    {current final : Implementation inputs outputs} :
    PhysicalNormalizationTrace current final → Nat
  | .done _ _ => 0
  | .step _ tail => tail.gainIterations + 1

def PhysicalNormalizationTrace.savedGates {inputs outputs : Nat}
    {current final : Implementation inputs outputs} :
    PhysicalNormalizationTrace current final → Nat
  | .done _ _ => 0
  | .step gain tail => gain.savedGates + tail.savedGates

/-- Trace semantics, common stopping condition and exact telescoping cost. -/
theorem PhysicalNormalizationTrace.checked {inputs outputs : Nat}
    {current final : Implementation inputs outputs}
    (trace : PhysicalNormalizationTrace current final) :
    Equivalent final.candidate.program final.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      PhysicalNormalizationQuiescent final ∧
      final.gateCount + trace.savedGates = current.gateCount ∧
      trace.gainIterations ≤ trace.savedGates := by
  induction trace with
  | done current quiet =>
      exact ⟨Equivalent.refl _ _, quiet, Nat.add_zero _, Nat.le_refl 0⟩
  | step gain tail ih =>
      obtain ⟨equivalent, quiet, accounting, iterations⟩ := ih
      have edgeAccounting := gain.checked.2.1
      have positive := gain.checked.2.2.1
      refine ⟨Equivalent.trans equivalent gain.strictGain.equivalent, quiet, ?_, ?_⟩
      · change _ + (gain.savedGates + tail.savedGates) = _
        omega
      · change tail.gainIterations + 1 ≤ gain.savedGates + tail.savedGates
        omega

/-- The concrete result carries its constructed execution trace. -/
structure PhysicalNormalizationExecution {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  result : Implementation inputs outputs
  trace : PhysicalNormalizationTrace current result

/-- Recheck the fixed family after every actual strict gain. Termination uses
only physical gate count; no semantic minimum is executed. -/
def runPhysicalNormalization {inputs outputs : Nat}
    (current : Implementation inputs outputs) : PhysicalNormalizationExecution current :=
  match nextPhysicalNormalizationStep current with
  | .gain gain =>
      let tail := runPhysicalNormalization gain.result
      { result := tail.result
        trace := .step gain tail.trace }
  | .quiescent quiet =>
      { result := current
        trace := .done current quiet }
termination_by current.gateCount
decreasing_by exact gain.strictGain.smaller

/-- Complete semantics, same-result three-pass quiescence and exact trace cost,
with no supplied normalizer or oracle premise. -/
theorem runPhysicalNormalization_checked {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    let execution := runPhysicalNormalization current
    Equivalent execution.result.candidate.program execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      PhysicalNormalizationQuiescent execution.result ∧
      execution.result.gateCount + execution.trace.savedGates = current.gateCount ∧
      execution.trace.gainIterations ≤ execution.trace.savedGates :=
  (runPhysicalNormalization current).trace.checked

/-- A quiescent input is returned unchanged, not merely with an equal gate count. -/
theorem runPhysicalNormalization_of_quiescent {inputs outputs : Nat}
    (current : Implementation inputs outputs) (quiet : PhysicalNormalizationQuiescent current) :
    (runPhysicalNormalization current).result = current := by
  have constants : ¬ 0 < physicalNormalizationPassSavings .constants current := by
    rw [quiet .constants]
    exact Nat.lt_irrefl 0
  have sharing : ¬ 0 < physicalNormalizationPassSavings .sharing current := by
    rw [quiet .sharing]
    exact Nat.lt_irrefl 0
  have pruning : ¬ 0 < physicalNormalizationPassSavings .pruning current := by
    rw [quiet .pruning]
    exact Nat.lt_irrefl 0
  rw [runPhysicalNormalization]
  simp only [nextPhysicalNormalizationStep, dif_neg constants, dif_neg sharing, dif_neg pruning]

/-- Running the complete concrete closure twice has the same result as once. -/
theorem runPhysicalNormalization_idempotent {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (runPhysicalNormalization (runPhysicalNormalization current).result).result =
      (runPhysicalNormalization current).result :=
  runPhysicalNormalization_of_quiescent _
    (runPhysicalNormalization_checked current).2.1

/-- Semantic reference minima appear only in specifications, never execution. -/
theorem runPhysicalNormalization_referenceMinimum {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    referenceMinimum (runPhysicalNormalization current).result = referenceMinimum current :=
  referenceMinimum_invariant _ _ (runPhysicalNormalization_checked current).1

/-- The complete trace retires exactly its actual physical saving from slack. -/
theorem runPhysicalNormalization_residualSlack {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    residualSlack current =
      residualSlack (runPhysicalNormalization current).result +
        (runPhysicalNormalization current).trace.savedGates := by
  have accounting := (runPhysicalNormalization_checked current).2.2.1
  have bounded := referenceMinimum_le_target (runPhysicalNormalization current).result
  have sameMinimum := runPhysicalNormalization_referenceMinimum current
  unfold residualSlack
  rw [sameMinimum] at bounded ⊢
  omega

/-- The number of actual gain iterations is bounded by the original slack.
This is not a runtime bound for the pass computations. -/
theorem runPhysicalNormalization_gainIterations_le_residualSlack {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (runPhysicalNormalization current).trace.gainIterations ≤ residualSlack current := by
  have iterations := (runPhysicalNormalization_checked current).2.2.2
  have slack := runPhysicalNormalization_residualSlack current
  omega

/-- Supply the actual three-pass closure to the existing normalizer interface.
Positive total saving is surfaced as a strict gain, never hidden as stopping. -/
def physicalClosureNormalizer : PCCMinTotalNormalizer where
  normalize := fun current =>
    let execution := runPhysicalNormalization current
    if positive : 0 < execution.trace.savedGates then
      .gain execution.result
        { smaller := by
            have accounting := (runPhysicalNormalization_checked current).2.2.1
            change 0 < (runPhysicalNormalization current).trace.savedGates at positive
            change (runPhysicalNormalization current).result.gateCount < current.gateCount
            omega
          equivalent := (runPhysicalNormalization_checked current).1 }
    else
      .normal
        { result := execution.result
          equivalent := (runPhysicalNormalization_checked current).1
          gateCount_le := by
            have accounting := (runPhysicalNormalization_checked current).2.2.1
            change (runPhysicalNormalization current).result.gateCount ≤ current.gateCount
            omega }

/-- Both public branches return the computed quiescent result. Gain means
positive actual savings; no-gain means zero savings, not semantic minimality. -/
theorem physicalClosureNormalizer_checked {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    match physicalClosureNormalizer.normalize current with
    | .gain next _ =>
        next = (runPhysicalNormalization current).result ∧
          PhysicalNormalizationQuiescent next ∧
          0 < (runPhysicalNormalization current).trace.savedGates
    | .normal normalized =>
        normalized.result = (runPhysicalNormalization current).result ∧
          PhysicalNormalizationQuiescent normalized.result ∧
          (runPhysicalNormalization current).trace.savedGates = 0 ∧
          normalized.result.gateCount = current.gateCount := by
  have checked := runPhysicalNormalization_checked current
  by_cases positive : 0 < (runPhysicalNormalization current).trace.savedGates
  · simp only [physicalClosureNormalizer, dif_pos positive]
    exact ⟨True.intro, checked.2.1, positive⟩
  · simp only [physicalClosureNormalizer, dif_neg positive]
    exact ⟨True.intro, checked.2.1, by omega, by
      have accounting := checked.2.2.1
      omega⟩

end DirectWire
end PNP
