/-
Copyright (c) 2026 PNP Labs.

A conditional threshold boundary for actual typed direct-wire candidates.  The
premises deliberately include the baseline and full candidates plus their
semantic preservation facts.  Establishing those premises uniformly for a
global locked builder is outside this file; consequently none of the results
below is the global builder or global threshold theorem.
-/

import PNP.DirectWireBaseline
import PNP.NANDSlack

namespace PNP
namespace DirectWire

/-! ## Baseline and final output coordinates -/

def baselineOutputEmbedding {baseline : Nat} (output : Fin baseline) :
    Fin (baseline + 1) :=
  Fin.castAdd 1 output

def conditionalFinalOutput (baseline : Nat) : Fin (baseline + 1) :=
  Fin.natAdd baseline fin1Zero

theorem fin1_eq_fin1Zero (index : Fin 1) : index = fin1Zero := by
  apply Fin.ext
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ index.isLt)

theorem conditionalFinalOutput_eq_last (baseline : Nat) :
    conditionalFinalOutput baseline = Fin.last baseline := by
  apply Fin.ext
  rfl

/-! ## First-baseline-output projection -/

/-- Retain the full program and project its first `baseline` output wires. -/
def projectBaselineOutputs
    {inputs gates baseline : Nat}
    (full : Candidate inputs gates (baseline + 1)) :
    Candidate inputs gates baseline :=
  Candidate.ofDirectWireWord full.program
    ⟨fun output => full.directWireWord.source
      (baselineOutputEmbedding output)⟩

theorem projectBaselineOutputs_program
    {inputs gates baseline : Nat}
    (full : Candidate inputs gates (baseline + 1)) :
    (projectBaselineOutputs full).program = full.program := rfl

theorem projectBaselineOutputs_size
    {inputs gates baseline : Nat}
    (full : Candidate inputs gates (baseline + 1)) :
    (projectBaselineOutputs full).program.size = full.program.size := rfl

theorem projectBaselineOutputs_source
    {inputs gates baseline : Nat}
    (full : Candidate inputs gates (baseline + 1))
    (output : Fin baseline) :
    (projectBaselineOutputs full).directWireWord.source output =
      full.directWireWord.source (baselineOutputEmbedding output) :=
  Candidate.ofDirectWireWord_pointwise full.program
    ⟨fun output => full.directWireWord.source
      (baselineOutputEmbedding output)⟩ output

theorem projectBaselineOutputs_semantics
    {inputs gates baseline : Nat}
    (full : Candidate inputs gates (baseline + 1))
    (input : Valuation inputs) (output : Fin baseline) :
    (projectBaselineOutputs full).semantics input output =
      full.semantics input (baselineOutputEmbedding output) := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [projectBaselineOutputs_source]
  rfl

/-! ## Free zero-output append -/

/-- Append one constant-zero output wire without changing the program. -/
def appendZeroFinalOutput
    {inputs gates baseline : Nat}
    (initial : Candidate inputs gates baseline) :
    Candidate inputs gates (baseline + 1) :=
  Candidate.ofDirectWireWord initial.program
    ⟨splitFin initial.directWireWord.source
      (fun _ => .constant false)⟩

theorem appendZeroFinalOutput_program
    {inputs gates baseline : Nat}
    (initial : Candidate inputs gates baseline) :
    (appendZeroFinalOutput initial).program = initial.program := rfl

theorem appendZeroFinalOutput_size
    {inputs gates baseline : Nat}
    (initial : Candidate inputs gates baseline) :
    (appendZeroFinalOutput initial).program.size = initial.program.size := rfl

theorem appendZeroFinalOutput_initial_source
    {inputs gates baseline : Nat}
    (initial : Candidate inputs gates baseline) (output : Fin baseline) :
    (appendZeroFinalOutput initial).directWireWord.source
        (baselineOutputEmbedding output) =
      initial.directWireWord.source output := by
  unfold appendZeroFinalOutput
  rw [Candidate.ofDirectWireWord_pointwise]
  change splitFin initial.directWireWord.source
      (fun _ => Source.constant false) (Fin.castAdd 1 output) =
    initial.directWireWord.source output
  exact splitFin_left _ _ output

theorem appendZeroFinalOutput_final_source
    {inputs gates baseline : Nat}
    (initial : Candidate inputs gates baseline) :
    (appendZeroFinalOutput initial).directWireWord.source
        (conditionalFinalOutput baseline) = .constant false := by
  unfold appendZeroFinalOutput
  rw [Candidate.ofDirectWireWord_pointwise]
  change splitFin initial.directWireWord.source
      (fun _ => Source.constant false) (Fin.natAdd baseline fin1Zero) =
    Source.constant false
  exact splitFin_right _ _ fin1Zero

theorem appendZeroFinalOutput_initial_semantics
    {inputs gates baseline : Nat}
    (initial : Candidate inputs gates baseline)
    (input : Valuation inputs) (output : Fin baseline) :
    (appendZeroFinalOutput initial).semantics input
        (baselineOutputEmbedding output) =
      initial.semantics input output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [appendZeroFinalOutput_initial_source]
  rfl

theorem appendZeroFinalOutput_final_semantics
    {inputs gates baseline : Nat}
    (initial : Candidate inputs gates baseline)
    (input : Valuation inputs) :
    (appendZeroFinalOutput initial).semantics input
        (conditionalFinalOutput baseline) = false := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [appendZeroFinalOutput_final_source]
  rfl

/-! ## Explicit satisfiable-final semantic conditions -/

/-- Conditions contributed by the final output in the satisfiable branch.
    They say exactly that the final coordinate is nonconstant, is not a
    positive input projection, and differs from every baseline coordinate. -/
structure ConditionalFinalOutputSatConditions
    {inputs gates baseline : Nat}
    (full : Candidate inputs gates (baseline + 1)) : Prop where
  nonconstant : OutputNonconstant full (conditionalFinalOutput baseline)
  notPositiveProjection :
    OutputNotPositiveProjection full (conditionalFinalOutput baseline)
  distinctFromBaseline : ∀ output : Fin baseline, ∃ valuation,
    full.semantics valuation (baselineOutputEmbedding output) ≠
      full.semantics valuation (conditionalFinalOutput baseline)

/-! ## Conditional boundary premises -/

/-- Proof-bearing local premises for the conditional boundary.

The structure stores actual typed candidates.  The baseline has exactly
`baseline` gates and outputs; the full candidate has exactly four additional
gates and one additional output.  Satisfiability controls only the supplied
final-output facts, not construction of either candidate. -/
structure ConditionalThresholdBoundaryPremises
    (satisfiable : Prop) (inputs baseline : Nat) where
  baselineCandidate : Candidate inputs baseline baseline
  fullCandidate : Candidate inputs (baseline + 4) (baseline + 1)
  baselineConditions : BaselineOutputConditions baselineCandidate
  initialOutputsPreserved : ∀ input output,
    fullCandidate.semantics input (baselineOutputEmbedding output) =
      baselineCandidate.semantics input output
  unsatisfiableFinalZero : ¬ satisfiable → ∀ input,
    fullCandidate.semantics input (conditionalFinalOutput baseline) = false
  satisfiableFinalConditions : satisfiable →
    ConditionalFinalOutputSatConditions fullCandidate

def ConditionalThresholdBoundaryPremises.fullImplementation
    {satisfiable : Prop} {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline) :
    Implementation inputs (baseline + 1) :=
  ⟨baseline + 4, premises.fullCandidate⟩

/-! ## Baseline-condition transport -/

theorem ConditionalThresholdBoundaryPremises.projectedEquivalentBaseline
    {satisfiable : Prop} {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline) :
    Equivalent (projectBaselineOutputs premises.fullCandidate).program
        (projectBaselineOutputs premises.fullCandidate).directWireWord
      premises.baselineCandidate.program
        premises.baselineCandidate.directWireWord := by
  intro input output
  change (projectBaselineOutputs premises.fullCandidate).semantics input output =
    premises.baselineCandidate.semantics input output
  rw [projectBaselineOutputs_semantics]
  exact premises.initialOutputsPreserved input output

theorem ConditionalThresholdBoundaryPremises.projectedBaselineConditions
    {satisfiable : Prop} {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline) :
    BaselineOutputConditions
      (projectBaselineOutputs premises.fullCandidate) :=
  premises.baselineConditions.of_equivalent
    premises.projectedEquivalentBaseline

/-- Add the explicit final-output conditions to conditions on the first
    `baseline` outputs. -/
theorem baselineConditions_with_final
    {inputs gates baseline : Nat}
    (full : Candidate inputs gates (baseline + 1))
    (initialConditions : BaselineOutputConditions (projectBaselineOutputs full))
    (finalConditions : ConditionalFinalOutputSatConditions full) :
    BaselineOutputConditions full := by
  constructor
  · intro output
    cases finSum_decompose output with
    | inl initialCase =>
        rcases initialCase with ⟨initialOutput, outputEqual⟩
        subst output
        obtain ⟨leftInput, rightInput, different⟩ :=
          initialConditions.nonconstant initialOutput
        refine ⟨leftInput, rightInput, ?_⟩
        rw [projectBaselineOutputs_semantics,
          projectBaselineOutputs_semantics] at different
        exact different
    | inr finalCase =>
        rcases finalCase with ⟨finalIndex, outputEqual⟩
        rw [fin1_eq_fin1Zero finalIndex] at outputEqual
        subst output
        exact finalConditions.nonconstant
  · intro output input
    cases finSum_decompose output with
    | inl initialCase =>
        rcases initialCase with ⟨initialOutput, outputEqual⟩
        subst output
        obtain ⟨valuation, different⟩ :=
          initialConditions.notPositiveProjection initialOutput input
        refine ⟨valuation, ?_⟩
        rw [projectBaselineOutputs_semantics] at different
        exact different
    | inr finalCase =>
        rcases finalCase with ⟨finalIndex, outputEqual⟩
        rw [fin1_eq_fin1Zero finalIndex] at outputEqual
        subst output
        exact finalConditions.notPositiveProjection input
  · intro leftOutput rightOutput outputDifferent
    cases finSum_decompose leftOutput with
    | inl leftInitialCase =>
        rcases leftInitialCase with ⟨leftInitial, leftEqual⟩
        subst leftOutput
        cases finSum_decompose rightOutput with
        | inl rightInitialCase =>
            rcases rightInitialCase with ⟨rightInitial, rightEqual⟩
            subst rightOutput
            have initialDifferent : leftInitial ≠ rightInitial := by
              intro equal
              apply outputDifferent
              exact congrArg baselineOutputEmbedding equal
            obtain ⟨valuation, different⟩ :=
              initialConditions.pairwiseDistinct initialDifferent
            refine ⟨valuation, ?_⟩
            rw [projectBaselineOutputs_semantics,
              projectBaselineOutputs_semantics] at different
            exact different
        | inr rightFinalCase =>
            rcases rightFinalCase with ⟨rightFinal, rightEqual⟩
            rw [fin1_eq_fin1Zero rightFinal] at rightEqual
            subst rightOutput
            exact finalConditions.distinctFromBaseline leftInitial
    | inr leftFinalCase =>
        rcases leftFinalCase with ⟨leftFinal, leftEqual⟩
        rw [fin1_eq_fin1Zero leftFinal] at leftEqual
        subst leftOutput
        cases finSum_decompose rightOutput with
        | inl rightInitialCase =>
            rcases rightInitialCase with ⟨rightInitial, rightEqual⟩
            subst rightOutput
            obtain ⟨valuation, different⟩ :=
              finalConditions.distinctFromBaseline rightInitial
            refine ⟨valuation, ?_⟩
            intro equal
            exact different equal.symm
        | inr rightFinalCase =>
            rcases rightFinalCase with ⟨rightFinal, rightEqual⟩
            rw [fin1_eq_fin1Zero rightFinal] at rightEqual
            subst rightOutput
            exact False.elim (outputDifferent rfl)

theorem ConditionalThresholdBoundaryPremises.fullConditions_of_satisfiable
    {satisfiable : Prop} {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline)
    (isSatisfiable : satisfiable) :
    BaselineOutputConditions premises.fullCandidate :=
  baselineConditions_with_final premises.fullCandidate
    premises.projectedBaselineConditions
    (premises.satisfiableFinalConditions isSatisfiable)

/-! ## Reference-minimum lower bounds -/

/-- Any candidate satisfying all output conditions has reference minimum at
    least its output count. -/
theorem outputCount_le_referenceMinimum
    {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (conditions : BaselineOutputConditions candidate) :
    outputs ≤ referenceMinimum ⟨gates, candidate⟩ := by
  let target : Implementation inputs outputs := ⟨gates, candidate⟩
  have witnessEquivalent : Equivalent
      (referenceMinimumWitness target).program
      (referenceMinimumWitness target).directWireWord
      candidate.program candidate.directWireWord :=
    equivalentBool_sound (referenceMinimumWitness_equivalent target)
  have witnessConditions :
      BaselineOutputConditions (referenceMinimumWitness target) :=
    conditions.of_equivalent witnessEquivalent
  exact outputCount_le_gateCount (referenceMinimumWitness target)
    witnessConditions

/-- Conditions on the projected first outputs force the full reference
    minimum to retain at least `baseline` gates. -/
theorem projectedOutputCount_le_referenceMinimum
    {inputs gates baseline : Nat}
    (full : Candidate inputs gates (baseline + 1))
    (conditions : BaselineOutputConditions (projectBaselineOutputs full)) :
    baseline ≤ referenceMinimum ⟨gates, full⟩ := by
  let target : Implementation inputs (baseline + 1) := ⟨gates, full⟩
  let witness := referenceMinimumWitness target
  let projectedWitness := projectBaselineOutputs witness
  have witnessEquivalent : Equivalent witness.program witness.directWireWord
      full.program full.directWireWord :=
    equivalentBool_sound (referenceMinimumWitness_equivalent target)
  have projectedEquivalent : Equivalent projectedWitness.program
      projectedWitness.directWireWord
      (projectBaselineOutputs full).program
      (projectBaselineOutputs full).directWireWord := by
    intro input output
    change (projectBaselineOutputs witness).semantics input output =
      (projectBaselineOutputs full).semantics input output
    rw [projectBaselineOutputs_semantics,
      projectBaselineOutputs_semantics]
    exact witnessEquivalent input (baselineOutputEmbedding output)
  have witnessConditions : BaselineOutputConditions projectedWitness :=
    conditions.of_equivalent projectedEquivalent
  exact outputCount_le_gateCount projectedWitness witnessConditions

theorem ConditionalThresholdBoundaryPremises.fullMinimum_ge_baseline
    {satisfiable : Prop} {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline) :
    baseline ≤ referenceMinimum premises.fullImplementation :=
  projectedOutputCount_le_referenceMinimum premises.fullCandidate
    premises.projectedBaselineConditions

/-! ## Constructive slack arithmetic -/

theorem natAdd_sub_le_right_of_left_le
    {left minimum extra : Nat} (leftWithin : left ≤ minimum) :
    (left + extra) - minimum ≤ extra := by
  induction left generalizing minimum with
  | zero =>
      rw [Nat.zero_add]
      exact Nat.sub_le extra minimum
  | succ left ih =>
      cases minimum with
      | zero => exact False.elim (Nat.not_succ_le_zero left leftWithin)
      | succ minimum =>
          rw [Nat.succ_add, Nat.succ_sub_succ_eq_sub]
          exact ih (Nat.le_of_succ_le_succ leftWithin)

/-- The four displayed final gates give only an unconditional slack upper
    bound, not an exact slack or satisfiability theorem by themselves. -/
theorem ConditionalThresholdBoundaryPremises.fullResidualSlack_le_four
    {satisfiable : Prop} {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline) :
    residualSlack premises.fullImplementation ≤ 4 := by
  unfold residualSlack ConditionalThresholdBoundaryPremises.fullImplementation
  exact natAdd_sub_le_right_of_left_le premises.fullMinimum_ge_baseline

/-! ## Unsatisfiable and satisfiable branches -/

theorem ConditionalThresholdBoundaryPremises.appendZeroEquivalentFull_of_unsatisfiable
    {satisfiable : Prop} {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline)
    (notSatisfiable : ¬ satisfiable) :
    Equivalent
      (appendZeroFinalOutput premises.baselineCandidate).program
      (appendZeroFinalOutput premises.baselineCandidate).directWireWord
      premises.fullCandidate.program premises.fullCandidate.directWireWord := by
  intro input output
  change (appendZeroFinalOutput premises.baselineCandidate).semantics input output =
    premises.fullCandidate.semantics input output
  cases finSum_decompose output with
  | inl initialCase =>
      rcases initialCase with ⟨initialOutput, outputEqual⟩
      subst output
      exact (appendZeroFinalOutput_initial_semantics
        premises.baselineCandidate input initialOutput).trans
          (premises.initialOutputsPreserved input initialOutput).symm
  | inr finalCase =>
      rcases finalCase with ⟨finalIndex, outputEqual⟩
      rw [fin1_eq_fin1Zero finalIndex] at outputEqual
      subst output
      exact (appendZeroFinalOutput_final_semantics
        premises.baselineCandidate input).trans
          (premises.unsatisfiableFinalZero notSatisfiable input).symm

theorem ConditionalThresholdBoundaryPremises.fullMinimum_eq_baseline_of_unsatisfiable
    {satisfiable : Prop} {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline)
    (notSatisfiable : ¬ satisfiable) :
    referenceMinimum premises.fullImplementation = baseline := by
  apply Nat.le_antisymm
  · apply referenceMinimum_le_of_equivalent premises.fullImplementation
      (appendZeroFinalOutput premises.baselineCandidate)
    exact premises.appendZeroEquivalentFull_of_unsatisfiable notSatisfiable
  · exact premises.fullMinimum_ge_baseline

theorem ConditionalThresholdBoundaryPremises.fullMinimum_bounds_of_satisfiable
    {satisfiable : Prop} {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline)
    (isSatisfiable : satisfiable) :
    baseline + 1 ≤ referenceMinimum premises.fullImplementation ∧
      referenceMinimum premises.fullImplementation ≤ baseline + 4 := by
  constructor
  · exact outputCount_le_referenceMinimum premises.fullCandidate
      (premises.fullConditions_of_satisfiable isSatisfiable)
  · exact referenceMinimum_le_target premises.fullImplementation

/-! ## Conditional threshold characterization -/

/-- Conditional boundary theorem.  Given decidable satisfiability and the
    explicit premises above, satisfiability is exactly crossing from baseline
    `baseline` to minimum at least `baseline + 1`.  This theorem does not
    construct the premises and is therefore not the global threshold theorem. -/
theorem ConditionalThresholdBoundaryPremises.satisfiable_iff_minimum_ge_succ
    {satisfiable : Prop} [Decidable satisfiable]
    {inputs baseline : Nat}
    (premises : ConditionalThresholdBoundaryPremises satisfiable inputs baseline) :
    satisfiable ↔ baseline + 1 ≤ referenceMinimum premises.fullImplementation := by
  constructor
  · intro isSatisfiable
    exact (premises.fullMinimum_bounds_of_satisfiable isSatisfiable).1
  · intro crossed
    if isSatisfiable : satisfiable then
      exact isSatisfiable
    else
      have minimumEqual :=
        premises.fullMinimum_eq_baseline_of_unsatisfiable isSatisfiable
      rw [minimumEqual] at crossed
      exact False.elim (Nat.not_succ_le_self baseline crossed)

end DirectWire
end PNP
