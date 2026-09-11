/-
Copyright (c) 2026 PNP Labs.

Computed physical gain realization for production saturated supports.
The observer remains supplied, and minimization and support search remain
exhaustive reference computations. No full-profile route or runtime claim.
-/

import PNP.ResidualTerminalSaturatedSupportContext

namespace PNP
namespace DirectWire

/-- Compute the whole physical replacement using the existing reference-minimum
    witness and the actual saturated-support context. No replacement or frame
    certificate is supplied. -/
def terminalCandidateSaturatePhysicalMinimumReplacement
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Implementation inputs outputs :=
  let support := extractSaturatedTerminalSupport candidate
    (terminalCandidateSaturationSystem candidate model) seed
  let context := terminalCandidateSaturatePhysicalContext candidate model seed
  (context.plug support.extractedCandidate.referenceMinimumReplacement).toImplementation

/-- The constructed minimum-support replacement preserves the complete original
    ordered Boolean output word, at arbitrary dimensions and for every seed. -/
theorem terminalCandidateSaturatePhysicalMinimumReplacement_equivalent
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    let replacement := terminalCandidateSaturatePhysicalMinimumReplacement
      candidate model seed
    Equivalent replacement.candidate.program replacement.candidate.directWireWord
      candidate.program candidate.directWireWord := by
  let support := extractSaturatedTerminalSupport candidate
    (terminalCandidateSaturationSystem candidate model) seed
  exact terminalCandidateSaturatePhysicalContext_replace_equivalent
    candidate model seed support.extractedCandidate.referenceMinimumReplacement
    support.extractedCandidate.referenceMinimumReplacement_equivalent

private theorem physicalGain_size_balance (remaining selected minimum whole : Nat)
    (within : minimum ≤ selected)
    (partition : remaining + selected = whole + minimum) :
    remaining + (selected - minimum) = whole := by
  have balanced : (remaining + (selected - minimum)) + minimum = whole + minimum := by
    calc
      (remaining + (selected - minimum)) + minimum =
          remaining + ((selected - minimum) + minimum) := Nat.add_assoc _ _ _
      _ = remaining + selected := by rw [Nat.sub_add_cancel within]
      _ = whole + minimum := partition
  exact Nat.add_right_cancel balanced

/-- The replacement removes exactly the extracted physical gain. Properness
    and positivity are not needed for this accounting equation. -/
theorem terminalCandidateSaturatePhysicalMinimumReplacement_size_gain
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    (terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed).gateCount +
      terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) seed = gates := by
  let system := terminalCandidateSaturationSystem candidate model
  let support := extractSaturatedTerminalSupport candidate system seed
  let replacement := terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed
  have counted := terminalCandidateSaturatePhysicalContext_size candidate model seed
    support.extractedCandidate.referenceMinimumReplacement
  have charges := terminalCandidateSaturatePhysicalCharges_size candidate model seed
  change support.gateCount =
    (terminalSaturatePhysicalCharges system seed).length at charges
  rw [Program.size_eq_gateCount] at counted
  change replacement.gateCount + (terminalSaturatePhysicalCharges system seed).length =
    gates + referenceMinimum support.extractedCandidate.toImplementation at counted
  rw [← charges] at counted
  change replacement.gateCount +
    (support.gateCount - referenceMinimum support.extractedCandidate.toImplementation) = gates
  exact physicalGain_size_balance _ _ _ _
    (referenceMinimum_le_target support.extractedCandidate.toImplementation) counted

private theorem physicalGain_slack_balance (remaining whole minimum gain : Nat)
    (within : minimum ≤ remaining) (size : remaining + gain = whole) :
    (remaining - minimum) + gain = whole - minimum := by
  have wholeWithin : minimum ≤ whole :=
    Nat.le_trans within (Nat.le.intro size)
  have balanced : ((remaining - minimum) + gain) + minimum =
      (whole - minimum) + minimum := by
    calc
      ((remaining - minimum) + gain) + minimum =
          ((remaining - minimum) + minimum) + gain := Nat.add_right_comm _ _ _
      _ = remaining + gain := by rw [Nat.sub_add_cancel within]
      _ = whole := size
      _ = (whole - minimum) + minimum := (Nat.sub_add_cancel wholeWithin).symm
  exact Nat.add_right_cancel balanced

/-- Exact global physical slack reduction by the computed local gain.
    Reference minima remain exhaustive; this is not a full-profile law. -/
theorem terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (seed : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    residualSlack (terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed) +
      terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) seed =
      residualSlack candidate.toImplementation := by
  let replacement := terminalCandidateSaturatePhysicalMinimumReplacement candidate model seed
  have minima := referenceMinimum_invariant replacement candidate.toImplementation
    (terminalCandidateSaturatePhysicalMinimumReplacement_equivalent candidate model seed)
  have within := referenceMinimum_le_target replacement
  rw [minima] at within
  have size := terminalCandidateSaturatePhysicalMinimumReplacement_size_gain candidate model seed
  change residualSlack replacement + _ = residualSlack candidate.toImplementation
  unfold residualSlack
  rw [minima]
  exact physicalGain_slack_balance _ _ _ _ within size

/-- Run the existing production proper-positive search and construct the actual
    whole-circuit reference replacement. Failure is not a global minimum claim. -/
def findTerminalCandidatePhysicalGain
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    Option (Implementation inputs outputs) :=
  (findTerminalCandidateProperPositiveSupport candidate model).map fun found =>
    terminalCandidateSaturatePhysicalMinimumReplacement candidate model found.seed

private theorem physicalGain_strict_of_positive (remaining gain whole : Nat)
    (balanced : remaining + gain = whole) (positive : 0 < gain) :
    remaining < whole := by
  have grows : remaining + 0 < remaining + gain :=
    Nat.add_lt_add_left positive remaining
  simpa only [Nat.add_zero, balanced] using grows

/-- A successful computed search realizes its selected proper positive support
    as an equivalent whole circuit with exact and strictly positive physical
    size and slack decrease. No gain or correctness certificate is an input. -/
theorem findTerminalCandidatePhysicalGain_sound
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate)
    (result : Implementation inputs outputs)
    (foundAt : findTerminalCandidatePhysicalGain candidate model = some result) :
    ∃ found : TerminalCandidateProperPositiveSupport candidate model,
      findTerminalCandidateProperPositiveSupport candidate model = some found ∧
      found.seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth ∧
      TerminalSupportProper candidate
        (terminalCandidateSaturationSystem candidate model) found.seed ∧
      0 < terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) found.seed ∧
      result = terminalCandidateSaturatePhysicalMinimumReplacement
        candidate model found.seed ∧
      Equivalent result.candidate.program result.candidate.directWireWord
        candidate.program candidate.directWireWord ∧
      result.gateCount + terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) found.seed = gates ∧
      residualSlack result + terminalSupportLocalGain candidate
        (terminalCandidateSaturationSystem candidate model) found.seed =
          residualSlack candidate.toImplementation ∧
      result.gateCount < gates ∧
      residualSlack result < residualSlack candidate.toImplementation := by
  cases supportAt : findTerminalCandidateProperPositiveSupport candidate model with
  | none =>
      simp only [findTerminalCandidatePhysicalGain, supportAt, Option.map_none] at foundAt
      cases foundAt
  | some found =>
      simp only [findTerminalCandidatePhysicalGain, supportAt, Option.map_some] at foundAt
      have same := Option.some.inj foundAt
      subst result
      have size := terminalCandidateSaturatePhysicalMinimumReplacement_size_gain
        candidate model found.seed
      have slack := terminalCandidateSaturatePhysicalMinimumReplacement_slack_gain
        candidate model found.seed
      exact ⟨found, rfl, found.governed, found.proper, found.positive, rfl,
        terminalCandidateSaturatePhysicalMinimumReplacement_equivalent
          candidate model found.seed,
        size, slack,
        physicalGain_strict_of_positive _ _ _ size found.positive,
        physicalGain_strict_of_positive _ _ _ slack found.positive⟩

/-- Failure excludes every canonical proper positive seed for the actual
    candidate-derived system. It does not exclude a whole-circuit gain or prove
    ZeroSlack, full-profile route completeness or polynomial runtime. -/
theorem findTerminalCandidatePhysicalGain_eq_none_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel
      (profileWidth := profileWidth) candidate) :
    findTerminalCandidatePhysicalGain candidate model = none ↔
      ∀ seed, seed ∈ allTerminalSupportSeeds inputs gates outputs profileWidth →
        ¬(TerminalSupportProper candidate
            (terminalCandidateSaturationSystem candidate model) seed ∧
          TerminalSupportPositive candidate
            (terminalCandidateSaturationSystem candidate model) seed) := by
  have erase : findTerminalCandidatePhysicalGain candidate model = none ↔
      findTerminalCandidateProperPositiveSupport candidate model = none := by
    unfold findTerminalCandidatePhysicalGain
    cases findTerminalCandidateProperPositiveSupport candidate model with
    | none => simp only [Option.map_none]
    | some found =>
        constructor <;> intro impossible <;> cases impossible
  exact erase.trans (findTerminalProperPositiveSupport_eq_none_iff candidate
    (terminalCandidateSaturationSystem candidate model))

end DirectWire
end PNP
