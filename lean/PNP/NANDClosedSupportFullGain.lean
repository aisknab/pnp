import PNP.NANDClosedSupportFullGainPrefix
import PNP.ResidualRoutes

/-!
Physically reconnect a computed full-profile minimum of a computed closed
support. All input bindings, the complementary circuit, and profile sources
are derived. No replacement, correctness certificate, or frame is an input.

Legacy dependency: the positive full-mode branch in RW-SaturatePositive and
BCELReady needs a real whole-carrier descent that preserves required values.
This construction handles arbitrary computational wire fields and proves its
exact gate and full-slack balance. It does not derive a positive seed, prove
proper-local VerifyDW eligibility, cover the manuscript's noncomputational
profile roles, or close global routing, SaturatePositive, BCELReady, or
ZeroSlack. Exhaustive reference minimization is not a polynomial algorithm.
-/

namespace PNP.DirectWire.ClosedSupportFullGain

variable {inputs outputs fields : Nat}

def complementRecords (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :=
  terminalPhysicalComplementRecords (ClosedSupportObservation.records target keep seed)

def complement (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :=
  extractTerminalSupport target.implementation.candidate (complementRecords target keep seed)

private theorem complement_boundary_interface
    {gates profileWidth : Nat} (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates)
    (member : TerminalSupportWire.gate producer ∈
      (extractTerminalSupport candidate (terminalPhysicalComplementRecords records)).boundary) :
    producer ∈ (extractTerminalSupport candidate records).interface := by
  let outside := terminalPhysicalComplementRecords records
  change TerminalSupportWire.gate producer ∈
    terminalBoundaryPorts candidate.program outside at member
  obtain ⟨external, consumer, enumerated, selected, uses⟩ :=
    (terminalBoundaryWire_eq_true_iff candidate.program outside (.gate producer)).mp
      ((mem_terminalBoundaryPorts_iff candidate.program outside (.gate producer)).mp member)
  have outsideFalse : terminalGateSelected outside producer = false :=
    (terminalWireExternal_eq_true_iff outside (.gate producer)).mp external
  have producerSelected : terminalGateSelected records producer = true := by
    have flipped := terminalPhysicalComplementRecords_selected records producer
    change terminalGateSelected outside producer = _ at flipped
    rw [outsideFalse] at flipped
    cases original : terminalGateSelected records producer with
    | false => rw [original] at flipped; exact False.elim (Bool.noConfusion flipped)
    | true => rfl
  have consumerOutside : terminalGateSelected records consumer = false := by
    change terminalGateSelected (terminalPhysicalComplementRecords records) consumer = true at selected
    rw [terminalPhysicalComplementRecords_selected] at selected
    cases original : terminalGateSelected records consumer with
    | false => rfl
    | true => rw [original] at selected; exact False.elim (Bool.noConfusion selected)
  apply (mem_terminalInterfacePorts_iff candidate records producer).mpr
  apply (terminalInterfaceGate_eq_true_iff candidate records producer).mpr
  exact ⟨producerSelected, Or.inl
    ((terminalGateHasExternalConsumer_eq_true_iff candidate.program records producer).mpr
      ⟨consumer, enumerated, consumerOutside, uses⟩)⟩

def boundarySource (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    TerminalSupportWire inputs target.implementation.gateCount →
      Source inputs (0 + (offered target keep seed).gateCount)
  | .input input => .input input
  | .gate producer => prefixOutput target keep seed producer

theorem boundarySource_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
    (wire : TerminalSupportWire inputs target.implementation.gateCount)
    (member : wire ∈ (complement target keep seed).boundary)
    (valuation : Valuation inputs) :
    (boundarySource target keep seed wire).eval valuation
        ((prefixProgram target keep seed).eval valuation) =
      wire.candidateValue target.implementation.candidate valuation := by
  cases wire with
  | input input => rfl
  | gate producer =>
      exact prefixOutput_value target keep seed producer
        (complement_boundary_interface target.implementation.candidate
          (ClosedSupportObservation.records target keep seed) producer member) valuation

def boundaryBinding (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    Fin (complement target keep seed).boundary.length →
      Source inputs (0 + (offered target keep seed).gateCount) :=
  fun index => boundarySource target keep seed ((complement target keep seed).boundary.get index)

def program (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    Program inputs ((0 + (offered target keep seed).gateCount) +
      (complement target keep seed).gateCount) :=
  (prefixProgram target keep seed).appendSubstituted (boundaryBinding target keep seed)
    (complement target keep seed).extractedCandidate.program

theorem complement_gate_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (gate : Fin target.implementation.gateCount)
    (selected : terminalGateSelected (complementRecords target keep seed) gate = true)
    (valuation : Valuation inputs) :
    (program target keep seed).eval valuation
        (Fin.natAdd (0 + (offered target keep seed).gateCount)
          (terminalExtractionGateIndex target.implementation.candidate
            (complementRecords target keep seed) gate selected)) =
      target.implementation.candidate.program.eval valuation gate := by
  have boundaryEqual :
      (fun index => (boundaryBinding target keep seed index).eval valuation
        ((prefixProgram target keep seed).eval valuation)) =
      terminalInducedBoundaryValuation target.implementation.candidate
        (complementRecords target keep seed) valuation := by
    funext index
    exact boundarySource_value target keep seed
      ((complement target keep seed).boundary.get index) (List.get_mem _ index) valuation
  unfold program
  rw [Program.eval_appendSubstituted_suffix, boundaryEqual]
  exact extractTerminalSupport_gate_induced target.implementation.candidate
    (complementRecords target keep seed) valuation gate selected

theorem retained_source_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields))
    (source : Source inputs (0 + (offered target keep seed).gateCount))
    (valuation : Valuation inputs) :
    (source.weakenGates (complement target keep seed).gateCount).eval valuation
        ((program target keep seed).eval valuation) =
      source.eval valuation ((prefixProgram target keep seed).eval valuation) := by
  rw [Source.eval_weakenGates]
  exact source.eval_congr (fun _ => rfl)
    (fun gate => Program.eval_appendSubstituted_prefix _ _ _ valuation gate)

private theorem complement_selected_of_not (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (gate : Fin target.implementation.gateCount)
    (absent : terminalGateSelected (ClosedSupportObservation.records target keep seed) gate ≠ true) :
    terminalGateSelected (complementRecords target keep seed) gate = true := by
  unfold complementRecords
  rw [terminalPhysicalComplementRecords_selected]
  cases equal : terminalGateSelected (ClosedSupportObservation.records target keep seed) gate with
  | false => rfl
  | true => exact False.elim (absent equal)

def outputSource (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    Source inputs target.implementation.gateCount →
      Source inputs ((0 + (offered target keep seed).gateCount) +
        (complement target keep seed).gateCount)
  | .input input => .input input
  | .constant value => .constant value
  | .gate gate =>
      if selected : terminalGateSelected (ClosedSupportObservation.records target keep seed) gate = true
      then (prefixOutput target keep seed gate).weakenGates (complement target keep seed).gateCount
      else .gate (Fin.natAdd (0 + (offered target keep seed).gateCount)
        (terminalExtractionGateIndex target.implementation.candidate
          (complementRecords target keep seed) gate
          (complement_selected_of_not target keep seed gate selected)))

theorem outputSource_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (source : Source inputs target.implementation.gateCount)
    (visible : ∀ gate, source = .gate gate →
      terminalGateSelected (ClosedSupportObservation.records target keep seed) gate = true →
      gate ∈ (extractTerminalSupport target.implementation.candidate
        (ClosedSupportObservation.records target keep seed)).interface)
    (valuation : Valuation inputs) :
    (outputSource target keep seed source).eval valuation ((program target keep seed).eval valuation) =
      source.eval valuation (target.implementation.candidate.program.eval valuation) := by
  cases source with
  | input input => rfl
  | constant value => rfl
  | gate gate =>
      by_cases selected :
        terminalGateSelected (ClosedSupportObservation.records target keep seed) gate = true
      · simp only [outputSource, dif_pos selected]
        exact (retained_source_value target keep seed (prefixOutput target keep seed gate)
          valuation).trans (prefixOutput_value target keep seed gate (visible gate rfl selected)
            valuation)
      · simp only [outputSource, dif_neg selected]
        exact complement_gate_value target keep seed gate
          (complement_selected_of_not target keep seed gate selected) valuation

def fieldSource (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields) :
    Source inputs ((0 + (offered target keep seed).gateCount) +
      (complement target keep seed).gateCount) :=
  if ClosedSupportObservation.retained target keep seed (target.source field) = true
  then (prefixField target keep seed field).weakenGates (complement target keep seed).gateCount
  else outputSource target keep seed (target.source field)

theorem fieldSource_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (field : Fin fields) (valuation : Valuation inputs) :
    (fieldSource target keep seed field).eval valuation ((program target keep seed).eval valuation) =
      target.fieldValue valuation field := by
  unfold fieldSource
  split
  · rename_i present
    exact (retained_source_value target keep seed (prefixField target keep seed field)
      valuation).trans (prefixField_value target keep seed field present valuation)
  · rename_i absent
    apply outputSource_value target keep seed (target.source field) _ valuation
    intro gate sourceAt selected
    apply False.elim
    apply absent
    rw [sourceAt]
    exact selected

def result (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) : WireCarrier inputs outputs fields :=
  { implementation :=
      (Candidate.ofDirectWireWord (program target keep seed)
        ⟨fun output => outputSource target keep seed
          (target.implementation.candidate.directWireWord.source output)⟩).toImplementation
    source := fieldSource target keep seed }

theorem result_output (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (valuation : Valuation inputs) (output : Fin outputs) :
    (result target keep seed).implementation.candidate.semantics valuation output =
      target.implementation.candidate.semantics valuation output := by
  change (Candidate.ofDirectWireWord (program target keep seed)
    ⟨fun out => outputSource target keep seed
      (target.implementation.candidate.directWireWord.source out)⟩).semantics valuation output = _
  rw [Candidate.ofDirectWireWord_semantics]
  apply outputSource_value target keep seed _ _ valuation
  intro producer sourceAt selected
  apply (mem_terminalInterfacePorts_iff target.implementation.candidate
    (ClosedSupportObservation.records target keep seed) producer).mpr
  apply (terminalInterfaceGate_eq_true_iff target.implementation.candidate
    (ClosedSupportObservation.records target keep seed) producer).mpr
  exact ⟨selected, Or.inr
    ((terminalGateIsGlobalOutput_eq_true_iff
      target.implementation.candidate.directWireWord producer).mpr ⟨output, sourceAt⟩)⟩

theorem result_fullEquivalent (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    WireProfile.FullEquivalent target (result target keep seed) :=
  (WireProfile.full_iff target (result target keep seed)).mpr
    ⟨result_output target keep seed, fun valuation field =>
      fieldSource_value target keep seed field valuation⟩

theorem result_exact_accounting (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    (result target keep seed).implementation.gateCount +
        (extractTerminalSupport target.implementation.candidate
          (ClosedSupportObservation.records target keep seed)).gateCount =
      target.implementation.gateCount +
        (terminalSaturationCostSnapshot target.implementation.candidate
          (WireProfileAmbient.model target keep)
          (ClosedSupportObservation.records target keep seed)).fullMinimum := by
  have partition := terminalPhysicalComplementRecords_gateCount_partition
    target.implementation.candidate (ClosedSupportObservation.records target keep seed)
  have minimum := offered_gateCount target keep seed
  change ((0 + (offered target keep seed).gateCount) +
    (extractTerminalSupport target.implementation.candidate
      (terminalPhysicalComplementRecords
        (ClosedSupportObservation.records target keep seed))).gateCount) + _ = _
  omega

theorem result_gain_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    (result target keep seed).implementation.gateCount +
        (terminalSaturationCostSnapshot target.implementation.candidate
          (WireProfileAmbient.model target keep)
          (ClosedSupportObservation.records target keep seed)).fullSlack =
      target.implementation.gateCount := by
  have accounting := result_exact_accounting target keep seed
  have minimum := offered_gateCount target keep seed
  have within := offered_gateCount_le target keep seed
  change (result target keep seed).implementation.gateCount +
    ((extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep seed)).gateCount -
      (terminalSaturationCostSnapshot target.implementation.candidate
        (WireProfileAmbient.model target keep)
        (ClosedSupportObservation.records target keep seed)).fullMinimum) = _
  omega

theorem result_strict_iff (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    (result target keep seed).implementation.gateCount < target.implementation.gateCount ↔
      0 < (terminalSaturationCostSnapshot target.implementation.candidate
        (WireProfileAmbient.model target keep)
        (ClosedSupportObservation.records target keep seed)).fullSlack := by
  have balance := result_gain_balance target keep seed
  constructor
  · intro smaller
    cases slack : (terminalSaturationCostSnapshot target.implementation.candidate
      (WireProfileAmbient.model target keep)
      (ClosedSupportObservation.records target keep seed)).fullSlack with
    | zero =>
        rw [slack, Nat.add_zero] at balance
        exact False.elim ((Nat.ne_of_lt smaller) balance)
    | succ value => exact Nat.zero_lt_succ value
  · intro positive
    have grows := Nat.add_lt_add_left positive
      (result target keep seed).implementation.gateCount
    rw [Nat.add_zero, balance] at grows
    exact grows

/-- Return the computed whole-carrier improvement precisely at positive full slack.
    This searches neither for a suitable seed nor for a global route. -/
def improvement? (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) : Option (WireCarrier inputs outputs fields) :=
  if 0 < (terminalSaturationCostSnapshot target.implementation.candidate
    (WireProfileAmbient.model target keep)
    (ClosedSupportObservation.records target keep seed)).fullSlack
  then some (result target keep seed) else none

theorem improvement?_sound (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (replacement : WireCarrier inputs outputs fields)
    (found : improvement? target keep seed = some replacement) :
    WireProfile.FullEquivalent target replacement ∧
      replacement.implementation.gateCount < target.implementation.gateCount := by
  unfold improvement? at found
  split at found
  · rename_i positive
    cases found
    exact ⟨result_fullEquivalent target keep seed,
      (result_strict_iff target keep seed).mpr positive⟩
  · cases found

theorem improvement?_none_iff (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    improvement? target keep seed = none ↔
      (terminalSaturationCostSnapshot target.implementation.candidate
        (WireProfileAmbient.model target keep)
        (ClosedSupportObservation.records target keep seed)).fullSlack = 0 := by
  unfold improvement?
  split
  · rename_i positive
    constructor
    · intro impossible
      cases impossible
    · intro zero
      omega
  · rename_i notPositive
    constructor
    · intro _none
      omega
    · intro _zero
      rfl

/-- The actual whole-carrier reference minimum is invariant under the computed replacement. -/
theorem result_fullMinimum (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    WireProfile.fullMinimum (result target keep seed) = WireProfile.fullMinimum target :=
  referenceMinimum_invariant (result target keep seed).exposed target.exposed
    (result_fullEquivalent target keep seed)

/-- Local full slack is exactly the retired whole-carrier full slack. -/
theorem result_fullSlack_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    WireProfile.fullSlack (result target keep seed) +
        (terminalSaturationCostSnapshot target.implementation.candidate
          (WireProfileAmbient.model target keep)
          (ClosedSupportObservation.records target keep seed)).fullSlack =
      WireProfile.fullSlack target := by
  have physical := result_gain_balance target keep seed
  have minimumEqual := result_fullMinimum target keep seed
  have within := WireProfile.fullMinimum_le_physical (result target keep seed)
  rw [minimumEqual] at within
  unfold WireProfile.fullSlack
  rw [minimumEqual]
  omega

/-- Positive local full slack is bounded by the whole-carrier full slack. -/
theorem localFullSlack_le_global (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) :
    (terminalSaturationCostSnapshot target.implementation.candidate
      (WireProfileAmbient.model target keep)
      (ClosedSupportObservation.records target keep seed)).fullSlack ≤
      WireProfile.fullSlack target := by
  have balance := result_fullSlack_balance target keep seed
  exact balance ▸ Nat.le_add_left _ _

/-- Connect the checked optional route to the existing residual-descent interface. -/
theorem improvement?_strictGain (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount
      outputs fields)) (replacement : WireCarrier inputs outputs fields)
    (found : improvement? target keep seed = some replacement) :
    StrictEquivalentGain target.implementation replacement.implementation := by
  have checked := improvement?_sound target keep seed replacement found
  exact ⟨checked.2, ((WireProfile.full_iff target replacement).mp checked.1).1⟩

end PNP.DirectWire.ClosedSupportFullGain
