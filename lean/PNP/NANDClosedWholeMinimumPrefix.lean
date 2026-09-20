import PNP.NANDClosedSupportFullGain

/-!
Computed whole-support interface for the full-profile reference comparison.
The seed enumerates the actual physical gates, not a supplied support witness.
No polynomial-time or proper-local rewrite claim is made.
-/

namespace PNP.DirectWire.ClosedWholeMinimum

variable {inputs outputs fields : Nat}

def seed (target : WireCarrier inputs outputs fields) :
    List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields) :=
  (allFin target.implementation.gateCount).map TerminalPrimitiveRecord.gate

def records (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :=
  ClosedSupportObservation.records target keep (seed target)

def snapshot (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :=
  terminalSaturationCostSnapshot target.implementation.candidate
    (WireProfileAmbient.model target keep) (records target keep)

theorem gate_selected (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (gate : Fin target.implementation.gateCount) :
    terminalGateSelected (records target keep) gate = true := by
  apply (terminalGateSelected_eq_true_iff _ gate).mpr
  apply terminalSaturateRecords_extensive
  exact List.mem_map.mpr ⟨gate, mem_allFin gate, rfl⟩

theorem source_retained (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (source : Source inputs target.implementation.gateCount) :
    ClosedSupportObservation.retained target keep (seed target) source = true := by
  cases source with
  | input _ => rfl
  | constant _ => rfl
  | gate gate => exact gate_selected target keep gate

theorem available_all (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (field : Fin fields) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (ClosedSupportObservation.implementation target keep (seed target)) field = true := by
  apply ClosedSupportObservation.available_of_retained_source target keep (seed target)
    field (target.source field)
  · apply (ClosedSupportObservation.mem_matchingSources target field (target.source field)).mpr
    exact (WireProfileAvailability.sourceMatches_iff target target.implementation field
      (target.source field)).mpr (fun _ => rfl)
  · exact source_retained target keep (target.source field)

private theorem selected_all_length (gates : Nat) :
    (terminalSelectedGateIndices (fun _ : Fin gates => true)).length = gates := by
  induction gates with
  | zero => rfl
  | succ gates ih =>
      change ((terminalSelectedGateIndices (fun _ : Fin gates => true)).map Fin.castSucc ++
        [Fin.last gates]).length = gates + 1
      rw [List.length_append, List.length_map, ih]
      rfl

theorem support_gateCount (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (extractTerminalSupport target.implementation.candidate
      (records target keep)).gateCount = target.implementation.gateCount := by
  rw [extractTerminalSupport_gateCount]
  unfold terminalSelectedGates
  have allSelected : terminalGateSelected (records target keep) =
      fun _ : Fin target.implementation.gateCount => true :=
    funext (gate_selected target keep)
  rw [allSelected]
  exact selected_all_length _

theorem result_gateCount (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (ClosedSupportFullGain.result target keep (seed target)).implementation.gateCount =
      (snapshot target keep).fullMinimum := by
  have balance := ClosedSupportFullGain.result_exact_accounting target keep (seed target)
  change (ClosedSupportFullGain.result target keep (seed target)).implementation.gateCount +
    (extractTerminalSupport target.implementation.candidate (records target keep)).gateCount =
      target.implementation.gateCount + (snapshot target keep).fullMinimum at balance
  rw [support_gateCount] at balance
  exact Nat.add_right_cancel (balance.trans (Nat.add_comm _ _))

theorem global_minimum_le (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    WireProfile.fullMinimum target ≤ (snapshot target keep).fullMinimum := by
  have lower := WireProfile.full_candidate_lower_bound target
    (ClosedSupportFullGain.result target keep (seed target))
    (ClosedSupportFullGain.result_fullEquivalent target keep (seed target))
  rw [result_gateCount] at lower
  exact lower

theorem interface_iff_output (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (producer : Fin target.implementation.gateCount) :
    producer ∈ (extractTerminalSupport target.implementation.candidate
      (records target keep)).interface ↔
      ∃ output : Fin outputs,
        target.implementation.candidate.directWireWord.source output = .gate producer := by
  constructor
  · intro member
    have interface := (terminalInterfaceGate_eq_true_iff target.implementation.candidate
      (records target keep) producer).mp
        ((mem_terminalInterfacePorts_iff target.implementation.candidate
          (records target keep) producer).mp member)
    cases interface.2 with
    | inl external =>
        obtain ⟨consumer, _enumerated, absent, _uses⟩ :=
          (terminalGateHasExternalConsumer_eq_true_iff target.implementation.candidate.program
            (records target keep) producer).mp external
        rw [gate_selected target keep consumer] at absent
        cases absent
    | inr output =>
        exact (terminalGateIsGlobalOutput_eq_true_iff
          target.implementation.candidate.directWireWord producer).mp output
  · intro output
    apply (mem_terminalInterfacePorts_iff target.implementation.candidate
      (records target keep) producer).mpr
    apply (terminalInterfaceGate_eq_true_iff target.implementation.candidate
      (records target keep) producer).mpr
    exact ⟨gate_selected target keep producer, Or.inr
      ((terminalGateIsGlobalOutput_eq_true_iff
        target.implementation.candidate.directWireWord producer).mpr output)⟩

def outputIndex (target : WireCarrier inputs outputs fields)
    (producer : Fin target.implementation.gateCount) : Option (Fin outputs) :=
  (allFin outputs).find? fun output =>
    decide (target.implementation.candidate.directWireWord.source output = .gate producer)

theorem outputIndex_sound (target : WireCarrier inputs outputs fields)
    (producer : Fin target.implementation.gateCount) (output : Fin outputs)
    (found : outputIndex target producer = some output) :
    target.implementation.candidate.directWireWord.source output = .gate producer := by
  unfold outputIndex at found
  have checked := List.find?_some found
  exact of_decide_eq_true checked

theorem outputIndex_exists (target : WireCarrier inputs outputs fields)
    (producer : Fin target.implementation.gateCount)
    (visible : ∃ output : Fin outputs,
      target.implementation.candidate.directWireWord.source output = .gate producer) :
    ∃ output, outputIndex target producer = some output := by
  obtain ⟨output, same⟩ := visible
  have present : (outputIndex target producer).isSome = true :=
    List.find?_isSome.mpr ⟨output, mem_allFin output, decide_eq_true same⟩
  cases found : outputIndex target producer with
  | none =>
      rw [found] at present
      cases present
  | some index => exact ⟨index, rfl⟩

theorem outputIndex_none_not_interface (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (producer : Fin target.implementation.gateCount)
    (missing : outputIndex target producer = none) :
    producer ∉ (extractTerminalSupport target.implementation.candidate
      (records target keep)).interface := by
  intro member
  obtain ⟨output, found⟩ := outputIndex_exists target producer
    ((interface_iff_output target keep producer).mp member)
  rw [missing] at found
  cases found

theorem ambient_output_absent (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (producer : Fin target.implementation.gateCount)
    (missing : outputIndex target producer = none)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (ClosedSupportObservation.implementation target keep (seed target)).candidate.semantics
      valuation producer = false := by
  have absent := outputIndex_none_not_interface target keep producer missing
  change (terminalAmbientSupportCandidate target.implementation.candidate
    (records target keep)).semantics valuation producer = false
  unfold terminalAmbientSupportCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  simp only [DirectWire.semantics, DirectWireWord.eval,
    TerminalExtractedSupport.interfaceIndex?, dif_neg absent, Source.eval]

end PNP.DirectWire.ClosedWholeMinimum
