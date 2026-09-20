import PNP.NANDClosedSupportNestedProgram

/-!
The physically enlarged support preserves the exact padded ordinary interface.
Its program contains the smaller realization followed only by the selected
physical difference. No cost or profile-equality certificate is assumed here.
-/

namespace PNP.DirectWire.ClosedSupportNestedGain

variable {inputs outputs fields : Nat}

private theorem interface_selected (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (seed : Seed target)
    (gate : Fin target.implementation.gateCount)
    (member : gate ∈ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep seed)).interface) :
    terminalGateSelected (ClosedSupportObservation.records target keep seed) gate = true :=
  ((terminalInterfaceGate_eq_true_iff target.implementation.candidate
    (ClosedSupportObservation.records target keep seed) gate).mp
      ((mem_terminalInterfacePorts_iff target.implementation.candidate
        (ClosedSupportObservation.records target keep seed) gate).mp member)).1

private theorem difference_of_interface (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (gate : Fin target.implementation.gateCount)
    (member : gate ∈ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep large)).interface)
    (absent : terminalGateSelected
      (ClosedSupportObservation.records target keep small) gate ≠ true) :
    terminalGateSelected (differenceRecords target keep small large) gate = true := by
  apply (difference_selected_iff target keep small large gate).mpr
  refine ⟨interface_selected target keep large gate member, ?_⟩
  cases value : terminalGateSelected
      (ClosedSupportObservation.records target keep small) gate with
  | false => rfl
  | true => exact False.elim (absent value)

def outputSource (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (prefixImpl : Implementation (inputs + target.implementation.gateCount)
      target.implementation.gateCount)
    (gate : Fin target.implementation.gateCount) :
    Source (inputs + target.implementation.gateCount)
      (prefixImpl.gateCount + (difference target keep small large).gateCount) :=
  if member : gate ∈ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep large)).interface then
    if selected : terminalGateSelected
        (ClosedSupportObservation.records target keep small) gate = true then
      (prefixImpl.candidate.directWireWord.source gate).weakenGates
        (difference target keep small large).gateCount
    else
      .gate (Fin.natAdd prefixImpl.gateCount
        (terminalExtractionGateIndex target.implementation.candidate
          (differenceRecords target keep small large) gate
          (difference_of_interface target keep small large gate member selected)))
  else .constant false

theorem ambient_output_absent (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (seed : Seed target)
    (gate : Fin target.implementation.gateCount)
    (absent : gate ∉ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep seed)).interface)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (ClosedSupportObservation.implementation target keep seed).candidate.semantics
      valuation gate = false := by
  change (terminalAmbientSupportCandidate target.implementation.candidate
    (ClosedSupportObservation.records target keep seed)).semantics valuation gate = false
  unfold terminalAmbientSupportCandidate
  rw [Candidate.ofDirectWireWord_semantics]
  simp only [DirectWire.semantics, DirectWireWord.eval,
    TerminalExtractedSupport.interfaceIndex?, dif_neg absent, Source.eval]

theorem outputSource_value (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (offered : TerminalFullRealization
      (ClosedSupportObservation.implementation target keep small))
    (gate : Fin target.implementation.gateCount)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (outputSource target keep small large offered.implementation gate).eval valuation
        ((program target keep small large offered.implementation).eval valuation) =
      (ClosedSupportObservation.implementation target keep large).candidate.semantics
        valuation gate := by
  by_cases member : gate ∈ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep large)).interface
  · by_cases selected : terminalGateSelected
        (ClosedSupportObservation.records target keep small) gate = true
    · simp only [outputSource, dif_pos member, dif_pos selected]
      exact (prefix_source_value target keep small large offered.implementation
        (offered.implementation.candidate.directWireWord.source gate) valuation).trans
        ((offered.equivalent valuation gate).trans
          ((ClosedSupportFullGain.ambient_output target keep small gate
            (larger_interface_in_smaller target keep small large included gate
              selected member) valuation).trans
            (ClosedSupportFullGain.ambient_output target keep large gate member valuation).symm))
    · simp only [outputSource, dif_pos member, dif_neg selected, Source.eval]
      exact (difference_gate_value target keep small large offered gate
        (difference_of_interface target keep small large gate member selected) valuation).trans
        (ClosedSupportFullGain.ambient_output target keep large gate member valuation).symm
  · simp only [outputSource, dif_neg member, Source.eval]
    exact (ambient_output_absent target keep large gate member valuation).symm

def extendedImplementation (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (prefixImpl : Implementation (inputs + target.implementation.gateCount)
      target.implementation.gateCount) :
    Implementation (inputs + target.implementation.gateCount) target.implementation.gateCount :=
  (Candidate.ofDirectWireWord (program target keep small large prefixImpl)
    ⟨outputSource target keep small large prefixImpl⟩).toImplementation

theorem extended_gateCount (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (prefixImpl : Implementation (inputs + target.implementation.gateCount)
      target.implementation.gateCount) :
    (extendedImplementation target keep small large prefixImpl).gateCount =
      prefixImpl.gateCount + (difference target keep small large).gateCount := rfl

def extendRealization (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (offered : TerminalFullRealization
      (ClosedSupportObservation.implementation target keep small)) :
    TerminalFullRealization (ClosedSupportObservation.implementation target keep large) :=
  { implementation := extendedImplementation target keep small large offered.implementation
    equivalent := by
      intro valuation gate
      change (Candidate.ofDirectWireWord (program target keep small large offered.implementation)
        ⟨outputSource target keep small large offered.implementation⟩).semantics valuation gate = _
      rw [Candidate.ofDirectWireWord_semantics]
      exact outputSource_value target keep small large included offered gate valuation }

end PNP.DirectWire.ClosedSupportNestedGain
