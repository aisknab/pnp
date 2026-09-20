import PNP.NANDClosedSupportFullGain

/-!
Derived physical differences between two computed dependency-closed supports.
This is research toward nested full/quotient cost bounds, not a completed
saturation theorem or a polynomial construction. Inclusion is a relation on
the computed gate sets, not a supplied cost or correctness certificate.
-/

namespace PNP.DirectWire.ClosedSupportNestedGain

variable {inputs outputs fields : Nat}

abbrev Seed (target : WireCarrier inputs outputs fields) :=
  List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)

def Included (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (small large : Seed target) : Prop :=
  ∀ gate, terminalGateSelected (ClosedSupportObservation.records target keep small) gate = true →
    terminalGateSelected (ClosedSupportObservation.records target keep large) gate = true

def snapshot (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : Seed target) :=
  terminalSaturationCostSnapshot target.implementation.candidate
    (WireProfileAmbient.model target keep) (ClosedSupportObservation.records target keep seed)

def differenceRecords (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (small large : Seed target) : Seed target :=
  (terminalSelectedGateIndices fun gate =>
    terminalGateSelected (ClosedSupportObservation.records target keep large) gate &&
      !(terminalGateSelected (ClosedSupportObservation.records target keep small) gate)).map
    TerminalPrimitiveRecord.gate

def difference (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (small large : Seed target) :=
  extractTerminalSupport target.implementation.candidate
    (differenceRecords target keep small large)

private theorem bool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · exact False.elim (Bool.noConfusion (same.mpr rfl))
  · exact False.elim (Bool.noConfusion (same.mp rfl))
  · rfl

theorem difference_selected (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (gate : Fin target.implementation.gateCount) :
    terminalGateSelected (differenceRecords target keep small large) gate =
      (terminalGateSelected (ClosedSupportObservation.records target keep large) gate &&
        !(terminalGateSelected (ClosedSupportObservation.records target keep small) gate)) := by
  apply bool_eq_of_true_iff
  apply (terminalGateSelected_eq_true_iff _ gate).trans
  constructor
  · intro member
    obtain ⟨found, selected, same⟩ := List.mem_map.mp member
    have equal : found = gate := TerminalPrimitiveRecord.gate.inj same
    subst found
    exact (mem_terminalSelectedGateIndices_iff _ gate).mp selected
  · intro selected
    exact List.mem_map.mpr ⟨gate,
      (mem_terminalSelectedGateIndices_iff _ gate).mpr selected, rfl⟩

theorem difference_selected_iff (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (gate : Fin target.implementation.gateCount) :
    terminalGateSelected (differenceRecords target keep small large) gate = true ↔
      terminalGateSelected (ClosedSupportObservation.records target keep large) gate = true ∧
        terminalGateSelected (ClosedSupportObservation.records target keep small) gate = false := by
  rw [difference_selected]
  cases terminalGateSelected (ClosedSupportObservation.records target keep small) gate <;>
    cases terminalGateSelected (ClosedSupportObservation.records target keep large) gate <;> decide

private theorem selected_count_difference {gates : Nat} (small large : Fin gates → Bool)
    (included : ∀ gate, small gate = true → large gate = true) :
    (terminalSelectedGateIndices small).length +
        (terminalSelectedGateIndices fun gate => large gate && !(small gate)).length =
      (terminalSelectedGateIndices large).length := by
  induction gates with
  | zero => rfl
  | succ gates ih =>
      have earlier := ih (fun gate => small gate.castSucc) (fun gate => large gate.castSucc)
        (fun gate => included gate.castSucc)
      cases smallLast : small (Fin.last gates) with
      | false =>
          cases largeLast : large (Fin.last gates) <;>
            simp only [terminalSelectedGateIndices, smallLast, largeLast, Bool.not_false,
              Bool.and_true, Bool.false_eq_true, if_false, if_true, List.length_append,
              List.length_map, List.length_cons, List.length_nil] <;> omega
      | true =>
          have largeLast := included (Fin.last gates) smallLast
          simp only [terminalSelectedGateIndices, smallLast, largeLast, Bool.not_true,
            Bool.and_false, Bool.false_eq_true, if_false, if_true, List.length_append,
            List.length_map, List.length_cons, List.length_nil]
          omega

theorem support_count_decomposition (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep small).supportSize + (difference target keep small large).gateCount =
      (snapshot target keep large).supportSize := by
  change (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep small)).gateCount +
    (extractTerminalSupport target.implementation.candidate
      (differenceRecords target keep small large)).gateCount =
    (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep large)).gateCount
  rw [extractTerminalSupport_gateCount, extractTerminalSupport_gateCount,
    extractTerminalSupport_gateCount]
  unfold terminalSelectedGates
  have selector := funext (difference_selected target keep small large)
  rw [selector]
  exact selected_count_difference _ _ included

theorem support_size_le (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep small).supportSize ≤ (snapshot target keep large).supportSize := by
  have partition := support_count_decomposition target keep small large included
  omega

theorem retained_mono (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (source : Source inputs target.implementation.gateCount)
    (present : ClosedSupportObservation.retained target keep small source = true) :
    ClosedSupportObservation.retained target keep large source = true := by
  cases source with
  | input input => rfl
  | constant value => rfl
  | gate gate => exact included gate present

theorem available_mono (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) (field : Fin fields)
    (present : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (ClosedSupportObservation.implementation target keep small) field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (ClosedSupportObservation.implementation target keep large) field = true := by
  obtain ⟨source, matched, retained⟩ :=
    (ClosedSupportObservation.available_iff_retained_source target keep small field).mp present
  exact ClosedSupportObservation.available_of_retained_source target keep large field source
    matched (retained_mono target keep small large included source retained)

theorem difference_boundary_interface (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (producer : Fin target.implementation.gateCount)
    (member : TerminalSupportWire.gate producer ∈
      (difference target keep small large).boundary) :
    producer ∈ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep small)).interface := by
  change TerminalSupportWire.gate producer ∈ terminalBoundaryPorts
    target.implementation.candidate.program (differenceRecords target keep small large) at member
  obtain ⟨external, consumer, enumerated, selected, uses⟩ :=
    (terminalBoundaryWire_eq_true_iff target.implementation.candidate.program
      (differenceRecords target keep small large) (.gate producer)).mp
      ((mem_terminalBoundaryPorts_iff target.implementation.candidate.program
        (differenceRecords target keep small large) (.gate producer)).mp member)
  have consumerParts := (difference_selected_iff target keep small large consumer).mp selected
  have producerOutside : terminalGateSelected
      (differenceRecords target keep small large) producer = false :=
    (terminalWireExternal_eq_true_iff (differenceRecords target keep small large)
      (.gate producer)).mp external
  have producerLarge : terminalGateSelected
      (ClosedSupportObservation.records target keep large) producer = true := by
    cases value : terminalGateSelected
        (ClosedSupportObservation.records target keep large) producer with
    | true => rfl
    | false =>
        have outside : terminalWireExternal
            (ClosedSupportObservation.records target keep large) (.gate producer) = true :=
          (terminalWireExternal_eq_true_iff
            (ClosedSupportObservation.records target keep large) (.gate producer)).mpr value
        have boundary : TerminalSupportWire.gate producer ∈
            (extractTerminalSupport target.implementation.candidate
              (ClosedSupportObservation.records target keep large)).boundary :=
          (mem_terminalBoundaryPorts_iff target.implementation.candidate.program
            (ClosedSupportObservation.records target keep large) (.gate producer)).mpr
            ((terminalBoundaryWire_eq_true_iff target.implementation.candidate.program
              (ClosedSupportObservation.records target keep large) (.gate producer)).mpr
              ⟨outside, consumer, enumerated, consumerParts.1, uses⟩)
        obtain ⟨input, impossible⟩ :=
          ClosedSupportObservation.boundary_isInput target keep large (.gate producer) boundary
        cases impossible
  have producerSmall : terminalGateSelected
      (ClosedSupportObservation.records target keep small) producer = true := by
    cases value : terminalGateSelected
        (ClosedSupportObservation.records target keep small) producer with
    | true => rfl
    | false =>
        have inside := (difference_selected_iff target keep small large producer).mpr
          ⟨producerLarge, value⟩
        rw [producerOutside] at inside
        cases inside
  apply (mem_terminalInterfacePorts_iff target.implementation.candidate
    (ClosedSupportObservation.records target keep small) producer).mpr
  apply (terminalInterfaceGate_eq_true_iff target.implementation.candidate
    (ClosedSupportObservation.records target keep small) producer).mpr
  exact ⟨producerSmall, Or.inl
    ((terminalGateHasExternalConsumer_eq_true_iff target.implementation.candidate.program
      (ClosedSupportObservation.records target keep small) producer).mpr
      ⟨consumer, enumerated, consumerParts.2, uses⟩)⟩

theorem larger_interface_in_smaller (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (producer : Fin target.implementation.gateCount)
    (selected : terminalGateSelected
      (ClosedSupportObservation.records target keep small) producer = true)
    (member : producer ∈ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep large)).interface) :
    producer ∈ (extractTerminalSupport target.implementation.candidate
      (ClosedSupportObservation.records target keep small)).interface := by
  have parts := (terminalInterfaceGate_eq_true_iff target.implementation.candidate
    (ClosedSupportObservation.records target keep large) producer).mp
    ((mem_terminalInterfacePorts_iff target.implementation.candidate
      (ClosedSupportObservation.records target keep large) producer).mp member)
  apply (mem_terminalInterfacePorts_iff target.implementation.candidate
    (ClosedSupportObservation.records target keep small) producer).mpr
  apply (terminalInterfaceGate_eq_true_iff target.implementation.candidate
    (ClosedSupportObservation.records target keep small) producer).mpr
  refine ⟨selected, ?_⟩
  rcases parts.2 with external | globalOutput
  · obtain ⟨consumer, enumerated, outsideLarge, uses⟩ :=
      (terminalGateHasExternalConsumer_eq_true_iff target.implementation.candidate.program
        (ClosedSupportObservation.records target keep large) producer).mp external
    have outsideSmall : terminalGateSelected
        (ClosedSupportObservation.records target keep small) consumer = false := by
      cases value : terminalGateSelected
          (ClosedSupportObservation.records target keep small) consumer with
      | false => rfl
      | true =>
          have inside := included consumer value
          rw [outsideLarge] at inside
          cases inside
    exact Or.inl ((terminalGateHasExternalConsumer_eq_true_iff
      target.implementation.candidate.program
      (ClosedSupportObservation.records target keep small) producer).mpr
      ⟨consumer, enumerated, outsideSmall, uses⟩)
  · exact Or.inr globalOutput

end PNP.DirectWire.ClosedSupportNestedGain
