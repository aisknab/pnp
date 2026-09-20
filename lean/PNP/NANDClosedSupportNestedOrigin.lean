import PNP.NANDClosedSupportNestedCandidate

/-! Every value in the enlarged program comes from the smaller realization or
one actual gate in the computed physical difference. -/

namespace PNP.DirectWire.ClosedSupportNestedGain

variable {inputs outputs fields : Nat}

theorem extended_source_origin (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (offered : TerminalFullRealization
      (ClosedSupportObservation.implementation target keep small))
    (source : Source (inputs + target.implementation.gateCount)
      (extendedImplementation target keep small large offered.implementation).gateCount) :
    (∃ prior : Source (inputs + target.implementation.gateCount) offered.implementation.gateCount,
      ∀ valuation, source.eval valuation
          ((extendedImplementation target keep small large offered.implementation).candidate.program.eval
            valuation) =
        prior.eval valuation (offered.implementation.candidate.program.eval valuation)) ∨
    (∃ original : Fin target.implementation.gateCount,
      terminalGateSelected (differenceRecords target keep small large) original = true ∧
      ∀ valuation, source.eval valuation
          ((extendedImplementation target keep small large offered.implementation).candidate.program.eval
            valuation) =
        target.implementation.candidate.program.eval
          (fun input => valuation (Fin.castAdd target.implementation.gateCount input)) original) := by
  cases source with
  | input index => exact Or.inl ⟨.input index, fun _ => rfl⟩
  | constant value => exact Or.inl ⟨.constant value, fun _ => rfl⟩
  | gate index =>
      rcases finSum_decompose index with ⟨prior, rfl⟩ | ⟨position, rfl⟩
      · exact Or.inl ⟨.gate prior, fun valuation =>
          prefix_source_value target keep small large offered.implementation (.gate prior) valuation⟩
      · let original := terminalExtractionOrigin target.implementation.candidate
          (differenceRecords target keep small large) position
        have selected := terminalExtractionOrigin_selected target.implementation.candidate
          (differenceRecords target keep small large) position
        refine Or.inr ⟨original, selected, ?_⟩
        intro valuation
        have same := difference_gate_value target keep small large offered original selected valuation
        rw [terminalExtractionGateIndex_origin] at same
        exact same

theorem available_from_prefix (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (prefixImpl : Implementation (inputs + target.implementation.gateCount)
      target.implementation.gateCount)
    (field : Fin fields)
    (present : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      prefixImpl field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (extendedImplementation target keep small large prefixImpl) field = true := by
  obtain ⟨source, same⟩ := (WireProfileAmbient.available_iff_exists
    (WireProfileAmbient.ambientTarget target) prefixImpl field).mp present
  apply WireProfileAvailability.available_of_source (WireProfileAmbient.ambientTarget target)
    (extendedImplementation target keep small large prefixImpl) field
    (source.weakenGates (difference target keep small large).gateCount)
  intro valuation
  exact (prefix_source_value target keep small large prefixImpl source valuation).trans (same valuation)

theorem available_to_large (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (offered : TerminalFullRealization
      (ClosedSupportObservation.implementation target keep small))
    (field : Fin fields)
    (fieldEqual : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      offered.implementation field =
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (ClosedSupportObservation.implementation target keep small) field)
    (present : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (extendedImplementation target keep small large offered.implementation) field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (ClosedSupportObservation.implementation target keep large) field = true := by
  obtain ⟨source, same⟩ := (WireProfileAmbient.available_iff_exists
    (WireProfileAmbient.ambientTarget target)
    (extendedImplementation target keep small large offered.implementation) field).mp present
  rcases extended_source_origin target keep small large offered source with
    ⟨prior, origin⟩ | ⟨original, selected, origin⟩
  · have priorPresent := WireProfileAvailability.available_of_source
      (WireProfileAmbient.ambientTarget target) offered.implementation field prior
      (fun valuation => (origin valuation).symm.trans (same valuation))
    exact available_mono target keep small large included field (fieldEqual.symm.trans priorPresent)
  · have selectedLarge := ((difference_selected_iff target keep small large original).mp selected).1
    obtain ⟨lifted, liftedValue⟩ := ClosedSupportObservation.lift_retained_source
      target keep large (.gate original) selectedLarge
    apply WireProfileAvailability.available_of_source (WireProfileAmbient.ambientTarget target)
      (ClosedSupportObservation.implementation target keep large) field lifted
    intro valuation
    exact (liftedValue valuation).trans ((origin valuation).symm.trans (same valuation))

end PNP.DirectWire.ClosedSupportNestedGain
