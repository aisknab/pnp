import PNP.NANDClosedSupportNestedOrigin

/-!
Exact computational-field observations for an enlarged closed support. Both
true and false availability values are preserved. The generic comparison
is subsequently instantiated with computed full and quotient minima.
-/

namespace PNP.DirectWire.ClosedSupportNestedGain

variable {inputs outputs fields : Nat}

theorem available_from_large (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (offered : TerminalFullRealization
      (ClosedSupportObservation.implementation target keep small))
    (field : Fin fields)
    (fieldEqual : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      offered.implementation field =
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (ClosedSupportObservation.implementation target keep small) field)
    (present : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (ClosedSupportObservation.implementation target keep large) field = true) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (extendedImplementation target keep small large offered.implementation) field = true := by
  obtain ⟨source, matched, retained⟩ :=
    (ClosedSupportObservation.available_iff_retained_source target keep large field).mp present
  have sourceValue := (WireProfileAvailability.sourceMatches_iff
    target target.implementation field source).mp
      ((ClosedSupportObservation.mem_matchingSources target field source).mp matched)
  cases source with
  | input input =>
      apply WireProfileAvailability.available_of_source (WireProfileAmbient.ambientTarget target)
        (extendedImplementation target keep small large offered.implementation) field
        (.input (Fin.castAdd target.implementation.gateCount input))
      intro valuation
      exact (sourceValue _).trans
        (WireProfileFieldClosed.ambient_fieldValue target valuation field).symm
  | constant value =>
      apply WireProfileAvailability.available_of_source (WireProfileAmbient.ambientTarget target)
        (extendedImplementation target keep small large offered.implementation) field (.constant value)
      intro valuation
      exact (sourceValue _).trans
        (WireProfileFieldClosed.ambient_fieldValue target valuation field).symm
  | gate gate =>
      by_cases selected : terminalGateSelected
          (ClosedSupportObservation.records target keep small) gate = true
      · have smallPresent := ClosedSupportObservation.available_of_retained_source
          target keep small field (.gate gate) matched selected
        exact available_from_prefix target keep small large offered.implementation field
          (fieldEqual.trans smallPresent)
      · have outside : terminalGateSelected
            (ClosedSupportObservation.records target keep small) gate = false := by
          cases value : terminalGateSelected
              (ClosedSupportObservation.records target keep small) gate with
          | false => rfl
          | true => exact False.elim (selected value)
        have differenceSelected :=
          (difference_selected_iff target keep small large gate).mpr ⟨retained, outside⟩
        apply WireProfileAvailability.available_of_source (WireProfileAmbient.ambientTarget target)
          (extendedImplementation target keep small large offered.implementation) field
          (.gate (Fin.natAdd offered.implementation.gateCount
            (terminalExtractionGateIndex target.implementation.candidate
              (differenceRecords target keep small large) gate differenceSelected)))
        intro valuation
        exact (difference_gate_value target keep small large offered gate differenceSelected valuation).trans
          ((sourceValue _).trans
            (WireProfileFieldClosed.ambient_fieldValue target valuation field).symm)

private theorem bool_eq_of_true_iff (left right : Bool)
    (same : left = true ↔ right = true) : left = right := by
  cases left <;> cases right
  · rfl
  · exact False.elim (Bool.noConfusion (same.mpr rfl))
  · exact False.elim (Bool.noConfusion (same.mp rfl))
  · rfl

theorem extended_available (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (offered : TerminalFullRealization
      (ClosedSupportObservation.implementation target keep small))
    (field : Fin fields)
    (fieldEqual : WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      offered.implementation field =
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (ClosedSupportObservation.implementation target keep small) field) :
    WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
      (extendedImplementation target keep small large offered.implementation) field =
        WireProfileAvailability.available (WireProfileAmbient.ambientTarget target)
          (ClosedSupportObservation.implementation target keep large) field :=
  bool_eq_of_true_iff _ _
    ⟨available_to_large target keep small large included offered field fieldEqual,
      available_from_large target keep small large offered field fieldEqual⟩

def extendFullComparison (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (full : TerminalFullCarrierRealization
      (WireProfileAmbient.model target keep).ambientProfileSystem
      (ClosedSupportObservation.implementation target keep small)) :
    TerminalFullCarrierRealization (WireProfileAmbient.model target keep).ambientProfileSystem
      (ClosedSupportObservation.implementation target keep large) :=
  { realization := extendRealization target keep small large included full.realization
    profileEqual := fun field =>
      extended_available target keep small large included full.realization field
        (full.profileEqual field) }

def extendQuotientComparison (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (comparison : TerminalQuotientComparison
      (WireProfileAmbient.model target keep).ambientProfileSystem
      (WireProfileAmbient.model target keep).projection
      (ClosedSupportObservation.implementation target keep small)) :
    TerminalQuotientComparison (WireProfileAmbient.model target keep).ambientProfileSystem
      (WireProfileAmbient.model target keep).projection
      (ClosedSupportObservation.implementation target keep large) :=
  { realization := extendRealization target keep small large included comparison.realization
    keptProfileEqual := fun field kept =>
      extended_available target keep small large included comparison.realization field
        (comparison.keptProfileEqual field kept) }

end PNP.DirectWire.ClosedSupportNestedGain
