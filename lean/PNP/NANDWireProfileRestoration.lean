/-
Copyright (c) 2026 PNP Labs.

Research: bind the existing actual hidden-wire materializer to the full and
quotient semantic minima. A full restored candidate need not be smaller than
the original. Reference minimization remains exhaustive, not polynomial.
-/

import PNP.NANDWireProfileExposure
import PNP.NANDWireQuotientLift
import PNP.NANDWireUnaryRealization

namespace PNP.DirectWire.WireProfileRestoration

open WireProfile

variable {inputs outputs fields : Nat}

theorem quotientAgreement_iff (carrier offered : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    WireQuotientLift.QuotientAgreement carrier keep offered ↔
      QuotientEquivalent keep carrier offered := by
  constructor
  · intro same
    apply (quotient_iff keep carrier offered).2
    exact ⟨fun valuation output =>
      (same.output valuation output).trans
        (WireObligationRestoration.projected_output carrier keep valuation output),
      fun valuation field kept =>
        (same.keptField valuation field kept).trans
          (WireObligationRestoration.projected_kept_field
            carrier keep valuation field kept)⟩
  · intro same
    have parts := (quotient_iff keep carrier offered).1 same
    exact
      { output := fun valuation output =>
          (parts.1 valuation output).trans
            (WireObligationRestoration.projected_output
              carrier keep valuation output).symm
        keptField := fun valuation field kept =>
          (parts.2 valuation field kept).trans
            (WireObligationRestoration.projected_kept_field
              carrier keep valuation field kept).symm }

theorem expanded_fullEquivalent (carrier offered : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (same : QuotientEquivalent keep carrier offered) :
    FullEquivalent carrier (WireQuotientLift.expanded carrier keep offered) := by
  have agreement := (quotientAgreement_iff carrier offered keep).2 same
  exact (full_iff carrier _).2
    ⟨WireQuotientLift.expanded_output carrier keep offered agreement,
      WireQuotientLift.expanded_field carrier keep offered agreement⟩

/-- Compute the quotient reference witness, then pay the actual shared
materializer. No replacement, full lift or agreement certificate is supplied. -/
def paidWitness (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs outputs fields :=
  WireQuotientLift.expanded carrier keep (quotientWitness carrier keep)

theorem paidWitness_fullEquivalent (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : FullEquivalent carrier (paidWitness carrier keep) :=
  expanded_fullEquivalent carrier (quotientWitness carrier keep) keep
    (quotientWitness_matches carrier keep)

theorem paidWitness_gateCount (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (paidWitness carrier keep).implementation.gateCount =
      quotientMinimum carrier keep + WireQuotientLift.charge carrier keep := by
  unfold paidWitness
  rw [WireQuotientLift.expanded_charge, quotientWitness_gateCount]

theorem fullMinimum_le_quotientMinimum_add_charge
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    fullMinimum carrier ≤
      quotientMinimum carrier keep + WireQuotientLift.charge carrier keep := by
  have bound := full_candidate_lower_bound carrier (paidWitness carrier keep)
    (paidWitness_fullEquivalent carrier keep)
  rw [paidWitness_gateCount] at bound
  exact bound

/-- A constructed materializer upper-bounds the semantic defect. Equality is
not assumed: sharing with the visible computation may make it strictly larger. -/
theorem projectionDefect_le_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    projectionDefect carrier keep ≤ WireQuotientLift.charge carrier keep := by
  have bound := fullMinimum_le_quotientMinimum_add_charge carrier keep
  unfold projectionDefect
  omega

def overhead (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Nat :=
  WireQuotientLift.charge carrier keep - projectionDefect carrier keep

theorem paidWitness_exact_overhead (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (paidWitness carrier keep).implementation.gateCount =
      fullMinimum carrier + overhead carrier keep := by
  have minimumOrder := quotientMinimum_le_full carrier keep
  have defectBound := projectionDefect_le_charge carrier keep
  rw [paidWitness_gateCount]
  unfold overhead
  unfold projectionDefect at defectBound ⊢
  omega

theorem paidWitness_smaller_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (paidWitness carrier keep).implementation.gateCount <
        carrier.implementation.gateCount ↔
      overhead carrier keep < fullSlack carrier := by
  have bound := fullMinimum_le_physical carrier
  have accounting := paidWitness_exact_overhead carrier keep
  unfold fullSlack
  constructor <;> intro comparison <;> omega

theorem paidWitness_optimal_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (paidWitness carrier keep).implementation.gateCount = fullMinimum carrier ↔
      overhead carrier keep = 0 := by
  rw [paidWitness_exact_overhead]
  constructor <;> intro comparison <;> omega

/-- Reuse the existing full-field physical normalization on the actual paid
candidate. It is not an oracle asserting that the resulting candidate is optimal. -/
def normalizedWitness (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs outputs fields :=
  (paidWitness carrier keep).normalize

def reclaimed (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Nat :=
  (runPhysicalNormalization (paidWitness carrier keep).exposed).trace.savedGates

theorem normalizedWitness_fullEquivalent (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : FullEquivalent carrier (normalizedWitness carrier keep) := by
  intro valuation coordinate
  exact (normalize_fullEquivalent (paidWitness carrier keep) valuation coordinate).trans
    (paidWitness_fullEquivalent carrier keep valuation coordinate)

theorem normalizedWitness_exact_accounting (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (normalizedWitness carrier keep).implementation.gateCount + reclaimed carrier keep =
      (paidWitness carrier keep).implementation.gateCount :=
  (paidWitness carrier keep).normalize_exact_accounting

theorem reclaimed_le_overhead (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : reclaimed carrier keep ≤ overhead carrier keep := by
  have lower := full_candidate_lower_bound carrier (normalizedWitness carrier keep)
    (normalizedWitness_fullEquivalent carrier keep)
  have paid := paidWitness_exact_overhead carrier keep
  have accounting := normalizedWitness_exact_accounting carrier keep
  omega

def remainingOverhead (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Nat :=
  overhead carrier keep - reclaimed carrier keep

theorem normalizedWitness_exact_overhead (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (normalizedWitness carrier keep).implementation.gateCount =
      fullMinimum carrier + remainingOverhead carrier keep := by
  have bound := reclaimed_le_overhead carrier keep
  have paid := paidWitness_exact_overhead carrier keep
  have accounting := normalizedWitness_exact_accounting carrier keep
  unfold remainingOverhead
  omega

theorem normalizedWitness_smaller_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (normalizedWitness carrier keep).implementation.gateCount <
        carrier.implementation.gateCount ↔
      remainingOverhead carrier keep < fullSlack carrier := by
  have bound := fullMinimum_le_physical carrier
  have accounting := normalizedWitness_exact_overhead carrier keep
  unfold fullSlack
  constructor <;> intro comparison <;> omega

theorem normalizedWitness_optimal_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (normalizedWitness carrier keep).implementation.gateCount = fullMinimum carrier ↔
      reclaimed carrier keep = overhead carrier keep := by
  have bound := reclaimed_le_overhead carrier keep
  rw [normalizedWitness_exact_overhead]
  unfold remainingOverhead
  constructor <;> intro comparison <;> omega

/-- Acceptance records the actual final-size test, not an unproved saving. -/
structure CheckedGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Type where
  smaller : (normalizedWitness carrier keep).implementation.gateCount <
    carrier.implementation.gateCount

def checkedGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Option (CheckedGain carrier keep) :=
  if smaller : (normalizedWitness carrier keep).implementation.gateCount <
      carrier.implementation.gateCount then some ⟨smaller⟩ else none

theorem checkedGain_isSome_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (checkedGain carrier keep).isSome = true ↔
      remainingOverhead carrier keep < fullSlack carrier := by
  rw [← normalizedWitness_smaller_iff]
  unfold checkedGain
  split
  next smaller => exact ⟨fun _ => smaller, fun _ => rfl⟩
  next notSmaller =>
    exact ⟨fun impossible => Bool.noConfusion impossible,
      fun smaller => False.elim (notSmaller smaller)⟩

def CheckedGain.strictGain {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} (gain : CheckedGain carrier keep) :
    StrictEquivalentGain carrier.implementation
      (normalizedWitness carrier keep).implementation where
  smaller := gain.smaller
  equivalent := ((full_iff carrier _).1
    (normalizedWitness_fullEquivalent carrier keep)).1

theorem CheckedGain.checked {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} (gain : CheckedGain carrier keep) :
    StrictEquivalentGain carrier.implementation
        (normalizedWitness carrier keep).implementation ∧
      FullEquivalent carrier (normalizedWitness carrier keep) :=
  ⟨gain.strictGain, normalizedWitness_fullEquivalent carrier keep⟩


/-- Reuse the previously proved complete unary constructor. This interface
identity does not introduce another enumerator or a new completeness premise. -/
theorem unary_fullMinimum (carrier : WireCarrier 1 outputs fields) :
    fullMinimum carrier = (WireUnaryRealization.realize carrier).implementation.gateCount := by
  apply Nat.le_antisymm
  · exact full_candidate_lower_bound carrier (WireUnaryRealization.realize carrier)
      (WireUnaryRealization.realize_full_equivalent carrier)
  · have bound := WireUnaryRealization.realize_minimal carrier (fullWitness carrier)
      (fullWitness_matches carrier)
    rw [fullWitness_gateCount] at bound
    exact bound

theorem unary_smaller_iff_fullSlack_positive (carrier : WireCarrier 1 outputs fields) :
    (WireUnaryRealization.realize carrier).implementation.gateCount <
        carrier.implementation.gateCount ↔
      0 < fullSlack carrier := by
  have bound := fullMinimum_le_physical carrier
  have minimum := unary_fullMinimum carrier
  unfold fullSlack
  constructor <;> intro comparison <;> omega

end PNP.DirectWire.WireProfileRestoration
