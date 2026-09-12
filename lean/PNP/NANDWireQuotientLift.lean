/-
Copyright (c) 2026 PNP Labs.

A quotient-compatible replacement is expanded with the same actual shared
materializer as the reference lift. Matched costs do not identify that lifted
reference with the original circuit: a relative saving must still pay its
whole materializer before it can be a gain against the original.

This is a computational word-level lift, not arbitrary-support Pull/Expand,
the complete obligation calculus, Package E, ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireObligationRestoration

namespace PNP.DirectWire.WireQuotientLift

variable {inputs outputs fields : Nat}

/-- Local quotient compatibility includes all ordinary outputs and every kept
computational field. It asserts no full equality of the expanded result. -/
structure QuotientAgreement (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) : Prop where
  output : ∀ valuation output,
    replacement.implementation.candidate.semantics valuation output =
      (WireObligationRestoration.projected carrier keep).implementation.candidate.semantics
        valuation output
  keptField : ∀ valuation field, keep field = true →
    replacement.fieldValue valuation field =
      (WireObligationRestoration.projected carrier keep).fieldValue valuation field

/-- The charge comes from the one actual normalized hidden-wire program. -/
def charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Nat :=
  (WireObligationRestoration.materializer carrier keep).implementation.gateCount

/-- This full reference may be larger than the original. It is not a claim
that every normalized support embeds into the original circuit. -/
def referenceLift (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs outputs fields :=
  WireObligationRestoration.restored carrier keep

/-- Append the same actual materializer to an arbitrary replacement. Ordinary
outputs and kept fields come from the replacement; lost fields do not. -/
def expanded (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) : WireCarrier inputs outputs fields :=
  WireObligationRestoration.join replacement
    (WireObligationRestoration.materializer carrier keep) keep

def referenceAgreement (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    QuotientAgreement carrier keep (WireObligationRestoration.projected carrier keep) where
  output := fun _ _ => rfl
  keptField := fun _ _ _ => rfl

theorem expanded_reference (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    expanded carrier keep (WireObligationRestoration.projected carrier keep) =
      referenceLift carrier keep := rfl

theorem referenceLift_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (referenceLift carrier keep).implementation.gateCount =
      (WireObligationRestoration.projected carrier keep).implementation.gateCount +
        charge carrier keep := rfl

theorem expanded_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) :
    (expanded carrier keep replacement).implementation.gateCount =
      replacement.implementation.gateCount + charge carrier keep := rfl

theorem referenceLift_charge_difference (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    ((referenceLift carrier keep).implementation.gateCount : Int) -
        (WireObligationRestoration.projected carrier keep).implementation.gateCount =
      charge carrier keep := by
  have accounting := referenceLift_charge carrier keep
  omega

theorem expanded_charge_difference (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) :
    ((expanded carrier keep replacement).implementation.gateCount : Int) -
        replacement.implementation.gateCount = charge carrier keep := by
  have accounting := expanded_charge carrier keep replacement
  omega

/-- The word-level materializer costs match as exact integer identities. -/
theorem matched_materializer_charge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) :
    ((referenceLift carrier keep).implementation.gateCount : Int) -
        (WireObligationRestoration.projected carrier keep).implementation.gateCount =
      ((expanded carrier keep replacement).implementation.gateCount : Int) -
        replacement.implementation.gateCount := by
  rw [referenceLift_charge_difference, expanded_charge_difference]

/-- Cancellation transports a saving against the lifted reference only. -/
theorem relative_saving_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) :
    (expanded carrier keep replacement).implementation.gateCount <
        (referenceLift carrier keep).implementation.gateCount ↔
      replacement.implementation.gateCount <
        (WireObligationRestoration.projected carrier keep).implementation.gateCount := by
  rw [expanded_charge, referenceLift_charge]
  exact ⟨Nat.lt_of_add_lt_add_right,
    fun smaller => Nat.add_lt_add_right smaller (charge carrier keep)⟩

/-- An original-circuit gain must pay the full charge, independently of any
saving measured against the lifted reference. -/
theorem original_gain_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) :
    (expanded carrier keep replacement).implementation.gateCount <
        carrier.implementation.gateCount ↔
      replacement.implementation.gateCount + charge carrier keep <
        carrier.implementation.gateCount := by
  rw [expanded_charge]

theorem expanded_output (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (expanded carrier keep replacement).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  ((WireObligationRestoration.join_output replacement
    (WireObligationRestoration.materializer carrier keep) keep valuation output).trans
      (same.output valuation output)).trans
        (WireObligationRestoration.projected_output carrier keep valuation output)

theorem expanded_kept_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) (field : Fin fields) (kept : keep field = true) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  ((WireObligationRestoration.join_kept_field replacement
    (WireObligationRestoration.materializer carrier keep) keep valuation field kept).trans
      (same.keptField valuation field kept)).trans
        (WireObligationRestoration.projected_kept_field carrier keep valuation field kept)

/-- Forgotten replacement fields are unused. The actual materializer supplies
the restored values without a quotient agreement about those fields. -/
theorem expanded_forgotten_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (valuation : Valuation inputs) (field : Fin fields) (forgotten : keep field = false) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  (WireObligationRestoration.join_forgotten_field replacement
    (WireObligationRestoration.materializer carrier keep) keep valuation field forgotten).trans
      (WireObligationRestoration.materializer_forgotten_field
        carrier keep valuation field forgotten)

theorem expanded_field (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement)
    (valuation : Valuation inputs) (field : Fin fields) :
    (expanded carrier keep replacement).fieldValue valuation field =
      carrier.fieldValue valuation field := by
  cases kept : keep field with
  | true => exact expanded_kept_field carrier keep replacement same valuation field kept
  | false => exact expanded_forgotten_field carrier keep replacement valuation field kept

theorem expanded_equivalent (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement) :
    Equivalent (expanded carrier keep replacement).implementation.candidate.program
      (expanded carrier keep replacement).implementation.candidate.directWireWord
      carrier.implementation.candidate.program carrier.implementation.candidate.directWireWord :=
  expanded_output carrier keep replacement same

/-- A full discharge binds the original lost source and the actual expanded
source. A witness for the different reference lift is not used as authority. -/
structure ExpandedDischarge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (creation : WireObligationRestoration.R5Creation carrier keep) where
  actualSource : Source inputs (expanded carrier keep replacement).implementation.gateCount
  sourceExact : actualSource = (expanded carrier keep replacement).source creation.coordinate
  fullWitness : ∀ valuation,
    actualSource.eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      creation.originalSource.eval valuation
        (carrier.implementation.candidate.program.eval valuation)

/-- Derive the expanded full-value witness from literal materializer wiring.
No agreement about the replacement's forgotten fields is required. -/
def discharge (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    ExpandedDischarge carrier keep replacement creation :=
  { actualSource := (expanded carrier keep replacement).source creation.coordinate
    sourceExact := rfl
    fullWitness := by
      intro valuation
      rw [creation.sourceExact]
      exact expanded_forgotten_field carrier keep replacement valuation
        creation.coordinate creation.forgotten }

theorem discharge_source_exact (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    (discharge carrier keep replacement creation).actualSource =
      (expanded carrier keep replacement).source creation.coordinate := rfl

theorem discharge_full_value (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation inputs) :
    (discharge carrier keep replacement creation).actualSource.eval valuation
        ((expanded carrier keep replacement).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  expanded_forgotten_field carrier keep replacement valuation
    creation.coordinate creation.forgotten

/-- The local quotient premise and actual expanded-size test are both retained.
This is not a construction of the replacement or a global equivalence oracle. -/
structure CheckedGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields) : Type where
  agreement : QuotientAgreement carrier keep replacement
  smaller : (expanded carrier keep replacement).implementation.gateCount <
    carrier.implementation.gateCount

/-- With the exact local quotient agreement, test the complete expanded cost.
Do not test only the saving against the projected or lifted reference word. -/
def checkedGain (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement) :
    Option (CheckedGain carrier keep replacement) :=
  if smaller : (expanded carrier keep replacement).implementation.gateCount <
      carrier.implementation.gateCount then
    some { agreement := same, smaller := smaller }
  else none

theorem checkedGain_isSome_iff (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (replacement : WireCarrier inputs outputs fields)
    (same : QuotientAgreement carrier keep replacement) :
    (checkedGain carrier keep replacement same).isSome = true ↔
      replacement.implementation.gateCount + charge carrier keep <
        carrier.implementation.gateCount := by
  unfold checkedGain
  split
  next smaller =>
    constructor
    · intro _accepted
      rw [← expanded_charge]
      exact smaller
    · intro _paid
      rfl
  next notSmaller =>
    constructor
    · intro impossible
      cases impossible
    · intro paid
      exact (notSmaller (by
        rw [expanded_charge]
        exact paid)).elim

def CheckedGain.strictGain {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    (gain : CheckedGain carrier keep replacement) :
    StrictEquivalentGain carrier.implementation
      (expanded carrier keep replacement).implementation where
  smaller := gain.smaller
  equivalent := expanded_equivalent carrier keep replacement gain.agreement

theorem CheckedGain.checked {carrier : WireCarrier inputs outputs fields}
    {keep : Fin fields → Bool} {replacement : WireCarrier inputs outputs fields}
    (gain : CheckedGain carrier keep replacement) :
    StrictEquivalentGain carrier.implementation
        (expanded carrier keep replacement).implementation ∧
      (∀ valuation field,
        (expanded carrier keep replacement).fieldValue valuation field =
          carrier.fieldValue valuation field) ∧
      (expanded carrier keep replacement).implementation.gateCount =
        replacement.implementation.gateCount + charge carrier keep :=
  ⟨gain.strictGain, expanded_field carrier keep replacement gain.agreement,
    expanded_charge carrier keep replacement⟩

end PNP.DirectWire.WireQuotientLift
