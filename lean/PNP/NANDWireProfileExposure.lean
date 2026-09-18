/-
Copyright (c) 2026 PNP Labs.

Actual computational-wire profile comparison and exact exposure balance.
Every ordinary output is preserved in both modes. Reference minima are
exhaustive specification objects, not polynomial algorithms. This is not the
complete manuscript profile grammar, terminal family or global route.
-/

import PNP.NANDWireCarrierZeroCostExposure

namespace PNP.DirectWire.WireProfile

variable {inputs outputs fields : Nat}

/-- Computational profile comparison only; ordinary outputs and gates stay intact. -/
def mask (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    WireCarrier inputs outputs fields :=
  { implementation := carrier.implementation
    source := fun field => if keep field then carrier.source field else .constant false }

theorem mask_implementation (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (mask carrier keep).implementation = carrier.implementation := rfl

theorem mask_fieldValue (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (valuation : Valuation inputs) (field : Fin fields) :
    (mask carrier keep).fieldValue valuation field =
      if keep field then carrier.fieldValue valuation field else false := by
  change (if keep field then carrier.source field else Source.constant false).eval
      valuation (carrier.implementation.candidate.program.eval valuation) = _
  cases keep field <;> rfl

def FullEquivalent (target offered : WireCarrier inputs outputs fields) : Prop :=
  Equivalent offered.exposed.candidate.program offered.exposed.candidate.directWireWord
    target.exposed.candidate.program target.exposed.candidate.directWireWord

def QuotientEquivalent (keep : Fin fields → Bool)
    (target offered : WireCarrier inputs outputs fields) : Prop :=
  FullEquivalent (mask target keep) (mask offered keep)

theorem full_iff (target offered : WireCarrier inputs outputs fields) :
    FullEquivalent target offered ↔
      Equivalent offered.implementation.candidate.program
        offered.implementation.candidate.directWireWord
        target.implementation.candidate.program target.implementation.candidate.directWireWord ∧
      ∀ valuation field, offered.fieldValue valuation field = target.fieldValue valuation field := by
  constructor
  · intro same
    constructor
    · intro valuation output
      have atOutput := same valuation (Fin.castAdd fields output)
      change offered.exposed.candidate.semantics valuation (Fin.castAdd fields output) =
        target.exposed.candidate.semantics valuation (Fin.castAdd fields output) at atOutput
      rw [WireCarrier.exposed_output, WireCarrier.exposed_output] at atOutput
      exact atOutput
    · intro valuation field
      have atField := same valuation (Fin.natAdd outputs field)
      change offered.exposed.candidate.semantics valuation (Fin.natAdd outputs field) =
        target.exposed.candidate.semantics valuation (Fin.natAdd outputs field) at atField
      simpa only [WireCarrier.exposed_field] using atField
  · rintro ⟨ordinary, profile⟩ valuation coordinate
    change offered.exposed.candidate.semantics valuation coordinate =
      target.exposed.candidate.semantics valuation coordinate
    rcases finSum_decompose coordinate with ⟨output, rfl⟩ | ⟨field, rfl⟩
    · rw [WireCarrier.exposed_output, WireCarrier.exposed_output]
      exact ordinary valuation output
    · simpa only [WireCarrier.exposed_field] using profile valuation field

theorem quotient_iff (keep : Fin fields → Bool)
    (target offered : WireCarrier inputs outputs fields) :
    QuotientEquivalent keep target offered ↔
      Equivalent offered.implementation.candidate.program
        offered.implementation.candidate.directWireWord
        target.implementation.candidate.program target.implementation.candidate.directWireWord ∧
      ∀ valuation field, keep field = true →
        offered.fieldValue valuation field = target.fieldValue valuation field := by
  constructor
  · intro same
    have parts := (full_iff (mask target keep) (mask offered keep)).1 same
    refine ⟨parts.1, ?_⟩
    intro valuation field kept
    have atField := parts.2 valuation field
    rw [mask_fieldValue, mask_fieldValue, kept] at atField
    exact atField
  · rintro ⟨ordinary, profile⟩
    apply (full_iff (mask target keep) (mask offered keep)).2
    refine ⟨ordinary, ?_⟩
    intro valuation field
    rw [mask_fieldValue, mask_fieldValue]
    cases kept : keep field with
    | false => rfl
    | true => exact profile valuation field kept

theorem full_to_quotient (keep : Fin fields → Bool)
    (target offered : WireCarrier inputs outputs fields)
    (same : FullEquivalent target offered) :
    QuotientEquivalent keep target offered :=
  (quotient_iff keep target offered).2
    ⟨((full_iff target offered).1 same).1,
      fun valuation field _ => ((full_iff target offered).1 same).2 valuation field⟩

theorem full_lift_iff (keep : Fin fields → Bool)
    (target offered : WireCarrier inputs outputs fields) :
    FullEquivalent target offered ↔
      QuotientEquivalent keep target offered ∧
      ∀ valuation field, keep field = false →
        offered.fieldValue valuation field = target.fieldValue valuation field := by
  constructor
  · intro same
    exact ⟨full_to_quotient keep target offered same,
      fun valuation field _ => ((full_iff target offered).1 same).2 valuation field⟩
  · rintro ⟨quotient, forgotten⟩
    have parts := (quotient_iff keep target offered).1 quotient
    apply (full_iff target offered).2
    refine ⟨parts.1, ?_⟩
    intro valuation field
    cases kept : keep field with
    | false => exact forgotten valuation field kept
    | true => exact parts.2 valuation field kept

def fullMinimum (carrier : WireCarrier inputs outputs fields) : Nat :=
  referenceMinimum carrier.exposed

def quotientMinimum (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Nat :=
  referenceMinimum (mask carrier keep).exposed

/-- Exhaustive semantic reference witness, not a polynomial-time construction. -/
def fullWitness (carrier : WireCarrier inputs outputs fields) :
    WireCarrier inputs outputs fields :=
  WireCarrier.unpack (referenceMinimumImplementation carrier.exposed)

theorem fullWitness_gateCount (carrier : WireCarrier inputs outputs fields) :
    (fullWitness carrier).implementation.gateCount = fullMinimum carrier := rfl

theorem fullWitness_matches (carrier : WireCarrier inputs outputs fields) :
    FullEquivalent carrier (fullWitness carrier) := by
  unfold FullEquivalent fullWitness
  rw [WireCarrier.exposed_unpack]
  exact equivalentBool_sound (referenceMinimumWitness_equivalent carrier.exposed)

theorem fullMinimum_le_physical (carrier : WireCarrier inputs outputs fields) :
    fullMinimum carrier ≤ carrier.implementation.gateCount :=
  referenceMinimum_le_target carrier.exposed

theorem quotientMinimum_le_full (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    quotientMinimum carrier keep ≤ fullMinimum carrier :=
  referenceMinimum_le_of_equivalent (mask carrier keep).exposed
    (mask (fullWitness carrier) keep).exposed.candidate
    (full_to_quotient keep carrier (fullWitness carrier) (fullWitness_matches carrier))

def quotientWitness (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : WireCarrier inputs outputs fields :=
  fullWitness (mask carrier keep)

theorem quotientWitness_gateCount (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (quotientWitness carrier keep).implementation.gateCount = quotientMinimum carrier keep := rfl

theorem quotientWitness_matches (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    QuotientEquivalent keep carrier (quotientWitness carrier keep) := by
  have parts := (full_iff (mask carrier keep) (quotientWitness carrier keep)).1
    (fullWitness_matches (mask carrier keep))
  apply (quotient_iff keep carrier (quotientWitness carrier keep)).2
  refine ⟨parts.1, ?_⟩
  intro valuation field kept
  have atField := parts.2 valuation field
  rw [mask_fieldValue, kept] at atField
  exact atField

theorem quotient_candidate_lower_bound (carrier offered : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (same : QuotientEquivalent keep carrier offered) :
    quotientMinimum carrier keep ≤ offered.implementation.gateCount :=
  referenceMinimum_le_of_equivalent (mask carrier keep).exposed
    (mask offered keep).exposed.candidate same

theorem full_candidate_lower_bound (carrier offered : WireCarrier inputs outputs fields)
    (same : FullEquivalent carrier offered) :
    fullMinimum carrier ≤ offered.implementation.gateCount :=
  referenceMinimum_le_of_equivalent carrier.exposed offered.exposed.candidate same

def fullSlack (carrier : WireCarrier inputs outputs fields) : Nat :=
  carrier.implementation.gateCount - fullMinimum carrier

def projectionDefect (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) : Nat :=
  fullMinimum carrier - quotientMinimum carrier keep

theorem fullSlack_add_projectionDefect (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    fullSlack carrier + projectionDefect carrier keep =
      carrier.implementation.gateCount - quotientMinimum carrier keep := by
  have fullBound := fullMinimum_le_physical carrier
  have quotientBound := quotientMinimum_le_full carrier keep
  unfold fullSlack projectionDefect
  omega



/-- Unexposed computational slots carry only a literal constant constraint. -/
theorem exposure_balance (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    fullSlack (mask carrier keep) =
      fullSlack carrier + projectionDefect carrier keep := by
  rw [fullSlack_add_projectionDefect]
  rfl

theorem exposure_preserves_positive_alternative (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (positive : 0 < fullSlack (mask carrier keep)) :
    0 < fullSlack carrier ∨ 0 < projectionDefect carrier keep := by
  rw [exposure_balance] at positive
  omega

/-- A strict quotient saving is not usable full evidence without restoration. -/
theorem quotient_minimum_cannot_lift_of_positive_defect
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (positive : 0 < projectionDefect carrier keep) :
    ¬ FullEquivalent carrier (quotientWitness carrier keep) := by
  intro lifted
  have lower := full_candidate_lower_bound carrier (quotientWitness carrier keep) lifted
  rw [quotientWitness_gateCount] at lower
  unfold projectionDefect at positive
  omega

/-- When full slack is lost, an actually attained quotient witness records the
remaining strict deficit. This is not a gain in the full carrier. -/
theorem exposure_loss_has_unliftable_quotient_witness
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (positive : 0 < fullSlack (mask carrier keep)) (noFullSlack : fullSlack carrier = 0) :
    QuotientEquivalent keep carrier (quotientWitness carrier keep) ∧
      (quotientWitness carrier keep).implementation.gateCount < fullMinimum carrier ∧
      ¬ FullEquivalent carrier (quotientWitness carrier keep) := by
  have alternative := exposure_preserves_positive_alternative carrier keep positive
  have defectPositive : 0 < projectionDefect carrier keep := by omega
  refine ⟨quotientWitness_matches carrier keep, ?_,
    quotient_minimum_cannot_lift_of_positive_defect carrier keep defectPositive⟩
  rw [quotientWitness_gateCount]
  unfold projectionDefect at defectPositive
  omega

/-- Reconstruct every gate's computational field from the actual source program.
This is not the manuscript's proof-only record grammar or route family. -/
def allGateFields (implementation : Implementation inputs outputs) :
    WireCarrier inputs outputs implementation.gateCount :=
  { implementation := implementation
    source := fun gate => .gate gate }

theorem allGateFields_value (implementation : Implementation inputs outputs)
    (valuation : Valuation inputs) (gate : Fin implementation.gateCount) :
    (allGateFields implementation).fieldValue valuation gate =
      implementation.candidate.program.eval valuation gate := rfl

theorem allGateFields_positive_alternative (implementation : Implementation inputs outputs)
    (keep : Fin implementation.gateCount → Bool)
    (positive : 0 < fullSlack (mask (allGateFields implementation) keep)) :
    0 < fullSlack (allGateFields implementation) ∨
      0 < projectionDefect (allGateFields implementation) keep :=
  exposure_preserves_positive_alternative (allGateFields implementation) keep positive



theorem quotientMinimum_forget_all (carrier : WireCarrier inputs outputs fields) :
    quotientMinimum carrier (fun _ => false) = referenceMinimum carrier.implementation := by
  have same : Equivalent
      (mask carrier (fun _ => false)).exposed.candidate.program
      (mask carrier (fun _ => false)).exposed.candidate.directWireWord
      (ZeroCostExposure.extend carrier.implementation
        (fun _ : Fin fields => ZeroCostExposure.Reference.constant false)).candidate.program
      (ZeroCostExposure.extend carrier.implementation
        (fun _ : Fin fields => ZeroCostExposure.Reference.constant false)).candidate.directWireWord := by
    intro valuation coordinate
    change (mask carrier (fun _ => false)).exposed.candidate.semantics valuation coordinate =
      (ZeroCostExposure.extend carrier.implementation
        (fun _ : Fin fields => ZeroCostExposure.Reference.constant false)).candidate.semantics
        valuation coordinate
    rcases finSum_decompose coordinate with ⟨output, rfl⟩ | ⟨field, rfl⟩
    · rw [WireCarrier.exposed_output, ZeroCostExposure.extend_original]
      rfl
    · rw [WireCarrier.exposed_field, mask_fieldValue, ZeroCostExposure.extend_field]
      rfl
  exact (referenceMinimum_invariant (mask carrier (fun _ => false)).exposed
    (ZeroCostExposure.extend carrier.implementation
      (fun _ : Fin fields => ZeroCostExposure.Reference.constant false)) same).trans
        (ZeroCostExposure.referenceMinimum_extend carrier.implementation _)

theorem source_slack_balance (carrier : WireCarrier inputs outputs fields) :
    residualSlack carrier.implementation =
      fullSlack carrier + projectionDefect carrier (fun _ => false) := by
  rw [fullSlack_add_projectionDefect, quotientMinimum_forget_all]
  rfl

theorem source_positive_alternative (carrier : WireCarrier inputs outputs fields)
    (positive : 0 < residualSlack carrier.implementation) :
    0 < fullSlack carrier ∨ 0 < projectionDefect carrier (fun _ => false) := by
  rw [source_slack_balance] at positive
  omega

theorem mask_absorb_equivalent (carrier : WireCarrier inputs outputs fields)
    (active keep : Fin fields → Bool) (contains : ∀ field, keep field = true → active field = true) :
    FullEquivalent (mask carrier keep) (mask (mask carrier active) keep) := by
  apply (full_iff _ _).2
  refine ⟨fun _ _ => rfl, ?_⟩
  intro valuation field
  simp only [mask_fieldValue]
  cases kept : keep field with
  | false => rfl
  | true =>
      rw [contains field kept]
      rfl

theorem quotientMinimum_mask_active (carrier : WireCarrier inputs outputs fields)
    (active keep : Fin fields → Bool) (contains : ∀ field, keep field = true → active field = true) :
    quotientMinimum (mask carrier active) keep = quotientMinimum carrier keep :=
  referenceMinimum_invariant (mask (mask carrier active) keep).exposed
    (mask carrier keep).exposed (mask_absorb_equivalent carrier active keep contains)

theorem fullMinimum_mask_mono (carrier : WireCarrier inputs outputs fields)
    (before after : Fin fields → Bool) (grows : ∀ field, before field = true → after field = true) :
    fullMinimum (mask carrier before) ≤ fullMinimum (mask carrier after) := by
  have compared := full_to_quotient before (mask carrier after)
    (fullWitness (mask carrier after)) (fullWitness_matches (mask carrier after))
  have absorbed := mask_absorb_equivalent carrier after before grows
  exact referenceMinimum_le_of_equivalent (mask carrier before).exposed
    (mask (fullWitness (mask carrier after)) before).exposed.candidate
    (Equivalent.trans compared absorbed)

/-- Any two exposure states retaining the same comparison fields have exactly
the same combined slack/defect. No forced-cost equality is assumed. -/
theorem exposure_states_balance (carrier : WireCarrier inputs outputs fields)
    (before after keep : Fin fields → Bool)
    (beforeContains : ∀ field, keep field = true → before field = true)
    (afterContains : ∀ field, keep field = true → after field = true) :
    fullSlack (mask carrier before) + projectionDefect (mask carrier before) keep =
      fullSlack (mask carrier after) + projectionDefect (mask carrier after) keep := by
  rw [fullSlack_add_projectionDefect, fullSlack_add_projectionDefect,
    quotientMinimum_mask_active carrier before keep beforeContains,
    quotientMinimum_mask_active carrier after keep afterContains]
  rfl

private theorem difference_chain (small large floor ceiling : Nat)
    (floor_le : floor ≤ small) (small_le : small ≤ large) (large_le : large ≤ ceiling) :
    ceiling - small = ceiling - large + (large - small) ∧
      large - floor = small - floor + (large - small) := by
  have first : (ceiling - small) + small =
      (ceiling - large + (large - small)) + small := by
    calc
      _ = ceiling := Nat.sub_add_cancel (Nat.le_trans small_le large_le)
      _ = (ceiling - large) + large := (Nat.sub_add_cancel large_le).symm
      _ = _ := by rw [Nat.add_assoc, Nat.sub_add_cancel small_le]
  have second : (large - floor) + floor =
      (small - floor + (large - small)) + floor := by
    calc
      _ = large := Nat.sub_add_cancel (Nat.le_trans floor_le small_le)
      _ = (large - small) + small := (Nat.sub_add_cancel small_le).symm
      _ = _ := by
        rw [Nat.add_comm (small - floor) (large - small),
          Nat.add_assoc, Nat.sub_add_cancel floor_le]
  exact ⟨Nat.add_right_cancel first, Nat.add_right_cancel second⟩

theorem exposure_moves_exact_slack_to_defect (carrier : WireCarrier inputs outputs fields)
    (before after keep : Fin fields → Bool)
    (grows : ∀ field, before field = true → after field = true)
    (beforeContains : ∀ field, keep field = true → before field = true) :
    fullSlack (mask carrier before) = fullSlack (mask carrier after) +
        (fullMinimum (mask carrier after) - fullMinimum (mask carrier before)) ∧
      projectionDefect (mask carrier after) keep =
        projectionDefect (mask carrier before) keep +
        (fullMinimum (mask carrier after) - fullMinimum (mask carrier before)) := by
  have monotone := fullMinimum_mask_mono carrier before after grows
  have afterBound := fullMinimum_le_physical (mask carrier after)
  have quotientBound := quotientMinimum_le_full (mask carrier before) keep
  have beforeQ := quotientMinimum_mask_active carrier before keep beforeContains
  have afterQ := quotientMinimum_mask_active carrier after keep
    (fun field kept => grows field (beforeContains field kept))
  rw [beforeQ] at quotientBound
  have identity := difference_chain
    (fullMinimum (mask carrier before)) (fullMinimum (mask carrier after))
    (quotientMinimum carrier keep) carrier.implementation.gateCount
    quotientBound monotone afterBound
  unfold fullSlack projectionDefect
  rw [beforeQ, afterQ]
  exact identity

/-- The existing physical normalization preserves this concrete full mode. -/
theorem normalize_fullEquivalent (carrier : WireCarrier inputs outputs fields) :
    FullEquivalent carrier carrier.normalize := by
  apply (full_iff carrier carrier.normalize).2
  exact ⟨carrier.normalize_output, carrier.normalize_field⟩

theorem fullMinimum_normalize (carrier : WireCarrier inputs outputs fields) :
    fullMinimum carrier.normalize = fullMinimum carrier :=
  referenceMinimum_invariant carrier.normalize.exposed carrier.exposed
    (normalize_fullEquivalent carrier)

theorem quotientMinimum_normalize (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    quotientMinimum carrier.normalize keep = quotientMinimum carrier keep :=
  referenceMinimum_invariant (mask carrier.normalize keep).exposed (mask carrier keep).exposed
    (full_to_quotient keep carrier carrier.normalize (normalize_fullEquivalent carrier))

section CheckedSplice

variable (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    {replacementGates : Nat}
    (replacement : Candidate
      (extractTerminalSupport carrier.exposed.candidate records).boundary.length
      replacementGates
      (extractTerminalSupport carrier.exposed.candidate records).interface.length)
    (sameOpen : replacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics)
    (result : WireCarrier inputs outputs fields)
    (accepted : carrier.splice records replacement = some result)

include records replacement sameOpen accepted

/-- Reuse the actual compiler's successful checked splice; no quotient-only word
is promoted to a full replacement by this theorem. -/
theorem splice_fullEquivalent : FullEquivalent carrier result := by
  have checked := carrier.splice_checked records replacement sameOpen result accepted
  apply (full_iff carrier result).2
  exact ⟨checked.1, checked.2.1⟩

theorem fullMinimum_splice : fullMinimum result = fullMinimum carrier :=
  referenceMinimum_invariant result.exposed carrier.exposed
    (splice_fullEquivalent carrier records replacement sameOpen result accepted)

theorem quotientMinimum_splice (keep : Fin fields → Bool) :
    quotientMinimum result keep = quotientMinimum carrier keep :=
  referenceMinimum_invariant (mask result keep).exposed (mask carrier keep).exposed
    (full_to_quotient keep carrier result
      (splice_fullEquivalent carrier records replacement sameOpen result accepted))

end CheckedSplice

end PNP.DirectWire.WireProfile
