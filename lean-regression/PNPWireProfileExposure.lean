import PNP

namespace PNP.DirectWire.WireProfileRegression

open WireProfile

-- These arbitrary-dimension signatures are independent regression expectations.
example {inputs outputs fields : Nat} (target offered : WireCarrier inputs outputs fields) :
    FullEquivalent target offered ↔
      Equivalent offered.implementation.candidate.program
        offered.implementation.candidate.directWireWord
        target.implementation.candidate.program target.implementation.candidate.directWireWord ∧
      ∀ valuation field, offered.fieldValue valuation field = target.fieldValue valuation field :=
  full_iff target offered

example {inputs outputs fields : Nat} (keep : Fin fields → Bool)
    (target offered : WireCarrier inputs outputs fields) :
    FullEquivalent target offered ↔ QuotientEquivalent keep target offered ∧
      ∀ valuation field, keep field = false →
        offered.fieldValue valuation field = target.fieldValue valuation field :=
  full_lift_iff keep target offered

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    quotientMinimum carrier keep ≤ fullMinimum carrier ∧
      fullMinimum carrier ≤ carrier.implementation.gateCount :=
  ⟨quotientMinimum_le_full carrier keep, fullMinimum_le_physical carrier⟩

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    QuotientEquivalent keep carrier (quotientWitness carrier keep) ∧
      (quotientWitness carrier keep).implementation.gateCount = quotientMinimum carrier keep :=
  ⟨quotientWitness_matches carrier keep, quotientWitness_gateCount carrier keep⟩

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (before after keep : Fin fields → Bool)
    (grows : ∀ field, before field = true → after field = true)
    (beforeContains : ∀ field, keep field = true → before field = true) :
    fullSlack (mask carrier before) = fullSlack (mask carrier after) +
        (fullMinimum (mask carrier after) - fullMinimum (mask carrier before)) ∧
      projectionDefect (mask carrier after) keep =
        projectionDefect (mask carrier before) keep +
        (fullMinimum (mask carrier after) - fullMinimum (mask carrier before)) :=
  exposure_moves_exact_slack_to_defect carrier before after keep grows beforeContains

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    FullEquivalent carrier carrier.normalize ∧
      fullMinimum carrier.normalize = fullMinimum carrier ∧
      quotientMinimum carrier.normalize keep = quotientMinimum carrier keep :=
  ⟨normalize_fullEquivalent carrier, fullMinimum_normalize carrier,
    quotientMinimum_normalize carrier keep⟩

example {inputs outputs fields replacementGates : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (replacement : Candidate
      (extractTerminalSupport carrier.exposed.candidate records).boundary.length
      replacementGates
      (extractTerminalSupport carrier.exposed.candidate records).interface.length)
    (sameOpen : replacement.semantics =
      (extractTerminalSupport carrier.exposed.candidate records).extractedCandidate.semantics)
    (result : WireCarrier inputs outputs fields)
    (accepted : carrier.splice records replacement = some result)
    (keep : Fin fields → Bool) :
    FullEquivalent carrier result ∧ fullMinimum result = fullMinimum carrier ∧
      quotientMinimum result keep = quotientMinimum carrier keep :=
  ⟨splice_fullEquivalent carrier records replacement sameOpen result accepted,
    fullMinimum_splice carrier records replacement sameOpen result accepted,
    quotientMinimum_splice carrier records replacement sameOpen result accepted keep⟩

private def notProgram : Program 1 1 :=
  .snoc .empty ⟨.input 0, .input 0⟩

private def hiddenNot : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord notProgram ⟨fun _ => .input 0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def identityOnly : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord .empty ⟨fun _ => .input 0⟩).toImplementation
    source := fun _ => .constant false }

private def wrongOrdinaryOutput : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord .empty ⟨fun _ => .constant false⟩).toImplementation
    source := fun _ => .constant false }

private theorem hidden_source_minimum : referenceMinimum hiddenNot.implementation = 0 := by
  apply Nat.le_zero.mp
  exact referenceMinimum_le_of_equivalent hiddenNot.implementation
    identityOnly.implementation.candidate (equivalentBool_sound (by decide))

private theorem hidden_full_minimum : fullMinimum hiddenNot = 1 := by decide +kernel

theorem hidden_values_record_exact_transfer :
    residualSlack hiddenNot.implementation = 1 ∧ fullSlack hiddenNot = 0 ∧
      projectionDefect hiddenNot (fun _ => false) = 1 := by
  unfold residualSlack fullSlack projectionDefect
  rw [hidden_source_minimum, hidden_full_minimum,
    quotientMinimum_forget_all, hidden_source_minimum]
  exact ⟨rfl, rfl, rfl⟩

theorem forgotten_field_permits_quotient_comparison :
    QuotientEquivalent (fun _ => false) hiddenNot identityOnly :=
  equivalentBool_sound (by decide)

theorem forgotten_field_does_not_permit_full_use :
    ¬ FullEquivalent hiddenNot identityOnly := by
  intro same
  have atFalse := ((full_iff hiddenNot identityOnly).1 same).2 (fun _ => false) 0
  change false = true at atFalse
  cases atFalse

theorem retained_field_rejects_wrong_value :
    ¬ QuotientEquivalent (fun _ => true) hiddenNot identityOnly := by
  intro same
  have atFalse := ((quotient_iff (fun _ => true) hiddenNot identityOnly).1 same).2
    (fun _ => false) 0 rfl
  change false = true at atFalse
  cases atFalse

theorem ordinary_output_cannot_be_forgotten :
    ¬ QuotientEquivalent (fun _ => false) hiddenNot wrongOrdinaryOutput := by
  intro same
  have atTrue := ((quotient_iff (fun _ => false) hiddenNot wrongOrdinaryOutput).1 same).1
    (fun _ => true) 0
  change false = true at atTrue
  cases atTrue

private def emptyCarrier : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

theorem empty_dimensions_have_zero_minimum :
    fullMinimum emptyCarrier = 0 ∧ quotientMinimum emptyCarrier Fin.elim0 = 0 := by
  have full := fullMinimum_le_physical emptyCarrier
  have quotient := quotientMinimum_le_full emptyCarrier Fin.elim0
  change fullMinimum emptyCarrier ≤ 0 at full
  exact ⟨Nat.le_zero.mp full, Nat.le_zero.mp (Nat.le_trans quotient full)⟩

end PNP.DirectWire.WireProfileRegression
