import PNP

namespace PNP.DirectWire.WireProfileAvailabilityRegression

open WireProfileAvailability

-- Independent arbitrary-dimension type contracts.
example {n m k : Nat} (target : WireCarrier n m k) (candidate : Implementation n m) :
    (bind target candidate).implementation = candidate :=
  bind_implementation target candidate

example {n m k : Nat} (target : WireCarrier n m k) (candidate : Implementation n m)
    (field : Fin k) (present : available target candidate field = true) :
    ∀ valuation, (bind target candidate).fieldValue valuation field =
      target.fieldValue valuation field :=
  bind_fieldValue target candidate field present

example {n m k : Nat} (target : WireCarrier n m k) :
    terminalFullProfileMinimum (system target) target.implementation =
      WireProfile.fullMinimum target :=
  full_minimum target

example {n m k : Nat} (target : WireCarrier n m k) (keep : Fin k → Bool) :
    terminalQuotientProfileMinimum (system target) ⟨keep⟩ target.implementation =
      WireProfile.quotientMinimum target keep :=
  quotient_minimum target keep

example {n m k : Nat} (target : WireCarrier n m k) (candidate : Implementation n m) :
    terminalFullProfileMatchBool (system target) target.implementation candidate = true ↔
      WireProfile.FullEquivalent target (bind target candidate) :=
  full_match_iff target candidate

example {n m k : Nat} (target : WireCarrier n m k)
    (candidate : Implementation n m) (keep : Fin k → Bool) :
    terminalQuotientProfileMatchBool (system target) ⟨keep⟩
      target.implementation candidate = true ↔
      WireProfile.QuotientEquivalent keep target (bind target candidate) :=
  quotient_match_iff target candidate keep

example {n m k : Nat} (left right : WireCarrier n m k)
    (same : WireProfile.FullEquivalent left right) :
    system left = system right :=
  system_fullEquivalent left right same

private def notProgram : Program 1 1 :=
  .snoc .empty ⟨.input 0, .input 0⟩

private def hiddenNot : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord notProgram ⟨fun _ => .input 0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def identityOnly : Implementation 1 1 :=
  (Candidate.ofDirectWireWord .empty ⟨fun _ => .input 0⟩).toImplementation

private def wrongOutput : Implementation 1 1 :=
  (Candidate.ofDirectWireWord notProgram ⟨fun _ => .constant false⟩).toImplementation

private def wrongBinding : WireCarrier 1 1 1 :=
  { implementation := hiddenNot.implementation
    source := fun _ => .constant false }

private def repeatedFields : WireCarrier 1 1 3 :=
  { implementation := hiddenNot.implementation
    source := fun field =>
      if field.val = 1 then .input 0 else .gate ⟨0, by decide⟩ }

private def emptyCarrier : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

private def binaryNand : WireCarrier 2 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (Program.snoc .empty ⟨.input 0, .input 1⟩) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def binaryEmpty : Implementation 2 0 :=
  (Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩).toImplementation

theorem availability_is_not_arbitrary_binding_equality :
    available hiddenNot wrongBinding.implementation 0 = true ∧
      ¬ WireProfile.FullEquivalent hiddenNot wrongBinding := by
  refine ⟨current_available hiddenNot 0, ?_⟩
  intro same
  have atFalse := ((WireProfile.full_iff hiddenNot wrongBinding).mp same).2
    (fun _ => false) 0
  change false = true at atFalse
  cases atFalse

theorem missing_field_is_rejected :
    available hiddenNot identityOnly 0 = false := by decide +kernel

theorem ordinary_output_is_still_required :
    available hiddenNot wrongOutput 0 = true ∧
      terminalQuotientProfileMatchBool (system hiddenNot) ⟨fun _ => false⟩
        hiddenNot.implementation wrongOutput = false := by decide +kernel

theorem pointwise_choice_is_not_one_uniform_source :
    (∀ valuation : Valuation 2, ∃ source : Source 2 binaryEmpty.gateCount,
      source.eval valuation (binaryEmpty.candidate.program.eval valuation) =
        binaryNand.fieldValue valuation 0) ∧
    ¬ (∃ source : Source 2 binaryEmpty.gateCount, ∀ valuation,
      source.eval valuation (binaryEmpty.candidate.program.eval valuation) =
        binaryNand.fieldValue valuation 0) := by
  constructor
  · intro valuation
    exact ⟨.constant (binaryNand.fieldValue valuation 0), rfl⟩
  · rintro ⟨source, uniform⟩
    have accepted := available_of_source binaryNand binaryEmpty 0 source uniform
    have rejected : available binaryNand binaryEmpty 0 = false := by decide +kernel
    rw [rejected] at accepted
    cases accepted

#print axioms availability_is_not_arbitrary_binding_equality
#print axioms missing_field_is_rejected
#print axioms ordinary_output_is_still_required
#print axioms pointwise_choice_is_not_one_uniform_source

def run : IO Unit := do
  let checks : List (String × Bool) := [
    ("self availability and zero gate overhead",
      available hiddenNot hiddenNot.implementation 0 &&
        ((bind hiddenNot hiddenNot.implementation).implementation.gateCount == 1)),
    ("missing field rejected in full and retained modes",
      !(terminalFullProfileMatchBool (system hiddenNot) hiddenNot.implementation identityOnly) &&
        !(terminalQuotientProfileMatchBool (system hiddenNot) ⟨fun _ => true⟩
          hiddenNot.implementation identityOnly)),
    ("forgotten missing field allowed only as quotient",
      terminalQuotientProfileMatchBool (system hiddenNot) ⟨fun _ => false⟩
        hiddenNot.implementation identityOnly),
    ("ordinary outputs cannot be forgotten",
      available hiddenNot wrongOutput 0 &&
        !(terminalFullProfileMatchBool (system hiddenNot) hiddenNot.implementation wrongOutput) &&
        !(terminalQuotientProfileMatchBool (system hiddenNot) ⟨fun _ => false⟩
          hiddenNot.implementation wrongOutput)),
    ("existing wrong binding is reconstructed",
      !(equivalentBool wrongBinding.exposed.candidate hiddenNot.exposed.candidate) &&
        equivalentBool (bind hiddenNot wrongBinding.implementation).exposed.candidate
          hiddenNot.exposed.candidate),
    ("repeated fields share existing sources",
      allTrue (allFin 3) (available repeatedFields repeatedFields.implementation) &&
        ((bind repeatedFields repeatedFields.implementation).implementation.gateCount == 1) &&
        equivalentBool (bind repeatedFields repeatedFields.implementation).exposed.candidate
          repeatedFields.exposed.candidate),
    ("empty dimensions",
      terminalFullProfileMatchBool (system emptyCarrier)
        emptyCarrier.implementation emptyCarrier.implementation &&
        terminalQuotientProfileMatchBool (system emptyCarrier) ⟨Fin.elim0⟩
          emptyCarrier.implementation emptyCarrier.implementation &&
        ((bind emptyCarrier emptyCarrier.implementation).implementation.gateCount == 0)),
    ("all-input source matching is uniform",
      !(available binaryNand binaryEmpty 0) &&
        terminalQuotientProfileMatchBool (system binaryNand) ⟨fun _ => false⟩
          binaryNand.implementation binaryEmpty)]
  for (name, accepted) in checks do
    if !accepted then
      throw (IO.userError ("wire-profile-availability regression failed: " ++ name))
  IO.println s!"wire-profile-availability-regressions: {checks.length} passed"

end PNP.DirectWire.WireProfileAvailabilityRegression

def main : IO Unit := PNP.DirectWire.WireProfileAvailabilityRegression.run
