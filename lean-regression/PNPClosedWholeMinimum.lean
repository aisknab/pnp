import PNP

/- General contracts and hostile boundaries for the actual computed whole seed.
   Runtime examples are regressions, not proof authority or complexity evidence. -/

namespace PNP.DirectWire.ClosedWholeMinimumRegression

open ClosedWholeMinimum

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (extractTerminalSupport target.implementation.candidate
      (records target keep)).gateCount = target.implementation.gateCount :=
  support_gateCount target keep

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (gate : Fin target.implementation.gateCount) :
    gate ∈ (extractTerminalSupport target.implementation.candidate
      (records target keep)).interface ↔
      ∃ output, target.implementation.candidate.directWireWord.source output = .gate gate :=
  interface_iff_output target keep gate

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (snapshot target keep).fullMinimum = WireProfile.fullMinimum target :=
  full_minimum target keep

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (ClosedSupportFullGain.result target keep (seed target)).implementation.gateCount =
      WireProfile.fullMinimum target :=
  result_optimal target keep

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (snapshot target keep).fullSlack = WireProfile.fullSlack target :=
  fullSlack_eq target keep

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    WireProfile.fullSlack (ClosedSupportFullGain.result target keep (seed target)) = 0 :=
  result_zero_fullSlack target keep

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    ClosedSupportFullGain.improvement? target keep (seed target) = none ↔
      WireProfile.fullSlack target = 0 :=
  improvement_none_iff target keep

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    WireProfile.FullEquivalent target (ClosedSupportFullGain.result target keep (seed target)) :=
  ClosedSupportFullGain.result_fullEquivalent target keep (seed target)

private def empty : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

private def freeFields : WireCarrier 2 3 2 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 2 0)
      ⟨Fin.cases (.input 1) (Fin.cases (.constant true) (fun _ => .input 0))⟩).toImplementation
    source := Fin.cases (.constant false) (fun _ => .input 1) }

private def notProgram : Program 1 1 := .snoc .empty ⟨.input 0, .input 0⟩

private def hiddenNot : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord notProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def lostField : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 1 0)
      ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .constant false }

private def duplicateProgram : Program 1 2 := .snoc notProgram ⟨.input 0, .input 0⟩

private def repeatedOutputs : WireCarrier 1 2 1 :=
  { implementation := (Candidate.ofDirectWireWord duplicateProgram
      ⟨fun _ => .gate ⟨1, by decide⟩⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def hiddenDuplicate : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord duplicateProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def unusedGate : WireCarrier 1 1 0 :=
  { implementation := (Candidate.ofDirectWireWord notProgram
      ⟨fun _ => .input 0⟩).toImplementation
    source := Fin.elim0 }

private def binaryNand : WireCarrier 2 2 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (.snoc (.empty : Program 2 0) ⟨.input 0, .input 1⟩)
      ⟨Fin.cases (.gate ⟨0, by decide⟩) (fun _ => .input 1)⟩).toImplementation
    source := Fin.elim0 }

theorem hidden_field_is_nonconstant :
    hiddenNot.fieldValue (fun _ => false) 0 = true ∧
      hiddenNot.fieldValue (fun _ => true) 0 = false := by decide +kernel

theorem dropped_field_has_quotient_equivalence :
    WireProfile.QuotientEquivalent (fun _ => false) hiddenNot lostField := by
  apply (WireProfile.quotient_iff _ hiddenNot lostField).mpr
  constructor
  · intro _valuation output
    exact Fin.elim0 output
  · intro _valuation _field kept
    cases kept

theorem dropped_field_has_no_full_equivalence :
    ¬ WireProfile.FullEquivalent hiddenNot lostField := by
  intro same
  have wrong := ((WireProfile.full_iff hiddenNot lostField).mp same).2 (fun _ => false) 0
  change false = true at wrong
  cases wrong

theorem field_only_has_no_ordinary_interface {inputs fields : Nat}
    (target : WireCarrier inputs 0 fields) (keep : Fin fields → Bool)
    (gate : Fin target.implementation.gateCount) :
    gate ∉ (extractTerminalSupport target.implementation.candidate
      (records target keep)).interface := by
  intro member
  obtain ⟨output, _same⟩ := (interface_iff_output target keep gate).mp member
  exact Fin.elim0 output

theorem whole_seed_is_not_proper {inputs outputs fields : Nat}
    (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool) :
    ¬ (extractTerminalSupport target.implementation.candidate
        (records target keep)).gateCount < target.implementation.gateCount := by
  rw [support_gateCount]
  exact Nat.lt_irrefl _

theorem repeated_output_truth_values :
    repeatedOutputs.implementation.gateCount = 2 ∧
      repeatedOutputs.implementation.candidate.semantics (fun _ => false) 0 = true ∧
      repeatedOutputs.implementation.candidate.semantics (fun _ => true) 1 = false := by
  decide +kernel

private def completeCheck {inputs outputs fields : Nat}
    (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (expectedMinimum : Nat) : Bool :=
  let measured := snapshot target keep
  let rebuilt := ClosedSupportFullGain.result target keep (seed target)
  decide (measured.supportSize = target.implementation.gateCount) &&
    decide (measured.fullMinimum = expectedMinimum) &&
    decide (measured.fullMinimum = WireProfile.fullMinimum target) &&
    decide (measured.fullSlack = WireProfile.fullSlack target) &&
    decide (rebuilt.implementation.gateCount = expectedMinimum) &&
    equivalentBool rebuilt.exposed.candidate target.exposed.candidate &&
    decide (WireProfile.fullSlack rebuilt = 0) &&
    decide ((ClosedSupportFullGain.improvement? target keep (seed target)).isSome =
      decide (0 < WireProfile.fullSlack target))

private def checks : List (String × Bool) :=
  [ ("empty dimensions have no invented gate or improvement", completeCheck empty Fin.elim0 0)
  , ("primary inputs and constants need no physical gate",
      completeCheck freeFields (fun field => decide (field.val = 1)) 0)
  , ("an unobserved physical gate can disappear", completeCheck unusedGate Fin.elim0 0)
  , ("a hidden field remains required in full mode with a false keep mask",
      completeCheck hiddenNot (fun _ => false) 1 &&
        decide ((snapshot hiddenNot (fun _ => false)).quotientMinimum = 0))
  , ("repeated outputs share a computed minimum with the hidden field",
      completeCheck repeatedOutputs (fun _ => true) 1)
  , ("the whole full minimum does not change when a keep mask changes",
      completeCheck repeatedOutputs (fun _ => false) 1)
  , ("field-only duplicate gates simplify without an ordinary interface",
      completeCheck hiddenDuplicate (fun _ => false) 1)
  , ("two independent primary inputs and mixed outputs are preserved",
      completeCheck binaryNand Fin.elim0 1) ]

def run : IO Unit := do
  for (name, passed) in checks do
    if !passed then throw (IO.userError ("closed-whole-minimum: " ++ name))
    IO.println ("passed: " ++ name)

end PNP.DirectWire.ClosedWholeMinimumRegression

#print axioms PNP.DirectWire.ClosedWholeMinimumRegression.hidden_field_is_nonconstant
#print axioms PNP.DirectWire.ClosedWholeMinimumRegression.dropped_field_has_quotient_equivalence
#print axioms PNP.DirectWire.ClosedWholeMinimumRegression.dropped_field_has_no_full_equivalence
#print axioms PNP.DirectWire.ClosedWholeMinimumRegression.field_only_has_no_ordinary_interface
#print axioms PNP.DirectWire.ClosedWholeMinimumRegression.whole_seed_is_not_proper
#print axioms PNP.DirectWire.ClosedWholeMinimumRegression.repeated_output_truth_values

def main : IO Unit := do
  PNP.DirectWire.ClosedWholeMinimumRegression.run
  IO.println "closed-whole-minimum-regressions-complete: 8 general type contracts; 6 kernel guards; 8 runtime checks"
