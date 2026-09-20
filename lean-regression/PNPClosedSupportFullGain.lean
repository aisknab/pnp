import PNP

/- Focused research regressions. General contracts have no supplied observer,
   minimum, replacement, frame, or equivalence certificate. Tiny examples test
   the construction, not global support discovery or polynomial complexity. -/

namespace PNP.DirectWire.ClosedSupportFullGainRegression

open ClosedSupportFullGain

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    WireProfile.FullEquivalent target (result target keep seed) :=
  result_fullEquivalent target keep seed

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    (result target keep seed).implementation.gateCount +
      (terminalSaturationCostSnapshot target.implementation.candidate
        (WireProfileAmbient.model target keep)
        (ClosedSupportObservation.records target keep seed)).fullSlack =
      target.implementation.gateCount :=
  result_gain_balance target keep seed

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    (result target keep seed).implementation.gateCount < target.implementation.gateCount ↔
      0 < (terminalSaturationCostSnapshot target.implementation.candidate
        (WireProfileAmbient.model target keep)
        (ClosedSupportObservation.records target keep seed)).fullSlack :=
  result_strict_iff target keep seed

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (replacement : WireCarrier inputs outputs fields)
    (found : improvement? target keep seed = some replacement) :
    WireProfile.FullEquivalent target replacement ∧
      replacement.implementation.gateCount < target.implementation.gateCount :=
  improvement?_sound target keep seed replacement found

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (valuation : Valuation inputs) (field : Fin fields) :
    (result target keep seed).fieldValue valuation field = target.fieldValue valuation field :=
  fieldSource_value target keep seed field valuation

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    improvement? target keep seed = none ↔
      (terminalSaturationCostSnapshot target.implementation.candidate
        (WireProfileAmbient.model target keep)
        (ClosedSupportObservation.records target keep seed)).fullSlack = 0 :=
  improvement?_none_iff target keep seed

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    WireProfile.fullSlack (result target keep seed) +
      (terminalSaturationCostSnapshot target.implementation.candidate
        (WireProfileAmbient.model target keep)
        (ClosedSupportObservation.records target keep seed)).fullSlack =
      WireProfile.fullSlack target :=
  result_fullSlack_balance target keep seed

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (replacement : WireCarrier inputs outputs fields)
    (found : improvement? target keep seed = some replacement) :
    StrictEquivalentGain target.implementation replacement.implementation :=
  improvement?_strictGain target keep seed replacement found

private def empty : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      ⟨Fin.elim0⟩).toImplementation
    source := Fin.elim0 }

private def freeFields : WireCarrier 1 2 2 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 1 0)
      ⟨Fin.cases (.input 0) (fun _ => .constant true)⟩).toImplementation
    source := Fin.cases (.constant false) (fun _ => .input 0) }

private def notProgram : Program 1 1 := .snoc .empty ⟨.input 0, .input 0⟩

private def hiddenNot : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord notProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def lostField : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 1 0)
      ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .constant false }

private def duplicatedProgram : Program 1 2 :=
  .snoc notProgram ⟨.input 0, .input 0⟩

private def duplicated : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord duplicatedProgram
      ⟨fun _ => .gate ⟨1, by decide⟩⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def hiddenDuplicate : WireCarrier 1 0 1 :=
  { implementation := (Candidate.ofDirectWireWord duplicatedProgram ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

/- One removable constant gate and one untouched nonconstant field/output.
   The field remains on the complement rather than being asserted available
   inside the selected support. -/
private def exteriorField : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord
      (.snoc (.snoc .empty ⟨.constant true, .constant true⟩) ⟨.input 0, .input 0⟩)
      ⟨fun _ => .gate ⟨1, by decide⟩⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

/- A genuine edge crosses from the removed support into the retained exterior.
   Replacing its true gate by false would reverse the truth table. -/
private def crossingEdge : WireCarrier 1 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (.snoc (.snoc .empty ⟨.constant false, .constant false⟩)
        ⟨.gate ⟨0, by decide⟩, .input 0⟩)
      ⟨fun _ => .gate ⟨1, by decide⟩⟩).toImplementation
    source := Fin.elim0 }

theorem hidden_field_is_nonconstant :
    hiddenNot.fieldValue (fun _ => false) 0 = true ∧
      hiddenNot.fieldValue (fun _ => true) 0 = false := by decide +kernel

theorem dropping_field_preserves_ordinary_outputs :
    Equivalent lostField.implementation.candidate.program
      lostField.implementation.candidate.directWireWord
      hiddenNot.implementation.candidate.program
      hiddenNot.implementation.candidate.directWireWord := by
  intro _valuation output
  exact Fin.elim0 output

theorem dropping_field_is_not_full_equivalence :
    ¬ WireProfile.FullEquivalent hiddenNot lostField := by
  intro same
  have atFalse := ((WireProfile.full_iff hiddenNot lostField).mp same).2 (fun _ => false) 0
  change false = true at atFalse
  cases atFalse

theorem crossing_edge_is_not_optional :
    crossingEdge.implementation.candidate.semantics (fun _ => false) 0 = true ∧
      crossingEdge.implementation.candidate.semantics (fun _ => true) 0 = false := by decide +kernel

theorem exterior_field_is_nonconstant :
    exteriorField.fieldValue (fun _ => false) 0 = true ∧
      exteriorField.fieldValue (fun _ => true) 0 = false := by decide +kernel

private def preservesAll {inputs outputs fields : Nat}
    (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :
    Bool :=
  equivalentBool (result target keep seed).exposed.candidate target.exposed.candidate

private def snapshot {inputs outputs fields : Nat}
    (target : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields)) :=
  terminalSaturationCostSnapshot target.implementation.candidate
    (WireProfileAmbient.model target keep) (ClosedSupportObservation.records target keep seed)

private def checks : List (String × Bool) :=
  [ ("empty dimensions do not manufacture a gain",
      decide ((result empty Fin.elim0 []).implementation.gateCount = 0) &&
        !(improvement? empty Fin.elim0 []).isSome && preservesAll empty Fin.elim0 [])
  , ("primary-input and constant fields cost no gates",
      decide ((result freeFields (fun _ => true) []).implementation.gateCount = 0) &&
        preservesAll freeFields (fun _ => true) [])
  , ("hidden internal field blocks an ordinary-output-only deletion",
      let seed := [TerminalPrimitiveRecord.gate (inputs := 1) (outputs := 0)
        (profileWidth := 1) (⟨0, by decide⟩ : Fin 1)]
      decide ((snapshot hiddenNot (fun _ => false) seed).fullMinimum = 1) &&
        decide ((snapshot hiddenNot (fun _ => false) seed).quotientMinimum = 0) &&
        !(improvement? hiddenNot (fun _ => false) seed).isSome &&
        preservesAll hiddenNot (fun _ => false) seed)
  , ("ordinary-output equivalence cannot substitute for full profile equivalence",
      equivalentBool lostField.implementation.candidate hiddenNot.implementation.candidate &&
        !(equivalentBool lostField.exposed.candidate hiddenNot.exposed.candidate))
  , ("duplicate gates give a strict whole-span gain",
      let seed := [TerminalPrimitiveRecord.gate (inputs := 1) (outputs := 1)
        (profileWidth := 1) (⟨0, by decide⟩ : Fin 2)]
      decide ((snapshot duplicated (fun _ => true) seed).supportSize = 2) &&
        decide ((snapshot duplicated (fun _ => true) seed).fullSlack = 1) &&
        decide ((result duplicated (fun _ => true) seed).implementation.gateCount = 1) &&
        (improvement? duplicated (fun _ => true) seed).isSome &&
        preservesAll duplicated (fun _ => true) seed)
  , ("field-only improvement retains an internal value absent from all ordinary outputs",
      let seed := [TerminalPrimitiveRecord.gate (inputs := 1) (outputs := 0)
        (profileWidth := 1) (⟨0, by decide⟩ : Fin 2)]
      decide ((result hiddenDuplicate (fun _ => false) seed).implementation.gateCount = 1) &&
        (improvement? hiddenDuplicate (fun _ => false) seed).isSome &&
        preservesAll hiddenDuplicate (fun _ => false) seed)
  , ("proper gain retains a nonconstant exterior field",
      let seed := [TerminalPrimitiveRecord.gate (inputs := 1) (outputs := 1)
        (profileWidth := 1) (⟨0, by decide⟩ : Fin 2)]
      decide ((snapshot exteriorField (fun _ => true) seed).supportSize = 1) &&
        decide ((result exteriorField (fun _ => true) seed).implementation.gateCount = 1) &&
        (improvement? exteriorField (fun _ => true) seed).isSome &&
        preservesAll exteriorField (fun _ => true) seed)
  , ("reconnection preserves a real support-to-exterior edge",
      let seed := [TerminalPrimitiveRecord.gate (inputs := 1) (outputs := 1)
        (profileWidth := 0) (⟨0, by decide⟩ : Fin 2)]
      decide ((snapshot crossingEdge Fin.elim0 seed).supportSize = 1) &&
        decide ((result crossingEdge Fin.elim0 seed).implementation.gateCount = 1) &&
        (improvement? crossingEdge Fin.elim0 seed).isSome &&
        preservesAll crossingEdge Fin.elim0 seed)
  , ("empty selected support reconstructs all exterior values with no gain",
      decide ((result hiddenNot (fun _ => false) []).implementation.gateCount = 1) &&
        !(improvement? hiddenNot (fun _ => false) []).isSome &&
        preservesAll hiddenNot (fun _ => false) [])
  , ("profile metadata seed derives the field-bearing support",
      let seed := [TerminalPrimitiveRecord.profile (inputs := 1) (gates := 2)
        (outputs := 0) (0 : Fin 1)]
      decide ((snapshot hiddenDuplicate (fun _ => true) seed).supportSize = 2) &&
        decide ((result hiddenDuplicate (fun _ => true) seed).implementation.gateCount = 1) &&
        preservesAll hiddenDuplicate (fun _ => true) seed) ]

def run : IO Unit := do
  for (name, passed) in checks do
    if !passed then throw (IO.userError ("closed-support-full-gain: " ++ name))
    IO.println ("passed: " ++ name)

end PNP.DirectWire.ClosedSupportFullGainRegression

#print axioms PNP.DirectWire.ClosedSupportFullGainRegression.hidden_field_is_nonconstant
#print axioms PNP.DirectWire.ClosedSupportFullGainRegression.dropping_field_preserves_ordinary_outputs
#print axioms PNP.DirectWire.ClosedSupportFullGainRegression.dropping_field_is_not_full_equivalence
#print axioms PNP.DirectWire.ClosedSupportFullGainRegression.crossing_edge_is_not_optional
#print axioms PNP.DirectWire.ClosedSupportFullGainRegression.exterior_field_is_nonconstant

def main : IO Unit := do
  PNP.DirectWire.ClosedSupportFullGainRegression.run
  IO.println "closed-support-full-gain-regressions-complete: 8 general type contracts; 5 kernel guards; 10 runtime checks"
