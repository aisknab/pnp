import PNP

namespace PNP.DirectWire.WireUnaryRealization.Regression

def dropAll {fields : Nat} : Fin fields → Bool := fun _ => false
def keepAll {fields : Nat} : Fin fields → Bool := fun _ => true

def tautologyProgram : Program 1 2 :=
  ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 0, .gate ⟨0, by decide⟩⟩

def freeFields : WireCarrier 1 3 4 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 1 0)
        (⟨fun output =>
          if output.val = 0 then .constant false
          else if output.val = 1 then .input 0 else .constant true⟩ :
          DirectWireWord 1 0 3)).toImplementation
    source := fun field =>
      if field.val = 0 then .constant true
      else if field.val = 2 then .constant false else .input 0 }

def singleNot : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord notProgram notWord).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def sharedNot : WireCarrier 1 4 5 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (tautologyProgram.snoc ⟨.input 0, .input 0⟩)
        (⟨fun output =>
          if output.val = 0 then .gate ⟨2, by decide⟩
          else if output.val = 1 then .input 0
          else if output.val = 2 then .gate ⟨0, by decide⟩
          else .constant false⟩ : DirectWireWord 1 3 4)).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨0, by decide⟩
      else if field.val = 1 then .gate ⟨1, by decide⟩
      else if field.val = 2 then .constant false
      else if field.val = 3 then .gate ⟨2, by decide⟩ else .input 0 }

def tautology : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord tautologyProgram
        (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 1 2 1)).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

-- The ordinary output is free, but its negated computational field is not.
def fieldOnlyNot : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord notProgram
        (⟨fun _ => .constant true⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def paddedFields : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 1 0)
        (⟨fun _ => .constant true⟩ : DirectWireWord 1 0 1)).toImplementation
    source := fun _ => .constant false }

-- Same numbered gate, different actual computation.
def unrelatedField : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        ((.empty : Program 1 0).snoc ⟨.constant true, .constant true⟩)
        (⟨fun _ => .constant true⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def noOutputs : WireCarrier 1 0 2 :=
  { implementation := (Candidate.ofDirectWireWord notProgram
      (⟨Fin.elim0⟩ : DirectWireWord 1 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def noFields : WireCarrier 1 1 0 :=
  { implementation := (Candidate.ofDirectWireWord notProgram notWord).toImplementation
    source := Fin.elim0 }

def emptyWord : WireCarrier 1 0 0 :=
  { implementation := (Candidate.ofDirectWireWord tautologyProgram
      (⟨Fin.elim0⟩ : DirectWireWord 1 2 0)).toImplementation
    source := Fin.elim0 }

def freeEmpty : WireCarrier 1 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 1 0)
      (⟨Fin.elim0⟩ : DirectWireWord 1 0 0)).toImplementation
    source := Fin.elim0 }

example {outputs fields : Nat} (carrier : WireCarrier 1 outputs fields)
    (valuation : Valuation 1) (field : Fin fields) :
    (realize carrier).fieldValue valuation field = carrier.fieldValue valuation field :=
  realize_field carrier valuation field

example {outputs fields : Nat} (carrier other : WireCarrier 1 outputs fields)
    (sameFull : Equivalent other.exposed.candidate.program
      other.exposed.candidate.directWireWord carrier.exposed.candidate.program
      carrier.exposed.candidate.directWireWord) :
    (realize carrier).implementation.gateCount ≤ other.implementation.gateCount :=
  realize_minimal carrier other sameFull

example {outputs fields : Nat} (carrier : WireCarrier 1 outputs fields)
    (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation 1) :
    (dischargeR7 carrier keep creation).actualSource.eval valuation
        ((realize carrier).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  dischargeR7_full_value carrier keep creation valuation

example : needsNegation freeFields = false := by decide
example : needsNegation fieldOnlyNot = true := by decide
example : (realize fieldOnlyNot).implementation.gateCount = 1 := by
  rw [realize_gateCount]
  decide
example : (realize tautology).implementation.gateCount = 0 := by
  rw [realize_gateCount]
  decide

-- Matching ordinary outputs does not imply the required full equivalence.
example : Equivalent paddedFields.implementation.candidate.program
    paddedFields.implementation.candidate.directWireWord
    fieldOnlyNot.implementation.candidate.program
    fieldOnlyNot.implementation.candidate.directWireWord := by
  intro valuation output
  change paddedFields.implementation.candidate.semantics valuation output =
    fieldOnlyNot.implementation.candidate.semantics valuation output
  unfold paddedFields fieldOnlyNot
  dsimp only [Candidate.toImplementation]
  rw [Candidate.ofDirectWireWord_semantics, Candidate.ofDirectWireWord_semantics]
  rfl

example : ¬Equivalent paddedFields.exposed.candidate.program
    paddedFields.exposed.candidate.directWireWord
    fieldOnlyNot.exposed.candidate.program fieldOnlyNot.exposed.candidate.directWireWord := by
  intro same
  have bad := same (fun _ => false) (Fin.natAdd 1 (0 : Fin 1))
  change paddedFields.exposed.candidate.semantics (fun _ => false) (Fin.natAdd 1 (0 : Fin 1)) =
    fieldOnlyNot.exposed.candidate.semantics (fun _ => false) (Fin.natAdd 1 (0 : Fin 1)) at bad
  rw [WireCarrier.exposed_field, WireCarrier.exposed_field] at bad
  change false = true at bad
  cases bad

example : unrelatedField.fieldValue (fun _ => false) 0 ≠
    fieldOnlyNot.fieldValue (fun _ => false) 0 := by decide

private def checkFullFixture {outputs fields : Nat}
    (carrier : WireCarrier 1 outputs fields) (keep : Fin fields → Bool)
    (expectedGates : Nat) (expectedGain : Bool) : IO Unit := do
  let actual := realize carrier
  if actual.implementation.gateCount != expectedGates then
    throw (IO.userError "the actual shared unary gate count changed")
  if (checkedGain carrier).isSome != expectedGain then
    throw (IO.userError "the computed complete-word strict gain changed")
  for value in [false, true] do
    let valuation : Valuation 1 := fun _ => value
    for output in allFin outputs do
      if actual.implementation.candidate.semantics valuation output !=
          carrier.implementation.candidate.semantics valuation output then
        throw (IO.userError "an ordered ordinary output changed")
    for field in allFin fields do
      if actual.fieldValue valuation field != carrier.fieldValue valuation field then
        throw (IO.userError "an ordered full computational field changed")
      if forgotten : keep field = false then
        let creation := WireObligationRestoration.createR5 carrier keep field forgotten
        let witness := dischargeR7 carrier keep creation
        if witness.actualSource ≠ actual.source field then
          throw (IO.userError "R7 did not name the actual computed source")
        if witness.actualSource.eval valuation
            (actual.implementation.candidate.program.eval valuation) !=
              carrier.fieldValue valuation field then
          throw (IO.userError "R7 used padding or an unrelated program as its full witness")

-- Small guarded executions supplement, never replace, the general Lean theorems.
#eval show IO Unit from do
  checkFullFixture freeFields dropAll 0 false
  checkFullFixture freeFields keepAll 0 false
  checkFullFixture singleNot dropAll 1 false
  checkFullFixture sharedNot (fun field => field.val == 1) 1 true
  checkFullFixture sharedNot dropAll 1 true
  checkFullFixture tautology dropAll 0 true
  checkFullFixture fieldOnlyNot dropAll 1 false
  checkFullFixture noOutputs dropAll 1 false
  checkFullFixture noFields dropAll 1 false
  checkFullFixture emptyWord dropAll 0 true
  checkFullFixture freeEmpty dropAll 0 false
  if (realize sharedNot).source 0 ≠ (realize sharedNot).source 3 then
    throw (IO.userError "repeated negation fields failed to share the same actual source")
  if (realize sharedNot).source 0 ≠
      (realize sharedNot).implementation.candidate.directWireWord.source 0 then
    throw (IO.userError "ordinary and computational negations duplicated physical ownership")

end PNP.DirectWire.WireUnaryRealization.Regression
