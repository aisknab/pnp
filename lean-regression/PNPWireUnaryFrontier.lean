import PNP

namespace PNP.DirectWire.WireUnaryFrontier.Regression

def dropAll {fields : Nat} : Fin fields → Bool := fun _ => false

-- The selected unary boundary is input 2, not input 0. The exterior
-- independently computes NOT input 0, so accidental relabelling is observable.
def ambientProgram : Program 3 3 :=
  (((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 2, .input 2⟩).snoc ⟨.input 2, .gate ⟨1, by decide⟩⟩

def properCarrier : WireCarrier 3 1 1 :=
  { implementation := (Candidate.ofDirectWireWord ambientProgram
      (⟨fun _ => .gate ⟨2, by decide⟩⟩ : DirectWireWord 3 3 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

-- A forgotten selected negation must be in the complete frontier.
def hiddenNegation : WireCarrier 3 1 2 :=
  { implementation := properCarrier.implementation
    source := fun field =>
      if field.val = 0 then .gate ⟨0, by decide⟩ else .gate ⟨1, by decide⟩ }

def repeated : WireCarrier 3 4 5 :=
  { implementation := (Candidate.ofDirectWireWord ambientProgram
      (⟨fun output =>
        if output.val = 0 || output.val = 2 then .gate ⟨2, by decide⟩
        else .gate ⟨1, by decide⟩⟩ : DirectWireWord 3 3 4)).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨0, by decide⟩
      else if field.val = 2 then .input 1
      else if field.val = 4 then .gate ⟨2, by decide⟩
      else .gate ⟨1, by decide⟩ }

def constantCarrier : WireCarrier 3 1 1 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩).snoc
        ⟨.constant true, .constant false⟩)
      (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 3 2 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def twoBoundary : WireCarrier 3 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 3 0).snoc ⟨.input 0, .input 2⟩)
      (⟨fun _ => .gate ⟨0, by decide⟩⟩ : DirectWireWord 3 1 1)).toImplementation
    source := Fin.elim0 }

def wholeCarrier : WireCarrier 3 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 3 0).snoc ⟨.input 2, .input 2⟩).snoc
        ⟨.input 2, .gate ⟨0, by decide⟩⟩)
      (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 3 2 1)).toImplementation
    source := Fin.elim0 }

def minimalCarrier : WireCarrier 3 1 1 :=
  { implementation := (Candidate.ofDirectWireWord
      (((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩).snoc
        ⟨.input 2, .input 2⟩)
      (⟨fun _ => .gate ⟨1, by decide⟩⟩ : DirectWireWord 3 2 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def freeFields : WireCarrier 3 1 3 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 3 0)
      (⟨fun _ => .input 2⟩ : DirectWireWord 3 0 1)).toImplementation
    source := fun field => if field.val = 0 then .input 1
      else if field.val = 1 then .constant false else .constant true }

def fieldsOnly : WireCarrier 3 0 1 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩)
      (⟨Fin.elim0⟩ : DirectWireWord 3 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def empty : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (result : WireCarrier inputs outputs fields)
    (accepted : attempt carrier keep = some result)
    (valuation : Valuation inputs) (field : Fin fields) :
    result.fieldValue valuation field = carrier.fieldValue valuation field :=
  attempt_field carrier keep result accepted valuation field

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (attempt carrier keep).isSome = true ↔
      (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1 :=
  attempt_isSome_iff carrier keep

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (other : Implementation (WireFrontierLift.pulled carrier keep).boundary.length
      (WireFrontierLift.pulled carrier keep).interface.length)
    (sameOpen : other.candidate.semantics =
      (WireFrontierLift.pulled carrier keep).extractedCandidate.semantics) :
    (replacement carrier keep small).gateCount ≤ other.gateCount :=
  replacement_minimal carrier keep small other sameOpen

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (small : (WireFrontierLift.pulled carrier keep).boundary.length ≤ 1)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation inputs) :
    (dischargeR7 carrier keep small creation).actualSource.eval valuation
        ((expanded carrier keep small).implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  dischargeR7_full_value carrier keep small creation valuation

private def checkFixture {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields) (keep : Fin fields → Bool)
    (expectedBoundary expectedSelected expectedExterior : Nat)
    (expectedReplacement expectedResult : Option Nat) (expectedProperGain : Bool) : IO Unit := do
  if inputs > 3 || outputs > 4 || fields > 5 || carrier.implementation.gateCount > 3 then
    throw (IO.userError "fixture exceeded the reviewed small runtime envelope")
  let support := WireFrontierLift.pulled carrier keep
  let exterior := WireFrontierLift.exteriorCharge carrier keep
  if support.boundary.length != expectedBoundary || support.gateCount != expectedSelected ||
      exterior != expectedExterior then
    throw (IO.userError "the derived boundary or physical partition changed")
  if (checkedProperGain carrier keep).isSome != expectedProperGain then
    throw (IO.userError "computed proper gain ignored the boundary, exterior or strict saving")
  let answer := attempt carrier keep
  if answer.map (fun result => result.implementation.gateCount) != expectedResult then
    throw (IO.userError "the automatic frontier result changed")
  if small : support.boundary.length ≤ 1 then
    let localResult := replacement carrier keep small
    let built := expanded carrier keep small
    if some localResult.gateCount != expectedReplacement then
      throw (IO.userError "the actual minimum complete-frontier cost changed")
    if localResult.gateCount > support.gateCount || built.implementation.gateCount != localResult.gateCount + exterior then
      throw (IO.userError "the original exterior was omitted or counted more than once")
    for mask in List.range (2 ^ inputs) do
      let valuation : Valuation inputs := fun index => (mask / 2 ^ index.val) % 2 == 1
      for output in allFin outputs do
        if built.implementation.candidate.semantics valuation output !=
            carrier.implementation.candidate.semantics valuation output then
          throw (IO.userError "an ordinary output changed under the actual ambient valuation")
      for field in allFin fields do
        if built.fieldValue valuation field != carrier.fieldValue valuation field then
          throw (IO.userError "a forgotten, exterior or reordered field changed")
        if forgotten : keep field = false then
          let creation := WireObligationRestoration.createR5 carrier keep field forgotten
          let witness := dischargeR7 carrier keep small creation
          if witness.actualSource ≠ built.source field then
            throw (IO.userError "R7 did not name the actual expanded source")
          if witness.actualSource.eval valuation
              (built.implementation.candidate.program.eval valuation) !=
                carrier.fieldValue valuation field then
            throw (IO.userError "R7 used padding or a source from an unrelated program")
  else if expectedReplacement.isSome || answer.isSome then
    throw (IO.userError "a multiboundary cone escaped unary recognition")

-- Guarded executions supplement the general theorems; they are not proof authority.
#eval show IO Unit from do
  checkFixture properCarrier dropAll 1 2 1 (some 0) (some 1) true
  checkFixture hiddenNegation dropAll 1 2 1 (some 1) (some 2) true
  checkFixture hiddenNegation (fun field => field.val == 1) 1 2 1 (some 1) (some 2) true
  checkFixture repeated dropAll 1 2 1 (some 1) (some 2) true
  checkFixture constantCarrier dropAll 0 1 1 (some 0) (some 1) true
  checkFixture twoBoundary dropAll 2 1 0 none none false
  checkFixture properCarrier (fun _ => true) 2 3 0 none none false
  checkFixture wholeCarrier dropAll 1 2 0 (some 0) (some 0) false
  checkFixture minimalCarrier dropAll 1 1 1 (some 1) (some 2) false
  checkFixture freeFields dropAll 0 0 0 (some 0) (some 0) false
  checkFixture fieldsOnly dropAll 0 0 1 (some 0) (some 1) false
  checkFixture fieldsOnly (fun _ => true) 1 1 0 (some 1) (some 1) false
  checkFixture empty dropAll 0 0 0 (some 0) (some 0) false
  match (WireFrontierLift.pulled properCarrier dropAll).boundary with
  | [.input index] =>
    if index.val != 2 then
      throw (IO.userError "the actual nonzero boundary input index was relabelled")
  | _ => throw (IO.userError "the expected unary primary boundary changed")
  match attempt repeated dropAll with
  | none => throw (IO.userError "the repeated unary word was rejected")
  | some result =>
    if result.source 1 ≠ result.source 3 ∨
        result.source 1 ≠ result.implementation.candidate.directWireWord.source 1 then
      throw (IO.userError "repeated full observations no longer share one physical negation")
  IO.println "M256_COMPUTED_UNARY_FRONTIER_RUNTIME_FIXTURES_GREEN"

end PNP.DirectWire.WireUnaryFrontier.Regression
