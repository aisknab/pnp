import PNP

namespace PNP.DirectWire.WireUnaryArbitrarySupport.Regression

def dropAll {fields : Nat} : Fin fields → Bool := fun _ => false

def selected {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (indices : List (Fin carrier.implementation.gateCount)) :
    List (TerminalPrimitiveRecord inputs carrier.implementation.gateCount (outputs + fields) 0) :=
  indices.map TerminalPrimitiveRecord.gate

-- The early selected constant is consumed by the exterior boundary gate.
-- The late selected NOT consumes that boundary gate. Replacing the early
-- frontier port by an input or NOT would create a real feedback cycle.
def interleavedProgram (earlyValue : Bool) : Program 3 3 :=
  (((.empty : Program 3 0).snoc ⟨.constant true, .constant (!earlyValue)⟩).snoc
    ⟨.gate ⟨0, by decide⟩, .input 2⟩).snoc ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩

def interleaved (earlyValue : Bool) : WireCarrier 3 1 3 :=
  { implementation := (Candidate.ofDirectWireWord (interleavedProgram earlyValue)
      (⟨fun _ => .gate ⟨2, by decide⟩⟩ : DirectWireWord 3 3 1)).toImplementation
    source := fun field => .gate ⟨field.val, field.isLt⟩ }

-- The selected primary boundary is input 2, not input 0. Its exterior uses input 0.
def primaryProgram : Program 3 3 :=
  (((.empty : Program 3 0).snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 2, .input 2⟩).snoc ⟨.input 2, .gate ⟨1, by decide⟩⟩

def primaryCarrier (hiddenNegation : Bool) : WireCarrier 3 1 2 :=
  { implementation := (Candidate.ofDirectWireWord primaryProgram
      (⟨fun _ => .gate ⟨2, by decide⟩⟩ : DirectWireWord 3 3 1)).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨0, by decide⟩
      else if hiddenNegation then .gate ⟨1, by decide⟩ else .constant true }

def repeated : WireCarrier 3 4 5 :=
  { implementation := (Candidate.ofDirectWireWord primaryProgram
      (⟨fun output => if output.val = 0 || output.val = 2 then .gate ⟨2, by decide⟩
        else .gate ⟨1, by decide⟩⟩ : DirectWireWord 3 3 4)).toImplementation
    source := fun field =>
      if field.val = 0 then .gate ⟨0, by decide⟩
      else if field.val = 2 then .input 1
      else if field.val = 4 then .gate ⟨2, by decide⟩
      else .gate ⟨1, by decide⟩ }

def twoBoundary : WireCarrier 3 1 0 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 3 0).snoc ⟨.input 0, .input 2⟩)
      (⟨fun _ => .gate ⟨0, by decide⟩⟩ : DirectWireWord 3 1 1)).toImplementation
    source := Fin.elim0 }

def fieldsOnly : WireCarrier 3 0 1 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 3 0).snoc ⟨.input 2, .input 2⟩)
      (⟨Fin.elim0⟩ : DirectWireWord 3 1 0)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def freeFields : WireCarrier 3 1 3 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 3 0)
      (⟨fun _ => .input 2⟩ : DirectWireWord 3 0 1)).toImplementation
    source := fun field => if field.val = 0 then .input 1
      else if field.val = 1 then .constant false else .constant true }

def emptyCarrier : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (small : (pulled carrier records).boundary.length ≤ 1) :
    (ArbitrarySupportSplice.compile carrier.exposed.candidate records
      (replacement carrier records small).candidate).isSome = true :=
  compile_isSome carrier records small

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0)) :
    (attempt carrier records).isSome = true ↔ (pulled carrier records).boundary.length ≤ 1 :=
  attempt_isSome_iff carrier records

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (result : WireCarrier inputs outputs fields) (accepted : attempt carrier records = some result)
    (valuation : Valuation inputs) (field : Fin fields) :
    result.fieldValue valuation field = carrier.fieldValue valuation field :=
  attempt_field carrier records result accepted valuation field

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (small : (pulled carrier records).boundary.length ≤ 1)
    (other : Implementation (pulled carrier records).boundary.length
      (pulled carrier records).interface.length)
    (sameOpen : other.candidate.semantics = (pulled carrier records).extractedCandidate.semantics) :
    (replacement carrier records small).gateCount ≤ other.gateCount :=
  replacement_minimal carrier records small other sameOpen

def checkFixture {inputs outputs fields : Nat} (name : String)
    (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (expectedBoundary expectedSelected expectedExterior : Nat)
    (expectedReplacement expectedResult : Option Nat) (expectedProper : Bool) : IO Unit := do
  if inputs > 3 || outputs > 4 || fields > 5 || carrier.implementation.gateCount > 3 ||
      records.length > 6 then
    throw (IO.userError "fixture exceeds the guarded runtime dimensions")
  let support := pulled carrier records
  let exterior := exteriorCharge carrier records
  if support.boundary.length != expectedBoundary || support.gateCount != expectedSelected ||
      exterior != expectedExterior then
    throw (IO.userError (name ++ ": actual boundary/support/exterior changed"))
  let answer := attempt carrier records
  if answer.map (fun result => result.implementation.gateCount) != expectedResult then
    throw (IO.userError (name ++ ": computed replacement result changed"))
  if (checkedProperGain carrier records).isSome != expectedProper then
    throw (IO.userError (name ++ ": properness or strict saving was misclassified"))
  if small : support.boundary.length ≤ 1 then
    let localResult := replacement carrier records small
    let built := expanded carrier records small
    if some localResult.gateCount != expectedReplacement then
      throw (IO.userError (name ++ ": complete open-function minimum changed"))
    if localResult.gateCount > support.gateCount ||
        built.implementation.gateCount != localResult.gateCount + exterior then
      throw (IO.userError (name ++ ": exterior was omitted or charged more than once"))
    for mask in List.range (2 ^ support.boundary.length) do
      let boundary : Valuation support.boundary.length :=
        fun index => (mask / 2 ^ index.val) % 2 == 1
      for port in allFin support.interface.length do
        if localResult.candidate.semantics boundary port !=
            support.extractedCandidate.semantics boundary port then
          throw (IO.userError (name ++ ": open agreement omitted a non-induced valuation"))
    for mask in List.range (2 ^ inputs) do
      let valuation : Valuation inputs := fun index => (mask / 2 ^ index.val) % 2 == 1
      for output in allFin outputs do
        if built.implementation.candidate.semantics valuation output !=
            carrier.implementation.candidate.semantics valuation output then
          throw (IO.userError (name ++ ": ordinary output changed"))
      for field in allFin fields do
        if built.fieldValue valuation field != carrier.fieldValue valuation field then
          throw (IO.userError (name ++ ": selected, exterior or repeated field changed"))
        let creation := WireObligationRestoration.createR5 carrier dropAll field rfl
        let witness := dischargeR7 carrier records small dropAll creation
        if witness.actualSource ≠ built.source field then
          throw (IO.userError (name ++ ": R7 source is not the actual expanded source"))
        if witness.actualSource.eval valuation
            (built.implementation.candidate.program.eval valuation) !=
              carrier.fieldValue valuation field then
          throw (IO.userError (name ++ ": R7 used padding or an unrelated source"))
  else if expectedReplacement.isSome || answer.isSome then
    throw (IO.userError (name ++ ": multiboundary support escaped recognition"))
  IO.println ("M257_FIXTURE_GREEN=" ++ name)

-- All enumerations above are guarded regression evidence, not theorem authority.
#eval show IO Unit from do
  let live := interleaved true
  let unrealizable := interleaved false
  checkFixture "external-gate-cycle-prevention" live (selected live [⟨0, by decide⟩, ⟨2, by decide⟩])
    1 2 1 (some 1) (some 2) true
  checkFixture "unrealizable-boundary-bit" unrealizable (selected unrealizable [⟨0, by decide⟩, ⟨2, by decide⟩])
    1 2 1 (some 1) (some 2) true
  checkFixture "repeated-nonprefix-support" live (selected live [⟨2, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩])
    1 2 1 (some 1) (some 2) true
  checkFixture "constant-support" live (selected live [⟨0, by decide⟩])
    0 1 2 (some 0) (some 2) true
  checkFixture "external-gate-no-saving" live (selected live [⟨2, by decide⟩])
    1 1 2 (some 1) (some 3) false
  checkFixture "whole-support-is-not-proper" live (selected live [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩])
    1 3 0 (some 1) (some 1) false
  checkFixture "input-plus-exterior-boundary-rejected" live (selected live [⟨1, by decide⟩, ⟨2, by decide⟩])
    2 2 1 none none false
  checkFixture "empty-selected-support" live []
    0 0 3 (some 0) (some 3) false
  let primary := primaryCarrier false
  let hidden := primaryCarrier true
  checkFixture "nonzero-primary-input" primary (selected primary [⟨1, by decide⟩, ⟨2, by decide⟩])
    1 2 1 (some 0) (some 1) true
  checkFixture "hidden-selected-negation" hidden (selected hidden [⟨1, by decide⟩, ⟨2, by decide⟩])
    1 2 1 (some 1) (some 2) true
  checkFixture "one-shared-negation" repeated (selected repeated [⟨1, by decide⟩, ⟨2, by decide⟩])
    1 2 1 (some 1) (some 2) true
  checkFixture "two-primary-inputs-rejected" twoBoundary (selected twoBoundary [⟨0, by decide⟩])
    2 1 0 none none false
  checkFixture "field-only-selected" fieldsOnly (selected fieldsOnly [⟨0, by decide⟩])
    1 1 0 (some 1) (some 1) false
  checkFixture "field-only-exterior" fieldsOnly []
    0 0 1 (some 0) (some 1) false
  checkFixture "free-input-and-constant-fields" freeFields []
    0 0 0 (some 0) (some 0) false
  checkFixture "empty-dimensions" emptyCarrier []
    0 0 0 (some 0) (some 0) false
  let support := pulled live (selected live [⟨0, by decide⟩, ⟨2, by decide⟩])
  match support.boundary with
  | [.gate gate] =>
    if gate.val != 1 then throw (IO.userError "the external boundary gate was relabelled")
  | _ => throw (IO.userError "the unary external boundary changed kind")
  if small : support.boundary.length ≤ 1 then
    let localResult := replacement live (selected live [⟨0, by decide⟩, ⟨2, by decide⟩]) small
    for port in allFin support.interface.length do
      if (support.interface.get port).val = 0 then
        if localResult.candidate.directWireWord.source port ≠ .constant true then
          throw (IO.userError "an early constant retained a cyclic dependency")
  else throw (IO.userError "the guarded external boundary was not unary")
  match (pulled primary (selected primary [⟨1, by decide⟩, ⟨2, by decide⟩])).boundary with
  | [.input index] =>
    if index.val != 2 then throw (IO.userError "a nonzero primary input was relabelled")
  | _ => throw (IO.userError "the expected primary boundary changed")
  match attempt repeated (selected repeated [⟨1, by decide⟩, ⟨2, by decide⟩]) with
  | none => throw (IO.userError "the repeated complete word was rejected")
  | some result =>
    if result.source 1 ≠ result.source 3 ∨
        result.source 1 ≠ result.implementation.candidate.directWireWord.source 1 then
      throw (IO.userError "repeated observations no longer share one physical NOT")
  for mask in List.range 8 do
    let valuation : Valuation 3 := fun index => (mask / 2 ^ index.val) % 2 == 1
    if unrealizable.implementation.candidate.program.eval valuation ⟨1, by decide⟩ != true then
      throw (IO.userError "the non-induced boundary fixture stopped being meaningful")
  IO.println "M257_COMPUTED_UNARY_ARBITRARY_SUPPORT_RUNTIME_FIXTURES_GREEN"

end PNP.DirectWire.WireUnaryArbitrarySupport.Regression
