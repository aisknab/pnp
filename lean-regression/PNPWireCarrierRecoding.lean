import PNP.NANDWireCarrierRecoding

namespace PNP.DirectWire.WireCarrierRecoding.Regression

def identity (width : Nat) : Implementation width width :=
  (Candidate.ofDirectWireWord (.empty : Program width 0)
    ⟨fun field => .input field⟩).toImplementation

def negation : Implementation 1 1 :=
  (Candidate.ofDirectWireWord
    ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
    ⟨fun _ => .gate 0⟩).toImplementation

def badConstant : Implementation 1 1 :=
  (Candidate.ofDirectWireWord (.empty : Program 1 0)
    (⟨fun _ => .constant false⟩ : DirectWireWord 1 0 1)).toImplementation

def swap : Implementation 2 2 :=
  (Candidate.ofDirectWireWord (.empty : Program 2 0)
    (⟨fun field => if field.val = 0 then .input 1 else .input 0⟩ :
      DirectWireWord 2 0 2)).toImplementation

/-- A genuinely interacting reversible map: (a,b) maps to (a,a xor b). -/
def controlledNot : Implementation 2 2 :=
  (Candidate.ofDirectWireWord
    (.snoc
      (.snoc
        (.snoc
          (.snoc (.empty : Program 2 0) ⟨.input 0, .input 1⟩)
          ⟨.input 0, .gate 0⟩)
        ⟨.input 1, .gate 0⟩)
      ⟨.gate 1, .gate 2⟩)
    (⟨fun field => if field.val = 0 then .input 0 else .gate 3⟩ :
      DirectWireWord 2 4 2)).toImplementation

def empty : WireCarrier 0 0 0 :=
  { implementation := (Candidate.ofDirectWireWord (.empty : Program 0 0)
      (⟨Fin.elim0⟩ : DirectWireWord 0 0 0)).toImplementation
    source := Fin.elim0 }

def unary : WireCarrier 1 1 1 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 1 0).snoc ⟨.input 0, .input 0⟩)
      (⟨fun _ => .input 0⟩ : DirectWireWord 1 1 1)).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

def hidden : WireCarrier 2 1 2 :=
  { implementation := (Candidate.ofDirectWireWord
      ((.empty : Program 2 0).snoc ⟨.input 0, .input 1⟩)
      (⟨fun _ => .constant false⟩ : DirectWireWord 2 1 1)).toImplementation
    source := fun field => if field.val = 0 then .input 0 else .gate ⟨0, by decide⟩ }

def repeated : WireCarrier 2 1 2 :=
  { implementation := hidden.implementation
    source := fun _ => .gate ⟨0, by decide⟩ }

example {fields : Nat} (encoder decoder : Implementation fields fields) :
    check encoder decoder = true ↔
      (∀ valuation field, decoder.candidate.semantics
        (encoder.candidate.semantics valuation) field = valuation field) ∧
      (∀ valuation field, encoder.candidate.semantics
        (decoder.candidate.semantics valuation) field = valuation field) :=
  check_iff encoder decoder

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) (checked : Checked encoder decoder)
    (valuation : Valuation inputs) (field : Fin fields) :
    (result carrier encoder decoder).fieldValue valuation field =
      carrier.fieldValue valuation field :=
  result_field carrier encoder decoder checked valuation field

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (result carrier encoder decoder).implementation.candidate.semantics valuation output =
      carrier.implementation.candidate.semantics valuation output :=
  result_output carrier encoder decoder valuation output

example {inputs outputs fields : Nat} (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) :
    (result carrier encoder decoder).implementation.gateCount +
        removed carrier encoder decoder =
      carrier.implementation.gateCount + encoder.gateCount + decoder.gateCount :=
  result_gate_balance carrier encoder decoder

#print axioms PNP.DirectWire.WireCarrierRecoding.check_iff
#print axioms PNP.DirectWire.WireCarrierRecoding.compile_success_iff
#print axioms PNP.DirectWire.WireCarrierRecoding.appendMap_field
#print axioms PNP.DirectWire.WireCarrierRecoding.result_output
#print axioms PNP.DirectWire.WireCarrierRecoding.result_field
#print axioms PNP.DirectWire.WireCarrierRecoding.result_gate_balance

/-- Bounded execution checks supplement, but never replace, the general proofs. -/
def assertRoundTrip {inputs outputs fields : Nat}
    (carrier : WireCarrier inputs outputs fields)
    (encoder decoder : Implementation fields fields) : IO Unit := do
  if !(check encoder decoder) || !(compile encoder decoder).isSome then
    throw (IO.userError "valid two-way recoding rejected")
  let transformed := result carrier encoder decoder
  if transformed.implementation.gateCount + removed carrier encoder decoder !=
      carrier.implementation.gateCount + encoder.gateCount + decoder.gateCount then
    throw (IO.userError "physical recoding gate balance is not exact")
  for tuple in allBoolTuples inputs do
    for output in allFin outputs do
      if transformed.implementation.candidate.semantics tuple.toValuation output !=
          carrier.implementation.candidate.semantics tuple.toValuation output then
        throw (IO.userError "recoding changed an ordinary output")
    for field in allFin fields do
      if transformed.fieldValue tuple.toValuation field !=
          carrier.fieldValue tuple.toValuation field then
        throw (IO.userError "recoding changed a required computational field")

#eval show IO Unit from do
  assertRoundTrip empty (identity 0) (identity 0)
  assertRoundTrip unary (identity 1) (identity 1)
  assertRoundTrip unary negation negation
  assertRoundTrip hidden swap swap
  assertRoundTrip hidden controlledNot controlledNot
  assertRoundTrip repeated controlledNot controlledNot
  if check negation (identity 1) || (compile negation (identity 1)).isSome then
    throw (IO.userError "a wrong inverse was accepted")
  if check badConstant (identity 1) || (compile badConstant (identity 1)).isSome then
    throw (IO.userError "information loss was accepted as recoding")
  if check (identity 1) badConstant || (compile (identity 1) badConstant).isSome then
    throw (IO.userError "a decoder that discards an input was accepted")
  if controlledNot.gateCount != 4 || negation.gateCount != 1 then
    throw (IO.userError "fixture does not contain its intended physical gates")
  IO.println "CARRIER_RECODING_RUNTIME_PASSED"

end PNP.DirectWire.WireCarrierRecoding.Regression
