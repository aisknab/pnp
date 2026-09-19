import PNP

namespace PNP.DirectWire.WireProfileFieldClosedRegression

open WireProfileAmbient

/- Contracts quantify over all dimensions and contain no supplied semantic
   observer, correctness certificate, selected family, or completeness premise. -/
example {inputs gates outputs fields : Nat} (candidate : Candidate inputs gates outputs)
    (selectedRecords : List (TerminalPrimitiveRecord inputs gates outputs fields))
    (boundary : Valuation (terminalBoundaryPorts candidate.program selectedRecords).length)
    (gate : Fin gates) (selected : terminalGateSelected selectedRecords gate = true) :
    (extractTerminalSupport candidate selectedRecords).extractedCandidate.program.eval boundary
      (terminalExtractionGateIndex candidate selectedRecords gate selected) =
        terminalOpenGateEvaluation candidate selectedRecords boundary gate :=
  extractTerminalSupport_gate_evaluation candidate selectedRecords boundary gate selected

example {inputs gates outputs fields : Nat} (candidate : Candidate inputs gates outputs)
    (selectedRecords : List (TerminalPrimitiveRecord inputs gates outputs fields))
    (input : Valuation inputs) (gate : Fin gates)
    (selected : terminalGateSelected selectedRecords gate = true) :
    (extractTerminalSupport candidate selectedRecords).extractedCandidate.program.eval
      (terminalInducedBoundaryValuation candidate selectedRecords input)
      (terminalExtractionGateIndex candidate selectedRecords gate selected) =
        candidate.program.eval input gate :=
  extractTerminalSupport_gate_induced candidate selectedRecords input gate selected

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (wire : TerminalSupportWire inputs target.implementation.gateCount)
    (member : wire ∈ (extractTerminalSupport target.implementation.candidate
      (WireProfileFieldClosed.records target keep seed)).boundary) :
    ∃ input : Fin inputs, wire = .input input :=
  WireProfileFieldClosed.boundary_isInput target keep seed wire member

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (gate : Fin target.implementation.gateCount)
    (selected : terminalGateSelected (WireProfileFieldClosed.records target keep seed) gate = true)
    (valuation : Valuation (inputs + target.implementation.gateCount)) :
    (WireProfileFieldClosed.implementation target keep seed).candidate.program.eval valuation
      (terminalExtractionGateIndex target.implementation.candidate
        (WireProfileFieldClosed.records target keep seed) gate selected) =
          target.implementation.candidate.program.eval
            (fun index => valuation (Fin.castAdd target.implementation.gateCount index)) gate :=
  WireProfileFieldClosed.gate_value target keep seed gate selected valuation

example {inputs outputs fields : Nat} (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool)
    (seed : List (TerminalPrimitiveRecord inputs target.implementation.gateCount outputs fields))
    (field : Fin fields) :
    (model target keep).observe (WireProfileFieldClosed.implementation target keep seed) field = true :=
  WireProfileFieldClosed.available target keep seed field

private def bit : Fin 1 := ⟨0, by decide⟩

private def negProgram : Program 1 1 := .snoc .empty ⟨.input bit, .input bit⟩

private def hidden : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord negProgram ⟨fun _ => .input bit⟩).toImplementation
    source := fun _ => .gate bit }

theorem hidden_field_recovered_for_every_ambient_input :
    (model hidden (fun _ => true)).observe
      (WireProfileFieldClosed.implementation hidden (fun _ => true) []) bit = true :=
  WireProfileFieldClosed.available hidden (fun _ => true) [] bit

theorem hidden_gate_not_an_ordinary_output :
    (extractTerminalSupport hidden.implementation.candidate
      (WireProfileFieldClosed.records hidden (fun _ => true) [])).interface = [] := by decide +kernel

private def withIrrelevant : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (.snoc negProgram ⟨.constant true, .constant true⟩)
        ⟨fun _ => .input bit⟩).toImplementation
    source := fun _ => .gate ⟨0, by decide⟩ }

private def doubleNeg : WireCarrier 1 1 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord
        (.snoc negProgram ⟨.gate bit, .gate bit⟩)
        ⟨fun _ => .input bit⟩).toImplementation
    source := fun _ => .gate ⟨1, by decide⟩ }

private def emptyOffered : Implementation 1 1 :=
  (Candidate.ofDirectWireWord (.empty : Program 1 0)
    ⟨fun _ => .input bit⟩).toImplementation

private def inputField : WireCarrier 1 1 1 :=
  { implementation := hidden.implementation
    source := fun _ => .input bit }

private def repeated : WireCarrier 1 1 2 :=
  { implementation := hidden.implementation
    source := fun _ => .gate bit }

private def noInputsConstant : WireCarrier 0 0 1 :=
  { implementation :=
      (Candidate.ofDirectWireWord (.empty : Program 0 0) ⟨Fin.elim0⟩).toImplementation
    source := fun _ => .constant true }

private def noFields : WireCarrier 0 0 0 :=
  { implementation := noInputsConstant.implementation
    source := Fin.elim0 }

private def checks : List (String × Bool) :=
  [ ("hidden field from internal gate",
      (model hidden (fun _ => true)).observe
        (WireProfileFieldClosed.implementation hidden (fun _ => true) []) bit)
  , ("hidden field needs no ordinary interface output",
      (extractTerminalSupport hidden.implementation.candidate
        (WireProfileFieldClosed.records hidden (fun _ => true) [])).interface.isEmpty)
  , ("irrelevant gate is not forced into support",
      decide ((WireProfileFieldClosed.implementation withIrrelevant (fun _ => true) []).gateCount = 1))
  , ("physical predecessors are derived",
      terminalGateSelected (WireProfileFieldClosed.records doubleNeg (fun _ => true) [])
        ⟨0, by decide⟩ &&
      terminalGateSelected (WireProfileFieldClosed.records doubleNeg (fun _ => true) [])
        ⟨1, by decide⟩)
  , ("constructed support is not claimed minimum",
      decide ((WireProfileFieldClosed.implementation doubleNeg (fun _ => true) []).gateCount = 2) &&
        WireProfileAvailability.available doubleNeg emptyOffered bit)
  , ("primary-input field needs no gate",
      decide ((WireProfileFieldClosed.implementation inputField (fun _ => false) []).gateCount = 0) &&
        (model inputField (fun _ => false)).observe
          (WireProfileFieldClosed.implementation inputField (fun _ => false) []) bit)
  , ("repeated fields share one physical gate",
      decide ((WireProfileFieldClosed.implementation repeated (fun _ => true) []).gateCount = 1) &&
        allTrue (allFin 2) ((model repeated (fun _ => true)).observe
          (WireProfileFieldClosed.implementation repeated (fun _ => true) [])))
  , ("zero-input constant", (model noInputsConstant (fun _ => true)).observe
      (WireProfileFieldClosed.implementation noInputsConstant (fun _ => true) []) bit)
  , ("empty dimensions", decide
      ((WireProfileFieldClosed.implementation noFields Fin.elim0 []).gateCount = 0))
  , ("extra seed retained without an optimality claim", decide
      ((WireProfileFieldClosed.implementation withIrrelevant (fun _ => true)
        [.gate ⟨1, by decide⟩]).gateCount = 2))
  ]

def run : IO Unit := do
  for (name, passed) in checks do
    if passed then
      IO.println ("field-closed-check-passed: " ++ name)
    else
      throw (IO.userError ("field-closed-check-failed: " ++ name))
  IO.println "field-closed-regressions-complete: 10 runtime checks; 5 general type contracts; 2 kernel guards"

end PNP.DirectWire.WireProfileFieldClosedRegression

#print axioms PNP.DirectWire.WireProfileFieldClosedRegression.hidden_field_recovered_for_every_ambient_input
#print axioms PNP.DirectWire.WireProfileFieldClosedRegression.hidden_gate_not_an_ordinary_output

def main : IO Unit := PNP.DirectWire.WireProfileFieldClosedRegression.run
