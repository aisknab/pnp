import PNP.NANDReindexedSupport

open PNP PNP.DirectWire PNP.DirectWire.StructuralReindexing

-- Arbitrary-dimension and arbitrary-descendant-support theorem contracts.
example {inputs gates outputs profileWidth : Nat} (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (wire : TerminalSupportWire inputs (compiled original.program relabeling).count) :
    wire ∈ terminalBoundaryPorts (result original relabeling).program records ↔
      backwardWire original.program relabeling wire ∈
        terminalBoundaryPorts original.program (backwardRecords original.program relabeling records) :=
  descendant_boundary original relabeling records wire

example {inputs gates outputs profileWidth : Nat} (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (producer : Fin (compiled original.program relabeling).count) :
    producer ∈ terminalInterfacePorts (result original relabeling) records ↔
      backwardGate original.program relabeling producer ∈
        terminalInterfacePorts original (backwardRecords original.program relabeling records) :=
  descendant_interface original relabeling records producer

#print axioms PNP.DirectWire.StructuralReindexing.backward_forward_records
#print axioms PNP.DirectWire.StructuralReindexing.forward_backward_records
#print axioms PNP.DirectWire.StructuralReindexing.uses_forward
#print axioms PNP.DirectWire.StructuralReindexing.descendant_boundary
#print axioms PNP.DirectWire.StructuralReindexing.descendant_interface

private def exampleProgram : Program 2 3 :=
  ((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 1, .input 1⟩).snoc ⟨.gate 0, .gate 1⟩

private def original : Candidate 2 3 3 :=
  Candidate.ofDirectWireWord exampleProgram
    ⟨fun output => if output.val = 1 then .input 0 else .gate 2⟩

private def checkSupport
    (relabeling : GateRenaming 3) (records : List (TerminalPrimitiveRecord 2 3 3 1)) : Bool :=
  let changed := result original relabeling
  let mapped := forwardRecords exampleProgram relabeling records
  decide (backwardRecords exampleProgram relabeling mapped = records) &&
    (allFin 3).all (fun node =>
      decide (terminalGateSelected mapped (forwardGate exampleProgram relabeling node) =
        terminalGateSelected records node) &&
      decide (terminalInterfaceGate changed mapped (forwardGate exampleProgram relabeling node) =
        terminalInterfaceGate original records node)) &&
    (allTerminalSupportWires 2 3).all (fun wire =>
      decide (terminalBoundaryWire changed.program mapped (forwardWire exampleProgram relabeling wire) =
        terminalBoundaryWire exampleProgram records wire))

private def supportFixtures : List (String × Bool) :=
  match GateRenaming.decode 3 [(0, 1)] with
  | none => [("reordering must decode", false)]
  | some relabeling =>
      let empty : List (TerminalPrimitiveRecord 2 3 3 1) := []
      let duplicate : List (TerminalPrimitiveRecord 2 3 3 1) :=
        [.gate 0, .boundary 1, .gate 0, .interface 2, .profile 0]
      let full : List (TerminalPrimitiveRecord 2 3 3 1) := [.gate 0, .gate 1, .gate 2]
      let last : List (TerminalPrimitiveRecord 2 3 3 1) := [.gate 2]
      let changed := result original relabeling
      let actualBoundary := terminalBoundaryPorts changed.program
        (forwardRecords exampleProgram relabeling last)
      let mappedBoundary := (terminalBoundaryPorts exampleProgram last).map
        (forwardWire exampleProgram relabeling)
      let descendant : List
          (TerminalPrimitiveRecord 2 (compiled exampleProgram relabeling).count 3 1) :=
        (allFin (compiled exampleProgram relabeling).count).reverse.map TerminalPrimitiveRecord.gate
      [("empty support", checkSupport relabeling empty),
        ("duplicate records and non-gate labels", checkSupport relabeling duplicate),
        ("full support", checkSupport relabeling full),
        ("outgoing global output with repeated output positions", checkSupport relabeling last),
        ("nonidentity canonical boundary order",
          decide (actualBoundary.map TerminalSupportWire.orderCode = [2, 3]) &&
            decide (mappedBoundary.map TerminalSupportWire.orderCode = [3, 2])),
        ("arbitrary descendant list round trip",
          decide (forwardRecords exampleProgram relabeling
            (backwardRecords exampleProgram relabeling descendant) = descendant)),
        ("both carrier constants stay off the incoming boundary",
          decide ((sourceMap (forwardGate exampleProgram relabeling)
            (Source.constant false : Source 2 3)).terminalSupportWire? = none) &&
          decide ((sourceMap (forwardGate exampleProgram relabeling)
            (Source.constant true : Source 2 3)).terminalSupportWire? = none))]

#eval (do
  for (name, checked) in supportFixtures do
    unless checked do throw (IO.userError ("reindexed-support failure: " ++ name))
  IO.println "reindexed-support-runtime-regressions: 7 passed"
  : IO Unit)
