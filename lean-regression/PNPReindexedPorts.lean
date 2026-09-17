import PNP.NANDReindexedPorts

open PNP PNP.DirectWire PNP.DirectWire.StructuralReindexing

example {inputs gates outputs profileWidth : Nat} (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (index : Fin (terminalBoundaryPorts original.program
      (backwardRecords original.program relabeling records)).length) :
    (terminalBoundaryPorts (result original relabeling).program records).get
        ((boundaryPorts original relabeling records).forward index) =
      forwardWire original.program relabeling
        ((terminalBoundaryPorts original.program
          (backwardRecords original.program relabeling records)).get index) :=
  (boundaryPorts original relabeling records).forward_get index

example {inputs gates outputs profileWidth : Nat} (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (index : Fin (terminalInterfacePorts (result original relabeling) records).length) :
    (interfacePorts original relabeling records).forward
        ((interfacePorts original relabeling records).backward index) = index :=
  (interfacePorts original relabeling records).forward_backward index

#print axioms PNP.DirectWire.StructuralReindexing.boundaryPorts
#print axioms PNP.DirectWire.StructuralReindexing.interfacePorts
#print axioms PNP.DirectWire.StructuralReindexing.selectedPorts
#print axioms PNP.DirectWire.StructuralReindexing.exteriorPorts
#print axioms PNP.DirectWire.StructuralReindexing.pull_push_boundary_valuation
#print axioms PNP.DirectWire.StructuralReindexing.push_pull_boundary_valuation
#print axioms PNP.DirectWire.StructuralReindexing.selected_gate_count
#print axioms PNP.DirectWire.StructuralReindexing.exterior_gate_count

private def exampleProgram : Program 2 3 :=
  ((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 1, .input 1⟩).snoc ⟨.gate 0, .gate 1⟩

private def original : Candidate 2 3 1 :=
  Candidate.ofDirectWireWord exampleProgram ⟨fun _ => .gate 2⟩

private def fixtures : List (String × Bool) :=
  match GateRenaming.decode 3 [(0, 1)] with
  | none => [("reordering must decode", false)]
  | some relabeling =>
      let selectedLast : List (TerminalPrimitiveRecord 2 3 1 0) := [.gate 2]
      let last := forwardRecords exampleProgram relabeling selectedLast
      let selectedPair : List (TerminalPrimitiveRecord 2 3 1 0) := [.gate 0, .gate 1, .gate 0]
      let pair := forwardRecords exampleProgram relabeling selectedPair
      let empty : List
          (TerminalPrimitiveRecord 2 (compiled exampleProgram relabeling).count 1 0) := []
      let boundary := boundaryPorts original relabeling last
      let interface := interfacePorts original relabeling pair
      let selected := selectedPorts original relabeling pair
      let exterior := exteriorPorts original relabeling last
      let oldBoundary := terminalBoundaryPorts exampleProgram
        (backwardRecords exampleProgram relabeling last)
      let newBoundary := terminalBoundaryPorts (result original relabeling).program last
      let oldValues : Valuation oldBoundary.length := fun index => index.val == 0
      let newValues := pushBoundaryValuation original relabeling last oldValues
      [("incoming ports follow the nonidentity permutation",
          decide ((allFin oldBoundary.length).map (fun index => (boundary.forward index).val) = [1, 0])),
        ("outgoing ports follow the nonidentity permutation",
          decide ((allFin (terminalInterfacePorts original
            (backwardRecords exampleProgram relabeling pair)).length).map
            (fun index => (interface.forward index).val) = [1, 0])),
        ("independent boundary values are permuted",
          decide ((allFin newBoundary.length).map newValues = [false, true])),
        ("independent boundary values round trip",
          (allFin oldBoundary.length).all (fun index =>
            decide (pullBoundaryValuation original relabeling last newValues index = oldValues index))),
        ("selected physical ownership ignores duplicate records",
          decide ((terminalSelectedGates pair).length = 2) &&
            (allFin (terminalSelectedGates pair).length).all (fun index =>
              decide (selected.forward (selected.backward index) = index))),
        ("exterior physical ownership has exact inverse indices",
          (allFin (ArbitrarySupportSplice.exterior last).length).all (fun index =>
            decide (exterior.forward (exterior.backward index) = index))),
        ("empty support has no boundary or interface",
          decide ((terminalBoundaryPorts (result original relabeling).program empty).length = 0) &&
            decide ((terminalInterfacePorts (result original relabeling) empty).length = 0))]

#eval (do
  for (name, checked) in fixtures do
    unless checked do throw (IO.userError ("reindexed-ports failure: " ++ name))
  IO.println "reindexed-ports-runtime-regressions: 7 passed"
  : IO Unit)
