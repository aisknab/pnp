import PNP.NANDReindexedOpenSemantics

open PNP PNP.DirectWire PNP.DirectWire.StructuralReindexing

example {inputs gates outputs profileWidth : Nat} (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (valuation :
      Valuation (terminalBoundaryPorts (result original relabeling).program records).length)
    (output : Fin (terminalInterfacePorts (result original relabeling) records).length) :
    terminalOpenSupportSemantics original (backwardRecords original.program relabeling records)
        (pullBoundaryValuation original relabeling records valuation)
        ((interfacePorts original relabeling records).backward output) =
      terminalOpenSupportSemantics (result original relabeling) records valuation output :=
  open_support_pullback original relabeling records valuation output

#print axioms PNP.DirectWire.StructuralReindexing.external_wire_value_preserved
#print axioms PNP.DirectWire.StructuralReindexing.open_gate_preserved
#print axioms PNP.DirectWire.StructuralReindexing.open_support_preserved
#print axioms PNP.DirectWire.StructuralReindexing.open_support_pullback
#print axioms PNP.DirectWire.StructuralReindexing.extracted_support_preserved

-- The whole circuit always returns true; the proper open support computes
-- a nonconstant function of two independent, not necessarily induced, inputs.
private def exampleProgram : Program 1 4 :=
  (((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 0, .input 0⟩).snoc ⟨.gate 0, .gate 0⟩).snoc ⟨.gate 2, .gate 1⟩

private def original : Candidate 1 4 1 :=
  Candidate.ofDirectWireWord exampleProgram ⟨fun _ => .gate 3⟩

private def fixtures : List (String × Bool) :=
  match GateRenaming.decode 4 [(0, 1)] with
  | none => [("reordering must decode", false)]
  | some relabeling =>
      let oldRecords : List (TerminalPrimitiveRecord 1 4 1 0) := [.gate 2, .gate 3]
      let records := forwardRecords exampleProgram relabeling oldRecords
      let predecessor := backwardRecords exampleProgram relabeling records
      let oldBoundary := terminalBoundaryPorts exampleProgram predecessor
      let changed := result original relabeling
      let newBoundary := terminalBoundaryPorts changed.program records
      let oldInterface := terminalInterfacePorts original predecessor
      let newInterface := terminalInterfacePorts changed records
      let oldValues : Valuation oldBoundary.length := fun index => index.val == 1
      let changedValues := pushBoundaryValuation original relabeling records oldValues
      let allInputs := [false, true].all (fun left => [false, true].all (fun right =>
        let values : Valuation oldBoundary.length := fun index => if index.val = 0 then left else right
        let pushed := pushBoundaryValuation original relabeling records values
        (allFin oldInterface.length).all (fun output =>
          decide (terminalOpenSupportSemantics changed records pushed
              ((interfacePorts original relabeling records).forward output) =
            terminalOpenSupportSemantics original predecessor values output))))
      [("proper support has two independent boundary inputs",
          decide (oldBoundary.length = 2) && decide (newBoundary.length = 2) &&
            decide (oldInterface.length = 1) && decide (newInterface.length = 1)),
        ("whole circuit outputs are true for both original inputs",
          [false, true].all (fun value => original.semantics (fun _ => value) 0)),
        ("non-induced open input has a different result",
          (allFin oldInterface.length).all (fun output =>
            !(terminalOpenSupportSemantics original predecessor oldValues output))),
        ("correct input permutation preserves that result",
          (allFin newInterface.length).all (fun output =>
            !(terminalOpenSupportSemantics changed records changedValues output))),
        ("omitting the input permutation changes the result",
          (allFin newInterface.length).all (fun output =>
            terminalOpenSupportSemantics changed records (fun index => index.val == 1) output)),
        ("all four independent valuations preserve ordered semantics", allInputs),
        ("actual extracted candidate realizes the same non-induced result",
          (allFin newInterface.length).all (fun output =>
            !((extractTerminalSupport changed records).extractedCandidate.semantics
              changedValues output)))]

#eval (do
  for (name, checked) in fixtures do
    unless checked do throw (IO.userError ("reindexed-open-semantics failure: " ++ name))
  IO.println "reindexed-open-semantics-runtime-regressions: 7 passed"
  : IO Unit)
