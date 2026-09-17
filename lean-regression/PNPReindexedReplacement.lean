import PNP.NANDReindexedReplacement

open PNP PNP.DirectWire PNP.DirectWire.StructuralReindexing

section Generic

variable {inputs gates outputs profileWidth replacementGates : Nat}
variable (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
variable (records : List
  (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
variable (offered : Candidate
  (terminalBoundaryPorts (result original relabeling).program records).length replacementGates
  (terminalInterfacePorts (result original relabeling) records).length)

example
    (equivalent : offered.semantics =
      (extractTerminalSupport (result original relabeling) records).extractedCandidate.semantics) :
    (pullReplacement original relabeling records offered).semantics =
      (extractTerminalSupport original
        (backwardRecords original.program relabeling records)).extractedCandidate.semantics :=
  pullReplacement_compatible original relabeling records offered equivalent

example (node : Fin replacementGates) :
    (pullReplacement original relabeling records offered).program.terminalGateSources node =
      ((offered.program.terminalGateSources node).1.renameInputs
          (boundaryPorts original relabeling records).backward,
        (offered.program.terminalGateSources node).2.renameInputs
          (boundaryPorts original relabeling records).backward) :=
  pullReplacement_gate_sources original relabeling records offered node

example (smaller : offered.toImplementation.gateCount <
      (extractTerminalSupport (result original relabeling) records).gateCount) :
    (pullReplacement original relabeling records offered).toImplementation.gateCount <
      (extractTerminalSupport original
        (backwardRecords original.program relabeling records)).gateCount :=
  strict_gain_pullback original relabeling records offered smaller

end Generic

#print axioms PNP.DirectWire.StructuralReindexing.renameInputs_gateSources
#print axioms PNP.DirectWire.StructuralReindexing.pullReplacement_gate_sources
#print axioms PNP.DirectWire.StructuralReindexing.pullReplacement_output_source
#print axioms PNP.DirectWire.StructuralReindexing.pullReplacement_semantics
#print axioms PNP.DirectWire.StructuralReindexing.pullReplacement_compatible
#print axioms PNP.DirectWire.StructuralReindexing.support_surcharge_zero
#print axioms PNP.DirectWire.StructuralReindexing.replacement_surcharge_zero
#print axioms PNP.DirectWire.StructuralReindexing.matched_surcharge
#print axioms PNP.DirectWire.StructuralReindexing.replacement_saving_preserved
#print axioms PNP.DirectWire.StructuralReindexing.strict_gain_pullback

-- Two proper double-negation paths. Their predecessors remain in the exterior.
-- Swapping both paths changes both canonical boundary and interface orders.
private def exampleProgram : Program 2 6 :=
  (((((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 1, .input 1⟩).snoc ⟨.gate 0, .gate 0⟩).snoc
      ⟨.gate 1, .gate 1⟩).snoc ⟨.gate 2, .gate 2⟩).snoc ⟨.gate 3, .gate 3⟩

private def original : Candidate 2 6 2 :=
  Candidate.ofDirectWireWord exampleProgram
    ⟨fun output => if output.val = 0 then .gate 4 else .gate 5⟩

private def fixtures : List (String × Bool) :=
  match GateRenaming.decode 6 [(0, 1), (2, 3), (4, 5)] with
  | none => [("reordering must decode", false)]
  | some relabeling =>
      let oldRecords : List (TerminalPrimitiveRecord 2 6 2 0) :=
        [.gate 2, .gate 3, .gate 4, .gate 5, .gate 2]
      let records := forwardRecords exampleProgram relabeling oldRecords
      let changed := result original relabeling
      let predecessor := backwardRecords exampleProgram relabeling records
      let oldBoundary := terminalBoundaryPorts exampleProgram predecessor
      let newBoundary := terminalBoundaryPorts changed.program records
      let oldInterface := terminalInterfacePorts original predecessor
      let newInterface := terminalInterfacePorts changed records
      if twoInputs : newBoundary.length = 2 then
        if twoOutputs : newInterface.length = 2 then
          let oldOutputWidth : oldInterface.length = 2 :=
            (interfacePorts original relabeling records).width_eq.trans twoOutputs
          let offered : Candidate newBoundary.length 0 newInterface.length :=
            Candidate.ofDirectWireWord .empty
              ⟨fun output => .input ⟨output.val, by omega⟩⟩
          let pulled := pullReplacement original relabeling records offered
          let identityInput : Valuation oldBoundary.length := fun index => index.val == 0
          let pushed := pushBoundaryValuation original relabeling records identityInput
          let allValues := [false, true].all (fun left => [false, true].all (fun right =>
            let values : Valuation oldBoundary.length :=
              fun index => if index.val = 0 then left else right
            (allFin oldInterface.length).all (fun output =>
              decide (pulled.semantics values output =
                terminalOpenSupportSemantics original predecessor values output))))
          let compatible := [false, true].all (fun left => [false, true].all (fun right =>
            let values : Valuation newBoundary.length :=
              fun index => if index.val = 0 then left else right
            (allFin newInterface.length).all (fun output =>
              decide (offered.semantics values output =
                terminalOpenSupportSemantics changed records values output))))
          let extracted := (extractTerminalSupport changed records).extractedCandidate
          let pulledExtracted := pullReplacement original relabeling records extracted
          [("proper support and both port widths are nonvacuous",
              decide (oldBoundary.length = 2) && decide (oldInterface.length = 2) &&
              decide ((extractTerminalSupport original predecessor).gateCount = 4) &&
              decide ((ArbitrarySupportSplice.exterior predecessor).length = 2)),
            ("boundary order really changes",
              (allFin oldBoundary.length).any (fun index =>
                ((boundaryPorts original relabeling records).forward index).val != index.val)),
            ("interface order really changes",
              (allFin oldInterface.length).any (fun index =>
                ((interfacePorts original relabeling records).forward index).val != index.val)),
            ("zero-gate offered replacement is compatible for all four inputs", compatible),
            ("pulled replacement is compatible for all four independent inputs", allValues),
            ("no gates added and strict four-gate saving preserved",
              decide (pulled.toImplementation.gateCount = 0) &&
              decide (pulled.toImplementation.gateCount <
                (extractTerminalSupport original predecessor).gateCount)),
            ("omitting input rewiring changes ordered behaviour",
              (allFin oldInterface.length).any (fun output =>
                offered.semantics (fun index => index.val == 0)
                  ((interfacePorts original relabeling records).forward output) !=
                    pulled.semantics identityInput output)),
            ("omitting output rewiring changes ordered behaviour",
              (allFin oldInterface.length).any (fun output =>
                offered.semantics pushed ⟨output.val, by omega⟩ !=
                  pulled.semantics identityInput output)),
            ("nonempty extracted replacement keeps its exact gate count",
              decide (extracted.toImplementation.gateCount = 4) &&
              decide (pulledExtracted.toImplementation.gateCount = 4)),
            ("nonempty replacement retains every exact gate-source pair",
              (allFin extracted.toImplementation.gateCount).all (fun node =>
                decide (pulledExtracted.program.terminalGateSources node =
                  ((extracted.program.terminalGateSources node).1.renameInputs
                      (boundaryPorts original relabeling records).backward,
                    (extracted.program.terminalGateSources node).2.renameInputs
                      (boundaryPorts original relabeling records).backward))))]
        else [("descendant interface width must be two", false)]
      else [("descendant boundary width must be two", false)]

#eval (do
  for (name, checked) in fixtures do
    unless checked do throw (IO.userError ("reindexed-replacement failure: " ++ name))
  IO.println "reindexed-replacement-runtime-regressions: 10 passed"
  : IO Unit)
