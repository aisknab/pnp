import PNP.NANDReindexedSplice

open PNP PNP.DirectWire PNP.DirectWire.StructuralReindexing

section Generic

variable {inputs gates outputs profileWidth replacementGates : Nat}
variable (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
variable (records : List
  (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
variable (offered : Candidate
  (terminalBoundaryPorts (result original relabeling).program records).length replacementGates
  (terminalInterfacePorts (result original relabeling) records).length)

example :
    ArbitrarySupportSplice.compile original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) = none ↔
    ArbitrarySupportSplice.compile (result original relabeling) records offered = none :=
  splice_compile_failure_iff original relabeling records offered

example (producer consumer : Fin ((ArbitrarySupportSplice.exterior
      (backwardRecords original.program relabeling records)).length + replacementGates)) :
    (ArbitrarySupportSplice.graph original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered)).Depends producer consumer ↔
    (ArbitrarySupportSplice.graph (result original relabeling) records offered).Depends
      (spliceForward original relabeling records producer)
      (spliceForward original relabeling records consumer) :=
  splice_dependencies original relabeling records offered producer consumer

example (output : Fin outputs) :
    (ArbitrarySupportSplice.word (result original relabeling) records offered).source output =
      sourceMap (spliceForward original relabeling records)
        ((ArbitrarySupportSplice.word original
          (backwardRecords original.program relabeling records)
          (pullReplacement original relabeling records offered)).source output) :=
  splice_output_source original relabeling records offered output

end Generic

#print axioms PNP.DirectWire.StructuralReindexing.splice_backward_forward
#print axioms PNP.DirectWire.StructuralReindexing.splice_forward_backward
#print axioms PNP.DirectWire.StructuralReindexing.splice_boundarySource_forward
#print axioms PNP.DirectWire.StructuralReindexing.splice_replacementSource_forward
#print axioms PNP.DirectWire.StructuralReindexing.splice_sources
#print axioms PNP.DirectWire.StructuralReindexing.splice_output_source
#print axioms PNP.DirectWire.StructuralReindexing.splice_dependencies
#print axioms PNP.DirectWire.StructuralReindexing.splice_wellFounded_iff
#print axioms PNP.DirectWire.StructuralReindexing.splice_compile_success_iff
#print axioms PNP.DirectWire.StructuralReindexing.splice_compile_failure_iff

-- Finite execution checks below do not establish the generic theorems above.
private def checkRaw {inputs gates outputs profileWidth replacementGates : Nat}
    (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (offered : Candidate
      (terminalBoundaryPorts (result original relabeling).program records).length replacementGates
      (terminalInterfacePorts (result original relabeling) records).length) : Bool :=
  let predecessor := backwardRecords original.program relabeling records
  let pulled := pullReplacement original relabeling records offered
  let before := ArbitrarySupportSplice.graph original predecessor pulled
  let after := ArbitrarySupportSplice.graph (result original relabeling) records offered
  let oldNodes := (ArbitrarySupportSplice.exterior predecessor).length + replacementGates
  let newNodes := (ArbitrarySupportSplice.exterior records).length + replacementGates
  (allFin oldNodes).all (fun node =>
    decide (spliceBackward original relabeling records
      (spliceForward original relabeling records node) = node) &&
    decide ((after.gate (spliceForward original relabeling records node)).left =
      sourceMap (spliceForward original relabeling records) (before.gate node).left) &&
    decide ((after.gate (spliceForward original relabeling records node)).right =
      sourceMap (spliceForward original relabeling records) (before.gate node).right) &&
    (allFin oldNodes).all (fun producer =>
      @decide (before.Depends producer node ↔
        after.Depends (spliceForward original relabeling records producer)
          (spliceForward original relabeling records node))
        (by unfold RawNandGraph.Depends; infer_instance))) &&
  (allFin newNodes).all (fun node =>
    decide (spliceForward original relabeling records
      (spliceBackward original relabeling records node) = node)) &&
  (allFin outputs).all (fun output =>
    decide ((ArbitrarySupportSplice.word (result original relabeling) records offered).source output =
      sourceMap (spliceForward original relabeling records)
        ((ArbitrarySupportSplice.word original predecessor pulled).source output))) &&
  decide ((ArbitrarySupportSplice.compile original predecessor pulled).isSome =
    (ArbitrarySupportSplice.compile (result original relabeling) records offered).isSome)

private def exampleProgram : Program 2 6 :=
  (((((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 1, .input 1⟩).snoc ⟨.gate 0, .gate 0⟩).snoc
      ⟨.gate 1, .gate 1⟩).snoc ⟨.gate 2, .gate 2⟩).snoc ⟨.gate 3, .gate 3⟩

private def original : Candidate 2 6 2 :=
  Candidate.ofDirectWireWord exampleProgram
    ⟨fun output => if output.val = 0 then .gate 4 else .gate 5⟩

private def acceptedFixtures : List (String × Bool) :=
  match GateRenaming.decode 6 [(0, 1), (2, 3), (4, 5)] with
  | none => [("reordering must decode", false)]
  | some relabeling =>
      let oldRecords : List (TerminalPrimitiveRecord 2 6 2 0) :=
        [.gate 2, .gate 3, .gate 4, .gate 5, .gate 2]
      let records := forwardRecords exampleProgram relabeling oldRecords
      let changed := result original relabeling
      let boundary := terminalBoundaryPorts changed.program records
      let interface := terminalInterfacePorts changed records
      if twoInputs : boundary.length = 2 then
        if twoOutputs : interface.length = 2 then
          let offered : Candidate boundary.length 0 interface.length :=
            Candidate.ofDirectWireWord .empty
              ⟨fun output => .input ⟨output.val, by omega⟩⟩
          let extracted := (extractTerminalSupport changed records).extractedCandidate
          let constants : Candidate boundary.length 0 interface.length :=
            Candidate.ofDirectWireWord .empty ⟨fun output => .constant (output.val == 0)⟩
          let predecessor := backwardRecords exampleProgram relabeling records
          [("proper support and retained exterior are nonempty",
              decide ((extractTerminalSupport original predecessor).gateCount = 4) &&
              decide ((ArbitrarySupportSplice.exterior predecessor).length = 2)),
            ("exterior correspondence is genuinely nonidentity",
              (allFin (ArbitrarySupportSplice.exterior predecessor).length).any (fun index =>
                ((exteriorPorts original relabeling records).forward index).val != index.val)),
            ("zero-gate replacement preserves all nodes, wires, edges and outputs",
              checkRaw original relabeling records offered),
            ("nonempty replacement preserves exterior and replacement ownership",
              decide (extracted.toImplementation.gateCount = 4) &&
              checkRaw original relabeling records extracted),
            ("ordered constant outputs preserve their exact literal references",
              checkRaw original relabeling records constants),
            ("both actual nonempty replacement splices compile",
              (ArbitrarySupportSplice.compile changed records extracted).isSome &&
              (ArbitrarySupportSplice.compile original predecessor
                (pullReplacement original relabeling records extracted)).isSome)]
        else [("descendant interface must have two outputs", false)]
      else [("descendant boundary must have two inputs", false)]

private def chain : Candidate 1 3 1 :=
  Candidate.ofDirectWireWord
    (((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc
      ⟨.gate 0, .gate 0⟩).snoc ⟨.gate 1, .gate 1⟩)
    ⟨fun _ => .gate 2⟩

private def rejectedFixtures : List (String × Bool) :=
  match GateRenaming.decode 3 [(0, 2)] with
  | none => [("cyclic-case reordering must decode", false)]
  | some relabeling =>
      let oldRecords : List (TerminalPrimitiveRecord 1 3 1 0) := [.gate 0, .gate 2]
      let records := forwardRecords chain.program relabeling oldRecords
      let changed := result chain relabeling
      let boundary := terminalBoundaryPorts changed.program records
      let interface := terminalInterfacePorts changed records
      if twoInputs : boundary.length = 2 then
        let offered : Candidate boundary.length 0 interface.length :=
          Candidate.ofDirectWireWord .empty ⟨fun _ => .input ⟨1, by omega⟩⟩
        let predecessor := backwardRecords chain.program relabeling records
        [("nonconvex cyclic case has the intended nonvacuous interface",
            decide (interface.length = 2) &&
            decide ((ArbitrarySupportSplice.exterior predecessor).length = 1)),
          ("cyclic raw replacement still has exact node, edge and output correspondence",
            checkRaw chain relabeling records offered),
          ("both actual compilers reject the raw cycle",
            !(ArbitrarySupportSplice.compile changed records offered).isSome &&
            !(ArbitrarySupportSplice.compile chain predecessor
              (pullReplacement chain relabeling records offered)).isSome)]
      else [("cyclic case must have two boundary inputs", false)]

#eval (do
  for (name, checked) in acceptedFixtures ++ rejectedFixtures do
    unless checked do throw (IO.userError ("reindexed-splice failure: " ++ name))
  IO.println "reindexed-splice-runtime-regressions: 9 passed"
  : IO Unit)
