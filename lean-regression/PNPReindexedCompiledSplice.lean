import PNP.NANDReindexedCompiledSplice

open PNP PNP.DirectWire PNP.DirectWire.StructuralReindexing

section Generic

variable {inputs gates outputs profileWidth replacementGates : Nat}
variable (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
variable (records : List
  (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
variable (offered : Candidate
  (terminalBoundaryPorts (result original relabeling).program records).length replacementGates
  (terminalInterfacePorts (result original relabeling) records).length)

variable (before : CompiledRawNandGraph
  (ArbitrarySupportSplice.graph original
    (backwardRecords original.program relabeling records)
    (pullReplacement original relabeling records offered)))
variable (after : CompiledRawNandGraph
  (ArbitrarySupportSplice.graph (result original relabeling) records offered))

example (position : Fin before.count) :
    splicePhysicalBackward original relabeling records offered before after
      (splicePhysicalForward original relabeling records offered before after position) = position :=
  splice_physical_backward_forward original relabeling records offered before after position

example
    (beforeAccepted : ArbitrarySupportSplice.compile original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) = some before)
    (afterAccepted : ArbitrarySupportSplice.compile (result original relabeling) records offered =
      some after)
    (position : Fin before.count) :
    after.program.terminalGateSources
        (splicePhysicalForward original relabeling records offered before after position) =
      (sourceMap (splicePhysicalForward original relabeling records offered before after)
          (before.program.terminalGateSources position).1,
        sourceMap (splicePhysicalForward original relabeling records offered before after)
          (before.program.terminalGateSources position).2) :=
  splice_compiled_sources original relabeling records offered before after
    beforeAccepted afterAccepted position

example
    (accepted : ArbitrarySupportSplice.compile (result original relabeling) records offered =
      some after) :
    ArbitrarySupportSplice.compile original
      (backwardRecords original.program relabeling records)
      (pullReplacement original relabeling records offered) =
        some (pullCompiledSplice original relabeling records offered after accepted) :=
  pullCompiledSplice_accepted original relabeling records offered after accepted

end Generic

#print axioms PNP.DirectWire.StructuralReindexing.splice_physical_backward_forward
#print axioms PNP.DirectWire.StructuralReindexing.splice_physical_forward_backward
#print axioms PNP.DirectWire.StructuralReindexing.splice_physical_position
#print axioms PNP.DirectWire.StructuralReindexing.splice_physical_exterior
#print axioms PNP.DirectWire.StructuralReindexing.splice_physical_replacement
#print axioms PNP.DirectWire.StructuralReindexing.splice_compiled_sources
#print axioms PNP.DirectWire.StructuralReindexing.splice_compiled_output_source
#print axioms PNP.DirectWire.StructuralReindexing.splice_compiled_gate_count
#print axioms PNP.DirectWire.StructuralReindexing.splice_compiled_semantics
#print axioms PNP.DirectWire.StructuralReindexing.pull_splice_isSome
#print axioms PNP.DirectWire.StructuralReindexing.pullCompiledSplice_accepted
#print axioms PNP.DirectWire.StructuralReindexing.literal_replacement_transport

-- Execution checks only; these fixtures do not establish the generic result.
private def checkCompiled {inputs gates outputs profileWidth replacementGates : Nat}
    (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (offered : Candidate
      (terminalBoundaryPorts (result original relabeling).program records).length replacementGates
      (terminalInterfacePorts (result original relabeling) records).length) : Bool :=
  match accepted : ArbitrarySupportSplice.compile (result original relabeling) records offered with
  | none => false
  | some after =>
      let before := pullCompiledSplice original relabeling records offered after accepted
      let forward := splicePhysicalForward original relabeling records offered before after
      let backward := splicePhysicalBackward original relabeling records offered before after
      let predecessor := backwardRecords original.program relabeling records
      let pulled := pullReplacement original relabeling records offered
      decide (before.count = after.count) &&
      (allFin before.count).all (fun position =>
        decide (backward (forward position) = position) &&
        decide ((after.program.terminalGateSources (forward position)).1 =
          sourceMap forward (before.program.terminalGateSources position).1) &&
        decide ((after.program.terminalGateSources (forward position)).2 =
          sourceMap forward (before.program.terminalGateSources position).2)) &&
      (allFin after.count).all (fun position => decide (forward (backward position) = position)) &&
      (allFin (ArbitrarySupportSplice.exterior predecessor).length).all (fun outside =>
        decide (forward (before.position (Fin.castAdd replacementGates outside)) =
          after.position (Fin.castAdd replacementGates
            ((exteriorPorts original relabeling records).forward outside)))) &&
      (allFin replacementGates).all (fun inside =>
        decide (forward (before.position
          (Fin.natAdd (ArbitrarySupportSplice.exterior predecessor).length inside)) =
          after.position (Fin.natAdd (ArbitrarySupportSplice.exterior records).length inside))) &&
      (allFin outputs).all (fun output =>
        decide ((ArbitrarySupportSplice.result (result original relabeling) records offered after).directWireWord.source
            output =
          sourceMap forward
            ((ArbitrarySupportSplice.result original predecessor pulled before).directWireWord.source output)))

private def checkWhole {inputs gates outputs profileWidth replacementGates : Nat}
    (original : Candidate inputs gates outputs) (relabeling : GateRenaming gates)
    (records : List
      (TerminalPrimitiveRecord inputs (compiled original.program relabeling).count outputs profileWidth))
    (offered : Candidate
      (terminalBoundaryPorts (result original relabeling).program records).length replacementGates
      (terminalInterfacePorts (result original relabeling) records).length)
    (input : Valuation inputs) : Bool :=
  match accepted : ArbitrarySupportSplice.compile (result original relabeling) records offered with
  | none => false
  | some after =>
      let before := pullCompiledSplice original relabeling records offered after accepted
      let predecessor := backwardRecords original.program relabeling records
      let pulled := pullReplacement original relabeling records offered
      (allFin outputs).all (fun output =>
        decide ((ArbitrarySupportSplice.result original predecessor pulled before).semantics input output =
          original.semantics input output) &&
        decide ((ArbitrarySupportSplice.result (result original relabeling) records offered after).semantics
          input output = original.semantics input output))

private def sourceTag {inputs gates : Nat} : Source inputs gates → Nat × Nat
  | .input index => (0, index.val)
  | .gate index => (1, index.val)
  | .constant value => (2, if value then 1 else 0)

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
      let boundary := terminalBoundaryPorts changed.program records
      let interface := terminalInterfacePorts changed records
      if twoInputs : boundary.length = 2 then
        if twoOutputs : interface.length = 2 then
          let offered : Candidate boundary.length 0 interface.length :=
            Candidate.ofDirectWireWord .empty ⟨fun output => .input ⟨output.val, by omega⟩⟩
          let extracted := (extractTerminalSupport changed records).extractedCandidate
          let constants : Candidate boundary.length 0 interface.length :=
            Candidate.ofDirectWireWord .empty ⟨fun output => .constant (output.val == 0)⟩
          let samples : List (Valuation 2) :=
            [fun _ => false, fun i => i.val == 0, fun i => i.val == 1, fun _ => true]
          match accepted : ArbitrarySupportSplice.compile changed records offered with
          | none => [("actual zero-gate replacement must compile", false)]
          | some after =>
              let before := pullCompiledSplice original relabeling records offered after accepted
              let forward := splicePhysicalForward original relabeling records offered before after
              let predecessor := backwardRecords exampleProgram relabeling records
              let pulled := pullReplacement original relabeling records offered
              [("zero-gate replacement has exact compiled wires and ownership",
                  checkCompiled original relabeling records offered),
                ("compiled physical map is genuinely nonidentity",
                  (allFin before.count).any (fun position => (forward position).val != position.val)),
                ("strict saving counts actual compiled gates",
                  decide (before.count = 2) && decide (after.count = 2) &&
                    decide (before.count < 6)),
                ("nonempty replacement preserves compiled replacement ownership",
                  checkCompiled original relabeling records extracted),
                ("ordered true and false outputs retain literal references",
                  checkCompiled original relabeling records constants),
                ("compatible zero-gate replacement preserves every input case",
                  samples.all (checkWhole original relabeling records offered)),
                ("actual extracted replacement preserves every input case",
                  samples.all (checkWhole original relabeling records extracted)),
                ("structural correspondence alone does not imply semantic compatibility",
                  !(samples.all (checkWhole original relabeling records constants))),
                ("omitting the computed physical map gives wrong ordered outputs",
                  !((allFin 2).all (fun output =>
                    decide (sourceTag ((ArbitrarySupportSplice.result changed records offered after).directWireWord.source
                        output) =
                      sourceTag ((ArbitrarySupportSplice.result original predecessor pulled before).directWireWord.source
                        output)))))]
        else [("descendant interface must have two outputs", false)]
      else [("descendant boundary must have two inputs", false)]

private def emptyFixture : Bool :=
  let original : Candidate 1 0 2 :=
    Candidate.ofDirectWireWord .empty
      ⟨fun output => if output.val = 0 then .input 0 else .constant true⟩
  match GateRenaming.decode 0 [] with
  | none => false
  | some relabeling =>
      let records : List (TerminalPrimitiveRecord 1
        (compiled original.program relabeling).count 2 0) := []
      let changed := result original relabeling
      let boundary := terminalBoundaryPorts changed.program records
      let interface := terminalInterfacePorts changed records
      if emptyInterface : interface.length = 0 then
        let offered : Candidate boundary.length 0 interface.length :=
          Candidate.ofDirectWireWord .empty
            ⟨fun output => False.elim (by have bound := output.isLt; omega)⟩
        checkCompiled original relabeling records offered &&
          checkWhole original relabeling records offered (fun _ => false) &&
          checkWhole original relabeling records offered (fun _ => true)
      else false

#eval (do
  for (name, checked) in fixtures ++ [("zero physical gates preserve primary and constant outputs", emptyFixture)] do
    unless checked do throw (IO.userError ("reindexed-compiled-splice failure: " ++ name))
  IO.println "reindexed-compiled-splice-runtime-regressions: 10 passed"
  : IO Unit)
