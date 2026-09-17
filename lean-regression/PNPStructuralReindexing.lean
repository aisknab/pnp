import PNP.NANDStructuralReindexing

open PNP PNP.DirectWire PNP.DirectWire.StructuralReindexing

-- These arbitrary-dimension contracts are theorem authority, unlike the runtime fixtures.
example {inputs gates outputs : Nat} (original : Candidate inputs gates outputs)
    (relabeling : GateRenaming gates) (node : Fin gates) :
    (result original relabeling).program.terminalGateSources
        (forwardGate original.program relabeling node) =
      (sourceMap (forwardGate original.program relabeling)
          (original.program.terminalGateSources node).1,
        sourceMap (forwardGate original.program relabeling)
          (original.program.terminalGateSources node).2) :=
  result_sources original relabeling node

example {inputs gates outputs : Nat} (original : Candidate inputs gates outputs)
    (code : List (Nat × Nat)) (output : Implementation inputs outputs)
    (accepted : attempt original code = some output) (input : Valuation inputs)
    (coordinate : Fin outputs) :
    output.candidate.semantics input coordinate = original.semantics input coordinate :=
  attempt_semantics original code output accepted input coordinate

#print axioms PNP.DirectWire.StructuralReindexing.GateRenaming.decode_isSome
#print axioms PNP.DirectWire.StructuralReindexing.result_sources
#print axioms PNP.DirectWire.StructuralReindexing.backward_forward
#print axioms PNP.DirectWire.StructuralReindexing.forward_backward
#print axioms PNP.DirectWire.StructuralReindexing.attempt_semantics
#print axioms PNP.DirectWire.StructuralReindexing.attempt_gateCount

private def exampleProgram : Program 2 3 :=
  ((Program.empty.snoc ⟨.input 0, .input 0⟩).snoc
    ⟨.input 1, .input 1⟩).snoc ⟨.gate 0, .gate 1⟩

private def original : Candidate 2 3 1 :=
  Candidate.ofDirectWireWord exampleProgram ⟨fun _ => .gate 2⟩

private def actualReordering : Bool :=
  match GateRenaming.decode 3 [(0, 1)] with
  | none => false
  | some relabeling =>
      let changed := result original relabeling
      decide ((forwardGate exampleProgram relabeling 0).val = 1) &&
        decide ((forwardGate exampleProgram relabeling 1).val = 0) &&
        decide ((forwardGate exampleProgram relabeling 2).val = 2) &&
        decide (changed.toImplementation.gateCount = 3) &&
        [false, true].all (fun left => [false, true].all (fun right =>
          decide (changed.semantics (fun index => if index.val = 0 then left else right) 0 =
            (left || right))))

#eval (do
  let fixtures : List (String × Bool) :=
    [("actual nonidentity order and all output valuations", actualReordering),
      ("raw valid code", (attempt original [(0, 1)]).isSome),
      ("invalid final instruction rejects complete code",
        !(attempt original [(0, 1), (0, 3)]).isSome),
      ("invalid first coordinate", !(GateRenaming.decode 3 [(3, 0)]).isSome),
      ("empty zero-width relabeling", (GateRenaming.decode 0 []).isSome),
      ("nonempty zero-width relabeling rejected", !(GateRenaming.decode 0 [(0, 0)]).isSome),
      ("duplicate and self swaps remain valid", (attempt original [(0, 0), (0, 1), (0, 1)]).isSome)]
  for (name, checked) in fixtures do
    unless checked do throw (IO.userError ("structural-reindexing failure: " ++ name))
  IO.println "structural-reindexing-runtime-regressions: 7 passed"
  : IO Unit)
