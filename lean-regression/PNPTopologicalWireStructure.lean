import PNP.NANDTopologicalWireStructure

open PNP PNP.DirectWire

-- This is a general theorem contract. The executable fixture below is not proof authority.
example {inputs nodes : Nat} (graph : RawNandGraph inputs nodes)
    (compiled : CompiledRawNandGraph graph)
    (accepted : compileRawNandGraph graph = some compiled) (node : Fin nodes) :
    compiled.program.terminalGateSources (compiled.position node) =
      (compiled.translateSource (graph.gate node).left,
        compiled.translateSource (graph.gate node).right) :=
  RawNandWireStructure.compile_sources graph compiled accepted node

#print axioms PNP.DirectWire.RawNandWireStructure.compile_sources
#print axioms PNP.DirectWire.RawNandWireStructure.physicalOrigin_sources

private def scrambled : RawNandGraph 1 2 :=
  { gate := fun node =>
      if node.val = 0 then ⟨.gate 1, .constant true⟩
      else ⟨.input 0, .input 0⟩ }

private def scrambledCheck : Bool :=
  match compileRawNandGraph scrambled with
  | none => false
  | some compiled =>
      decide (compiled.count = 2) &&
        decide ((compiled.position 1).val = 0) &&
        decide ((compiled.position 0).val = 1)

#eval (if scrambledCheck then
  IO.println "topological-wire-structure-scrambled-order: pass"
  else throw (IO.userError "topological-wire-structure-scrambled-order: failure") : IO Unit)
