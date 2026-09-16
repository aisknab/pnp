import PNP.NANDCompiledGateProvenance

/-! General inverse contracts plus a real, non-identity compiler ordering. -/
namespace PNP.Regression.CompiledGateProvenance

open PNP.DirectWire

example {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (compiled : CompiledRawNandGraph graph) (position : Fin compiled.count) :
    compiled.position (compiled.physicalOrigin position) = position :=
  compiled.position_physicalOrigin position

example {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}
    (compiled : CompiledRawNandGraph graph) :
    compiled.physicalOrigins.Nodup ∧ compiled.physicalOrigins.Perm (allFin nodes) :=
  ⟨compiled.physicalOrigins_nodup, compiled.physicalOrigins_perm⟩

private def reordered : RawNandGraph 1 3 where
  gate := fun node =>
    if node.val = 0 then ⟨.gate 2, .input 0⟩
    else if node.val = 1 then ⟨.gate 0, .gate 2⟩
    else ⟨.input 0, .input 0⟩

private def emptyGraph : RawNandGraph 0 0 where
  gate := Fin.elim0

#eval show IO Unit from do
  let some compiled := compileRawNandGraph reordered
    | throw (IO.userError "acyclic reordered graph rejected")
  if compiled.physicalOrigins.map Fin.val != [2, 0, 1] then
    throw (IO.userError "physical origins ignored the actual non-identity compiler order")
  if (allFin 3).map (fun node => (compiled.position node).val) != [1, 2, 0] then
    throw (IO.userError "fixture no longer exercises a non-identity position map")
  let some empty := compileRawNandGraph emptyGraph
    | throw (IO.userError "empty graph rejected")
  if !empty.physicalOrigins.isEmpty then
    throw (IO.userError "empty compiler fabricated a physical origin")
  IO.println "M266 compiled-gate-provenance-regressions-passed"

#print axioms CompiledRawNandGraph.position_surjective
#print axioms CompiledRawNandGraph.position_physicalOrigin
#print axioms CompiledRawNandGraph.physicalOrigin_position
#print axioms CompiledRawNandGraph.physicalOrigin_injective
#print axioms CompiledRawNandGraph.physicalOrigin_surjective
#print axioms CompiledRawNandGraph.physicalOrigins_nodup
#print axioms CompiledRawNandGraph.physicalOrigins_perm
#print axioms RawNandCompilationState.finish_physicalOrigin

end PNP.Regression.CompiledGateProvenance
