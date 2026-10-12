import PNP.Concrete.NormalizerCutPack
namespace PNP.Concrete.NormalizerBlocks
example (r : CutDriver.State) :
    (CutDriver.packed r).registers.output =
      CutDriver.packet r.core.table r.trace r.clauses r.variables := CutDriver.packed_output r
example (r : CutDriver.State) (bound : Nat) (h : r.store.Bounded bound) :
    CutDriver.packFuel r ≤ 36 * bound + 45 := CutDriver.packFuel_bound r bound h
#print axioms CutDriver.packVariables_exec
#print axioms CutDriver.prependClauses_exec
#print axioms CutDriver.prependTrace_exec
#print axioms CutDriver.prependMatching_exec
#print axioms CutDriver.pack_exec
#print axioms CutDriver.packed_output
#print axioms CutDriver.packed_frame
#print axioms CutDriver.packFuel_bound
end PNP.Concrete.NormalizerBlocks
