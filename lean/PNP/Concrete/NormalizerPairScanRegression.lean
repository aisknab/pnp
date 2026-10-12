import PNP.Concrete.NormalizerPairScan
namespace PNP.Concrete.NormalizerBlocks
def pairScanFixture (xs : List CNFLiteral) : PathPairs.State := ⟨Occurrence.initialRegisters [], PathData.encode xs, [], []⟩
example : (PathPairs.whole (pairScanFixture [⟨false,0⟩,⟨true,1⟩,⟨false,2⟩,⟨true,3⟩])).state.buffer =
    (TableBatch.encodeUpdates [(1,0),(3,2)]).reverse := by decide
example : (PathPairs.whole (pairScanFixture [⟨false,0⟩,⟨true,1⟩,⟨true,3⟩])).state.buffer =
    (TableBatch.encodeUpdates [(1,0)]).reverse := by decide
example (r : PathPairs.State) : (PathPairs.whole r).state.pending = [] := PathPairs.whole_stopped r
#print axioms PathPairs.scan_exec
#print axioms PathPairs.scan_fuel_bound
#print axioms PathPairs.scan_stopped
#print axioms PathPairs.whole_exec
#print axioms PathPairs.whole_fuel_bound
#print axioms PathPairs.whole_stopped
end PNP.Concrete.NormalizerBlocks
