import PNP.Concrete.NormalizerPathCompare

namespace PNP.Concrete.NormalizerBlocks
def pathCompareFixture : TracePath.State :=
  ⟨{ParentQuery.initial [] with pending := TraceData.row (⟨false, 2⟩, some ⟨true, 0⟩) [], targetIndex := [true, true], targetTag := [false]}, [true], []⟩
example : (TracePath.probed pathCompareFixture).registers.output = [true] := by decide
example : (TracePath.probed pathCompareFixture).core.pending = [] := by decide
example : (TracePath.probed pathCompareFixture).parentBytes = [true, true, false] := by decide
example : (TracePath.probed pathCompareFixture).buffer = [true] := by decide

#print axioms TraceMember.comparison_nodes
#print axioms TracePath.probe_exec
#print axioms TracePath.probed_pending
#print axioms TracePath.probed_preserves
#print axioms TracePath.probed_nodes
#print axioms TracePath.probeFuel_bound
#print axioms TracePath.probed_canonical

end PNP.Concrete.NormalizerBlocks
