import PNP.Concrete.NormalizerPathNode

namespace PNP.Concrete.NormalizerBlocks
def pathNodeFixture : TracePath.State :=
  ⟨{ParentQuery.initial [] with pending := TraceData.row (⟨false, 2⟩, some ⟨true, 0⟩) [true, false]}, [false], []⟩
example : (TracePath.nodeRead pathNodeFixture).core.pending = [true, false] := by decide
example : (TracePath.nodeRead pathNodeFixture).parentBytes =
    TraceData.predecessor (some ⟨true, 0⟩) [true, false] := by decide
example : (TracePath.nodeRead pathNodeFixture).buffer = [false] := by decide
example : (TracePath.nodeRead pathNodeFixture).core.currentIndex = [true, true] := by decide

#print axioms ParentQuery.pathNodePrefix_exec
#print axioms ParentQuery.pathNodeSuffix_exec
#print axioms TracePath.saveParent_exec
#print axioms TracePath.readNode_exec
#print axioms TracePath.nodeRead_fields
#print axioms TracePath.nodeFuel_bound
#print axioms TracePath.parentBytes_bound
#print axioms TracePath.nodeRead_canonical

end PNP.Concrete.NormalizerBlocks
