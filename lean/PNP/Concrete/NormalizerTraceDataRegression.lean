import PNP.Concrete.NormalizerTraceData

namespace PNP.Concrete.NormalizerBlocks

example (entry : TraceData.Row) (suffix : BitString) : TraceData.node (TraceData.row entry suffix) = entry.1 :=
  TraceData.node_canonical entry suffix
example (entry : TraceData.Row) (suffix : BitString) : TraceData.next (TraceData.row entry suffix) = suffix :=
  TraceData.next_canonical entry suffix
example : TraceData.next (TraceData.row (⟨false, 2⟩, some ⟨true, 7⟩) [true, false]) = [true, false] :=
  TraceData.next_canonical _ _
example : ParentQuery.answer none = [false] := rfl
example : ParentQuery.answer (some none) = [true, false] := rfl
example : ParentQuery.answer (some (some ⟨false, 2⟩)) = [true, true, false, true, true] := rfl
example : ParentQuery.value ⟨true, 0⟩ [[]] [none] [(⟨false, 0⟩, none)] = some none := rfl

#print axioms TraceData.skipParent_canonical
#print axioms TraceData.skipParent_length
#print axioms TraceData.node_canonical
#print axioms TraceData.nodeIndex_canonical
#print axioms TraceData.next_canonical
#print axioms TraceData.next_shorter
#print axioms TraceData.nodeIndex_length
#print axioms ParentQuery.root_before_edges
#print axioms ParentQuery.absent_distinct_root

end PNP.Concrete.NormalizerBlocks
