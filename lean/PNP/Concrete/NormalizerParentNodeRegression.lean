import PNP.Concrete.NormalizerParentNode

namespace PNP.Concrete.NormalizerBlocks

example (r : ParentQuery.State) : ParentQuery.nodeFuel r ≤ 8 * r.pending.length + 40 :=
  ParentQuery.nodeFuel_bound r
example (r : ParentQuery.State) (h : r.pending ≠ []) : (ParentQuery.nodeResult r).pending.length < r.pending.length :=
  ParentQuery.node_shorter r h
example (r : ParentQuery.State) : (ParentQuery.nodeResult r).currentIndex = TraceData.nodeIndex r.pending :=
  (ParentQuery.node_fields r).2.1
example (r : ParentQuery.State) : (ParentQuery.nodeResult r).output = r.output :=
  (ParentQuery.node_preserves r).2.2.2.2

#print axioms ParentQuery.beginNode_exec
#print axioms ParentQuery.saveNode_exec
#print axioms ParentQuery.skipParent_exec
#print axioms ParentQuery.parentSkipped_input
#print axioms ParentQuery.skipFuel_bound
#print axioms ParentQuery.readNode_exec
#print axioms ParentQuery.node_fields
#print axioms ParentQuery.node_preserves
#print axioms ParentQuery.nodeFuel_bound
#print axioms ParentQuery.node_shorter

end PNP.Concrete.NormalizerBlocks
