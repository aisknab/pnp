import PNP.Concrete.NormalizerParentStep

namespace PNP.Concrete.NormalizerBlocks

example (r : ParentQuery.State) : ParentQuery.bodyFuel r ≤ ParentQuery.stepBound r := ParentQuery.bodyFuel_bound r
example (r : ParentQuery.State) (h : r.pending ≠ []) :
    (ParentQuery.bodyResult r).pending = [] ∨ (ParentQuery.bodyResult r).pending.length < r.pending.length :=
  ParentQuery.body_progress r h
example (r : ParentQuery.State) (h : r.pending ≠ []) :
    ParentQuery.stepBound (ParentQuery.bodyResult r) ≤ ParentQuery.stepBound r := ParentQuery.stepBound_mono r h
example (r : ParentQuery.State) :
    (ParentQuery.accepted r).output = true :: true :: ForwardEdge.present r.graph.first :: r.currentIndex := rfl

#print axioms ParentQuery.queryEdge_exec
#print axioms ParentQuery.edge_data
#print axioms ParentQuery.answerTag_exec
#print axioms ParentQuery.acceptParent_exec
#print axioms ParentQuery.selectParent_exec
#print axioms ParentQuery.body_exec
#print axioms ParentQuery.bodyFuel_bound
#print axioms ParentQuery.body_preserves
#print axioms ParentQuery.body_progress
#print axioms ParentQuery.stepBound_mono

end PNP.Concrete.NormalizerBlocks
