import PNP.Concrete.NormalizerParentRoot

namespace PNP.Concrete.NormalizerBlocks

example (r : ParentQuery.State) :
    ParentQuery.rootFuel r ≤ 342 * r.targetIndex.length + 339 * r.graph.core.matching.length + 1316 :=
  ParentQuery.rootFuel_bound r
example (r : ParentQuery.State) :
    (ParentQuery.rootInput r).length = r.targetIndex.length + r.graph.core.matching.length + 2 :=
  ParentQuery.rootInput_length r
example (r : ParentQuery.State) : (ParentQuery.rootResult r).pending = r.pending := (ParentQuery.root_preserves r).1

#print axioms ParentQuery.rootData_exec
#print axioms ParentQuery.rootTag_exec
#print axioms ParentQuery.rootPrepare_exec
#print axioms ParentQuery.rootQuery_exec
#print axioms ParentQuery.rootInput_length
#print axioms ParentQuery.rootFuel_bound
#print axioms ParentQuery.root_output
#print axioms ParentQuery.root_canonical
#print axioms ParentQuery.root_preserves

end PNP.Concrete.NormalizerBlocks
