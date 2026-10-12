import PNP.Concrete.NormalizerParentState

namespace PNP.Concrete.NormalizerBlocks

example (r : ParentQuery.State) : (ParentQuery.resetResult r).pending = r.pending := rfl
example (r : ParentQuery.State) : (ParentQuery.headerResult r).targetIndex = r.targetIndex := rfl
example (r : ParentQuery.State) : (ParentQuery.dataResult r).graph.core.matching = r.graph.core.matching := rfl
example (word : BitString) (r : Occurrence.Registers) :
    (ParentQuery.prepended word r).input = List.replicate word.length true ++ r.input := rfl

#print axioms ParentQuery.liftCore_exec
#print axioms ParentQuery.reset_exec
#print axioms ParentQuery.readHeader_exec
#print axioms ParentQuery.loadData_exec
#print axioms ParentQuery.prepend_exec
#print axioms ParentQuery.prependCore_exec

end PNP.Concrete.NormalizerBlocks
