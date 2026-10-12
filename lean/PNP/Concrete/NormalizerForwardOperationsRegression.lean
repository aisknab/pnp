import PNP.Concrete.NormalizerForwardOperations

namespace PNP.Concrete.NormalizerBlocks

example (r : ForwardEdge.State) : ForwardEdge.finishFuel r ≤ 4 := ForwardEdge.finishFuel_bound r
example : ForwardEdge.present [] = false := rfl
example : ForwardEdge.present [false, true] = false := rfl
example : ForwardEdge.present [true, false] = true := rfl
example (found : Option CNFLiteral) :
    ForwardEdge.present (Occurrence.answer found) = found.isSome := ForwardEdge.present_answer found

#print axioms ForwardEdge.readHeader_exec
#print axioms ForwardEdge.saveTarget_exec
#print axioms ForwardEdge.saveIndex_exec
#print axioms ForwardEdge.loadData_exec
#print axioms ForwardEdge.saveData_exec
#print axioms ForwardEdge.prepare_exec
#print axioms ForwardEdge.query_exec
#print axioms ForwardEdge.saveAnswer_exec
#print axioms ForwardEdge.finish_exec
#print axioms ForwardEdge.finishFuel_bound
#print axioms ForwardEdge.present_answer

end PNP.Concrete.NormalizerBlocks
