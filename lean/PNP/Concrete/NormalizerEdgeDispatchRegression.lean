import PNP.Concrete.NormalizerEdgeDispatch

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : EdgeKinds.loaderFuel input ≤ 41 * input.length + 86 := EdgeKinds.loaderFuel_bound input
example (r : EdgeKinds.State) : EdgeKinds.dispatchFuel r ≤ EdgeKinds.branchBound r.core + 2 := EdgeKinds.dispatchFuel_bound r
example : ForwardEdge.present (EdgeKinds.loaded []).first = false := rfl
example : ForwardEdge.present (EdgeKinds.loaded [true]).second = false := rfl

#print axioms EdgeKinds.branch_head
#print axioms EdgeKinds.tags_exec
#print axioms EdgeKinds.loader_exec
#print axioms EdgeKinds.dispatch_exec
#print axioms EdgeKinds.dispatchFuel_bound
#print axioms EdgeKinds.dispatch_output
#print axioms EdgeKinds.loaderFuel_bound
#print axioms EdgeKinds.loaded_size
#print axioms EdgeKinds.loaded_core

end PNP.Concrete.NormalizerBlocks
