import PNP.Concrete.NormalizerEdgeBranches

namespace PNP.Concrete.NormalizerBlocks

example (r : ForwardEdge.State) : EdgeKinds.forwardFuel r ≤ EdgeKinds.branchBound r :=
  EdgeKinds.forwardFuel_bound r
example (r : ForwardEdge.State) : EdgeKinds.reverseFuel r ≤ EdgeKinds.branchBound r :=
  EdgeKinds.reverseFuel_bound r
example (r : ForwardEdge.State) : (EdgeKinds.swapped r).target = r.index := rfl
example (r : ForwardEdge.State) : (EdgeKinds.swapped r).index = r.target := rfl

#print axioms EdgeKinds.swap_exec
#print axioms EdgeKinds.normalize_exec
#print axioms EdgeKinds.reverse_exec
#print axioms EdgeKinds.forward_exec
#print axioms EdgeKinds.reverseFuel_bound
#print axioms EdgeKinds.forwardFuel_bound
#print axioms EdgeKinds.reverse_canonical
#print axioms EdgeKinds.forward_canonical

end PNP.Concrete.NormalizerBlocks
