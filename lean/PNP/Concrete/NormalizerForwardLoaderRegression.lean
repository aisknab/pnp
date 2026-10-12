import PNP.Concrete.NormalizerForwardLoader

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : ForwardEdge.loaderFuel input ≤ 41 * input.length + 82 :=
  ForwardEdge.loaderFuel_bound input
example (target index : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    (ForwardEdge.loaded (ForwardEdge.encode target index clauses entries)).formula = GraphQuery.clauseData clauses :=
  (ForwardEdge.loaded_canonical target index clauses entries).2.2.1
example : (ForwardEdge.loaded []).matching = [] := rfl
example : (ForwardEdge.loaded (ForwardEdge.encode 3 2 [[], [⟨false, 1⟩]] [none, some 3])).target =
    [true, true, true] := (ForwardEdge.loaded_canonical 3 2 _ _).1

#print axioms ForwardEdge.loader_exec
#print axioms ForwardEdge.header_input_bound
#print axioms ForwardEdge.header_target_bound
#print axioms ForwardEdge.loaded_size
#print axioms ForwardEdge.loaderFuel_bound
#print axioms ForwardEdge.loaded_canonical

end PNP.Concrete.NormalizerBlocks
