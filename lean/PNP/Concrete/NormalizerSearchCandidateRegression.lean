import PNP.Concrete.NormalizerSearchCandidate
namespace PNP.Concrete.NormalizerBlocks
def searchCandidateFixture (variables : Nat) (clauses : List (List CNFLiteral)) (matching : MatchingTable.Entries) : Search.State :=
  Search.seenDerived (Search.explored (Exploration.encode variables clauses matching))
example : (Search.selected (searchCandidateFixture 1 [[⟨true, 0⟩]] [none])).parent.graph.core.matching = TableOwner.answer (some 0) := by decide
example : (Search.selected (searchCandidateFixture 1 [[⟨true, 0⟩]] [some 0])).parent.graph.core.matching = TableOwner.answer none := by decide
example : (Search.selected (searchCandidateFixture 2 [[⟨true, 1⟩, ⟨false, 0⟩]] [none])).parent.graph.core.matching = TableOwner.answer (some 0) := by decide
#print axioms Search.saveTables_exec
#print axioms Search.readWidth_exec
#print axioms Search.prepareCandidate_exec
#print axioms Search.prepareCandidateFuel_bound
#print axioms Search.candidatePrepared_fields
#print axioms Search.selectCandidate_exec
#print axioms Search.select_exec
#print axioms Search.selected_frame
#print axioms Search.selected_canonical
end PNP.Concrete.NormalizerBlocks
