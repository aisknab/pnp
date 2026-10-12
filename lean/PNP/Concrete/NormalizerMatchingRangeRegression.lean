import PNP.Concrete.NormalizerMatchingRange
namespace PNP.Concrete.NormalizerBlocks
example : Search.traceValue 0 [] [] = [] := by decide
example : Search.traceValue 1 [[⟨true,0⟩]] [none] =
    [(⟨false,0⟩,some ⟨true,0⟩),(⟨true,0⟩,none)] := by decide
example (variables : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    ExplorationData.TraceBound (clauses.length + variables) (Search.traceValue variables clauses entries) :=
  (MatchingLoop.search_trace_range variables clauses entries).1
#print axioms MatchingLoop.parent_within
#print axioms MatchingLoop.eligibility_within
#print axioms MatchingLoop.extraction_range
#print axioms MatchingLoop.exploration_range
#print axioms MatchingLoop.search_trace_range
end PNP.Concrete.NormalizerBlocks
