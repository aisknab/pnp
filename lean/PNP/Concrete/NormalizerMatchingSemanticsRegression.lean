import PNP.Concrete.NormalizerMatchingSemantics
namespace PNP.Concrete.NormalizerBlocks
example : MatchingLoop.fullTable 0 [] = [] := by decide
example : MatchingLoop.fullTable 0 [[]] = [none] := by decide
example : MatchingLoop.fullTable 1 [[⟨true,0⟩]] = [some 0] := by decide
example : MatchingLoop.fullTable 2 [[⟨true,0⟩,⟨true,1⟩],[⟨true,0⟩]] = [some 1,some 0] := by decide
example (variables : Nat) (clauses : List (List CNFLiteral)) :
    (MatchingLoop.fullTable variables clauses).length = clauses.length :=
  (MatchingLoop.fullTable_invariant variables clauses).2
#print axioms MatchingLoop.finish_zero
#print axioms MatchingLoop.finish_terminal
#print axioms MatchingLoop.finish_augment
#print axioms MatchingLoop.finish_invariant
#print axioms MatchingLoop.fullTable_invariant
end PNP.Concrete.NormalizerBlocks
