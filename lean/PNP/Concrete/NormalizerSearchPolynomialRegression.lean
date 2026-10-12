import PNP.Concrete.NormalizerSearchPolynomial
namespace PNP.Concrete.NormalizerBlocks
example (input : BitString) : Search.sourceSteps input + 1 ≤ Search.sourceFuel.eval input.length := Search.sourceSteps_bound input
example (n : Nat) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    Search.polynomial.output (Exploration.encode n clauses entries) = Search.answer (Search.value n clauses entries) :=
  Search.polynomial_canonical n clauses entries
example : (Search.result []).registers.output = Search.answer (.terminal []) := by decide
#print axioms Search.explored_bounded
#print axioms Search.seenDerived_bounded
#print axioms Search.selected_bounded
#print axioms Search.sourceSteps_bound
#print axioms Search.padded_run
#print axioms Search.acceptsWithin
#print axioms Search.polynomial_program
#print axioms Search.polynomial_output
#print axioms Search.polynomial_accepts
#print axioms Search.polynomial_output_length
#print axioms Search.polynomial_canonical
#print axioms Search.machine_output
#print axioms Search.machine_canonical
end PNP.Concrete.NormalizerBlocks
