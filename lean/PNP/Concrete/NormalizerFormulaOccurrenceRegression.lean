import PNP.Concrete.NormalizerFormulaOccurrence

namespace PNP.Concrete.NormalizerBlocks

example (target index : Nat) (clauses : List (List CNFLiteral)) :
    ClauseQuery.occurrencePolynomial.output (ClauseQuery.encodeQuery target index clauses) =
      Occurrence.answer ((clauses[index]?.getD []).find? (fun literal => literal.variableIndex == target)) :=
  ClauseQuery.occurrencePolynomial_canonical target index clauses
example (target index : Nat) (clauses : List (List CNFLiteral)) :
    (ClauseQuery.occurrencePolynomial.output (ClauseQuery.encodeQuery target index clauses)).head! =
      ((clauses[index]?.getD []).find? (fun literal => literal.variableIndex == target)).isSome :=
  ClauseQuery.incidence_canonical target index clauses
example (input : BitString) :
    boundedDecide ClauseQuery.occurrenceRawRefinement.machine
      (ClauseQuery.occurrenceRawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  ClauseQuery.occurrenceMachine_halts input
example (input : BitString) :
    BitString.size (machineOutput ClauseQuery.occurrenceRawRefinement.machine
      (ClauseQuery.occurrenceRawRefinement.timeBound.eval (BitString.size input)) input) ≤
        ClauseQuery.occurrencePolynomial.outputSizeBound.eval (BitString.size input) :=
  ClauseQuery.occurrenceMachine_output_size input
example : ClauseQuery.occurrencePolynomial.output (ClauseQuery.encodeQuery 2 1 [[], [⟨false, 2⟩, ⟨true, 2⟩]]) =
    [true, false] := by rw [ClauseQuery.occurrencePolynomial_canonical]; rfl
example : ClauseQuery.occurrencePolynomial.output (ClauseQuery.encodeQuery 2 0 [[⟨true, 3⟩], [⟨false, 2⟩]]) =
    [false] := by rw [ClauseQuery.occurrencePolynomial_canonical]; rfl
example : ClauseQuery.occurrencePolynomial.output (ClauseQuery.encodeQuery 2 2 [[⟨true, 3⟩], [⟨false, 2⟩]]) =
    [false] := by rw [ClauseQuery.occurrencePolynomial_canonical]; rfl

#print axioms ClauseQuery.occurrencePolynomial
#print axioms ClauseQuery.occurrencePolynomial_program
#print axioms ClauseQuery.occurrencePolynomial_output
#print axioms ClauseQuery.occurrencePolynomial_canonical
#print axioms ClauseQuery.incidence_canonical
#print axioms ClauseQuery.queryRawRefinement
#print axioms ClauseQuery.literalRawRefinement
#print axioms ClauseQuery.occurrenceRawRefinement
#print axioms ClauseQuery.occurrenceMachine_output
#print axioms ClauseQuery.occurrenceMachine_canonical
#print axioms ClauseQuery.occurrenceMachine_halts
#print axioms ClauseQuery.occurrenceMachine_output_size

end PNP.Concrete.NormalizerBlocks
