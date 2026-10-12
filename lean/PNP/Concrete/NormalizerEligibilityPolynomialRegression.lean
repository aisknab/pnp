import PNP.Concrete.NormalizerEligibilityPolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : Eligibility.sourceSteps input + 1 ≤ Eligibility.sourceFuel.eval input.length :=
  Eligibility.sourceSteps_bound input
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine Eligibility.program)
      ((BitRegister.CompilerIO.runtimePolynomial 22 Eligibility.sourceFuel).eval input.length) input = .accept :=
  Eligibility.polynomial_accepts input
example (target : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) :
    Eligibility.polynomial.output (ParentQuery.encode target clauses entries trace) =
      ParentQuery.answer (Eligibility.value target clauses entries trace) :=
  Eligibility.polynomial_canonical target clauses entries trace
example : Eligibility.value ⟨true, 0⟩ [] [none] [(⟨true, 0⟩, none)] = none := by decide
example : Eligibility.value ⟨true, 0⟩ [] [none] [(⟨false, 0⟩, none)] = some none := by decide
example : Eligibility.value ⟨false, 0⟩ [[⟨true, 0⟩]] [none] [(⟨true, 0⟩, some ⟨false, 0⟩)] =
    some (some ⟨true, 0⟩) := by decide
example : Eligibility.value ⟨false, 0⟩ [[⟨true, 0⟩]] [none] [(⟨true, 0⟩, none), (⟨false, 0⟩, none)] = none := by decide
example : Eligibility.value ⟨false, 1⟩ [[⟨true, 0⟩]] [none] [] = none := by decide

#print axioms Eligibility.loader_exec
#print axioms Eligibility.block_exec
#print axioms Eligibility.closed_run
#print axioms Eligibility.sourceFuel_eval
#print axioms Eligibility.sourceSteps_bound
#print axioms Eligibility.padded_run
#print axioms Eligibility.acceptsWithin
#print axioms Eligibility.polynomial_program
#print axioms Eligibility.polynomial_output
#print axioms Eligibility.polynomial_accepts
#print axioms Eligibility.polynomial_output_length
#print axioms Eligibility.polynomial_canonical
#print axioms Eligibility.machine_canonical

end PNP.Concrete.NormalizerBlocks
