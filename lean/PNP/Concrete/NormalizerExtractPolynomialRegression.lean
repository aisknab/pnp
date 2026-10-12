import PNP.Concrete.NormalizerExtractPolynomial

namespace PNP.Concrete.NormalizerBlocks
open Extraction
example : (result (encode [] [none] [] [⟨false, 2⟩, ⟨true, 0⟩, ⟨false, 7⟩])).output =
    answer (some ((⟨true, 0⟩, none), [⟨false, 2⟩, ⟨false, 7⟩])) := by decide
example : (result (encode [[⟨true, 2⟩]] [none] [(⟨true, 0⟩, none)] [⟨true, 0⟩, ⟨false, 2⟩])).output =
    answer (some ((⟨false, 2⟩, some ⟨true, 0⟩), [⟨true, 0⟩])) := by decide
example : (result []).output = [false] := by decide
example : (result [false, true, true, false, true]).output = [false] := by decide
example (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) (vertices : List CNFLiteral) :
    polynomial.output (encode clauses entries trace vertices) = answer (value clauses entries trace vertices) :=
  polynomial_canonical clauses entries trace vertices

#print axioms Extraction.front_exec
#print axioms Extraction.block_exec
#print axioms Extraction.closed_run
#print axioms Extraction.loaded_step_bound
#print axioms Extraction.frontFuel_bound
#print axioms Extraction.front_bounded
#print axioms Extraction.finishFuel_of_bounded
#print axioms Extraction.finishing_bound
#print axioms Extraction.sourceSteps_bound
#print axioms Extraction.acceptsWithin
#print axioms Extraction.polynomial_program
#print axioms Extraction.polynomial_output
#print axioms Extraction.polynomial_accepts
#print axioms Extraction.polynomial_output_length
#print axioms Extraction.polynomial_canonical
#print axioms Extraction.machine_canonical

end PNP.Concrete.NormalizerBlocks
