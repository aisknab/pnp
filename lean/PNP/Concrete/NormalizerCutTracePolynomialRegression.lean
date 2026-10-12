import PNP.Concrete.NormalizerCutTracePolynomial

namespace PNP.Concrete.NormalizerBlocks

example : CutTrace.sourceSteps [false, true, false] + 1 ≤
    CutTrace.sourceFuel.eval [false, true, false].length :=
  CutTrace.sourceSteps_bound _

example (input : BitString) :
    (CutTrace.polynomial.output input).length ≤ input.length + CutTrace.sourceFuel.eval input.length :=
  CutTrace.polynomial_output_length input

example (variables : Nat) (clauses : List (List CNFLiteral)) :
    CutTrace.polynomial.output (MatchingDriver.encode variables clauses) =
      TraceData.encode (Search.traceValue variables clauses (MatchingLoop.fullTable variables clauses)) :=
  CutTrace.polynomial_canonical variables clauses

#print axioms CutTrace.packet_bound
#print axioms CutTrace.packFuel_bound
#print axioms CutTrace.sourceSteps_bound
#print axioms CutTrace.padded_run
#print axioms CutTrace.acceptsWithin
#print axioms CutTrace.polynomial_program
#print axioms CutTrace.polynomial_output
#print axioms CutTrace.polynomial_accepts
#print axioms CutTrace.polynomial_output_length
#print axioms CutTrace.polynomial_canonical
#print axioms CutTrace.machine_canonical

end PNP.Concrete.NormalizerBlocks
