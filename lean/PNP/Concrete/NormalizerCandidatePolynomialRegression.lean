import PNP.Concrete.NormalizerCandidatePolynomial

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) :
    CandidatePacket.sourceSteps input + 1 ≤ CandidatePacket.sourceFuel.eval input.length :=
  CandidatePacket.sourceSteps_bound input
example (input : BitString) :
    boundedDecide (BitRegister.CompilerIO.rawMachine CandidatePacket.program)
      ((BitRegister.CompilerIO.runtimePolynomial 13 CandidatePacket.sourceFuel).eval input.length) input = .accept :=
  CandidatePacket.polynomial_accepts input
example (input : BitString) :
    (CandidatePacket.polynomial.output input).length ≤ input.length + CandidatePacket.sourceFuel.eval input.length :=
  CandidatePacket.polynomial_output_length input
example (count : Nat) (matching seen : MatchingTable.Entries) :
    CandidatePacket.polynomial.output (CandidatePacket.encode count matching seen) =
      TableOwner.answer (Candidate.selectFrom matching seen count 0) :=
  CandidatePacket.polynomial_canonical count matching seen
example :
    CandidatePacket.polynomial.output (CandidatePacket.encode 0 [] []) = [false] := by
  rw [CandidatePacket.polynomial_canonical]
  rfl

#print axioms CandidatePacket.sourceFuel_eval
#print axioms CandidatePacket.block_exec
#print axioms CandidatePacket.initial_registers
#print axioms CandidatePacket.closed_run
#print axioms CandidatePacket.sourceSteps_bound
#print axioms CandidatePacket.padded_run
#print axioms CandidatePacket.acceptsWithin
#print axioms CandidatePacket.polynomial_program
#print axioms CandidatePacket.polynomial_output
#print axioms CandidatePacket.polynomial_accepts
#print axioms CandidatePacket.polynomial_output_length
#print axioms CandidatePacket.polynomial_canonical
#print axioms CandidatePacket.machine_canonical

end PNP.Concrete.NormalizerBlocks
