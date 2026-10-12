import PNP.Concrete.NormalizerCutTrace

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) :
    BitRegister.run CutTrace.program (CutTrace.sourceSteps input + 1)
      (BitRegister.initial CutTrace.program input) = ⟨.accepted, (CutTrace.result input).store⟩ :=
  CutTrace.closed_run input

example (variables : Nat) (clauses : List (List CNFLiteral)) :
    (CutTrace.result (MatchingDriver.encode variables clauses)).table =
      MatchingTable.encode (MatchingLoop.fullTable variables clauses) :=
  CutTrace.result_matching variables clauses

#print axioms MatchingDriver.result_frame
#print axioms MatchingDriver.result_within
#print axioms MatchingDriver.result_data
#print axioms CutTrace.exploreCore_exec
#print axioms CutTrace.block_exec
#print axioms CutTrace.closed_run
#print axioms CutTrace.packet_canonical
#print axioms CutTrace.result_canonical
#print axioms CutTrace.result_matching

end PNP.Concrete.NormalizerBlocks
