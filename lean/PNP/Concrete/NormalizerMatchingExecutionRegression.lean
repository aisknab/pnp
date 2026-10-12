import PNP.Concrete.NormalizerMatchingExecution
namespace PNP.Concrete.NormalizerBlocks
example (input : BitString) :
    (BitRegister.run MatchingDriver.program (MatchingDriver.sourceSteps input + 1)
      (BitRegister.initial MatchingDriver.program input)).control = .accepted := by
  rw [MatchingDriver.closed_run]
example (v : Nat) (cs : List (List CNFLiteral)) :
    (MatchingDriver.result (MatchingDriver.encode v cs)).registers.output =
      MatchingTable.encode (MatchingLoop.fullTable v cs) := MatchingDriver.result_canonical v cs
#print axioms MatchingDriver.finish_exec
#print axioms MatchingDriver.finished_output
#print axioms MatchingDriver.block_exec
#print axioms MatchingDriver.initial_registers
#print axioms MatchingDriver.closed_run
#print axioms MatchingDriver.result_canonical
#print axioms MatchingDriver.program_canonical
end PNP.Concrete.NormalizerBlocks
