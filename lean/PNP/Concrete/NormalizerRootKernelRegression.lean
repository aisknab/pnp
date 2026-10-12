import PNP.Concrete.NormalizerRootKernel

namespace PNP.Concrete.NormalizerBlocks

example (input : BitString) : RootKernel.sourceSteps input + 1 ≤ 339 * input.length + 622 :=
  RootKernel.sourceSteps_bound input
example (index : Nat) (entries : MatchingTable.Entries) :
    (RootKernel.result (MatchingRead.encodeQuery index entries)).output = [(MatchingTable.read entries index).isNone] :=
  RootKernel.result_canonical index entries
example : (RootKernel.result (MatchingRead.encodeQuery 1 [some 2, none])).output = [true] := by
  rw [RootKernel.result_canonical]
  rfl
example : (RootKernel.result (MatchingRead.encodeQuery 0 [some 2, none])).output = [false] := by
  rw [RootKernel.result_canonical]
  rfl

#print axioms RootKernel.block_exec
#print axioms RootKernel.sourceSteps_bound
#print axioms RootKernel.result_output
#print axioms RootKernel.result_canonical

end PNP.Concrete.NormalizerBlocks
