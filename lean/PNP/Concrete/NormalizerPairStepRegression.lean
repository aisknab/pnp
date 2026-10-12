import PNP.Concrete.NormalizerPairStep
namespace PNP.Concrete.NormalizerBlocks
def pairStepFixture (xs : List CNFLiteral) : PathPairs.State := ⟨Occurrence.initialRegisters [], PathData.encode xs, [], []⟩
example : (PathPairs.bodyResult (pairStepFixture [⟨false, 2⟩, ⟨true, 3⟩])).buffer = (TableBatch.encodePair 3 2 []).reverse := by decide
example : (PathPairs.bodyResult (pairStepFixture [⟨false, 2⟩, ⟨false, 3⟩])).buffer = [] := by decide
example : (PathPairs.bodyResult (pairStepFixture [⟨true, 0⟩])).pending = [] := by decide
#print axioms PathPairs.chooseSecond_exec
#print axioms PathPairs.processFirst_exec
#print axioms PathPairs.body_exec
#print axioms PathPairs.body_pending_bound
#print axioms PathPairs.body_shorter
#print axioms PathPairs.processFuel_first_bound
#print axioms PathPairs.bodyFuel_bound
#print axioms PathPairs.stepBound_mono
end PNP.Concrete.NormalizerBlocks
