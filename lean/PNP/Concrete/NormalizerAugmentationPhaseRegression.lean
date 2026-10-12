import PNP.Concrete.NormalizerAugmentationPhase
namespace PNP.Concrete.NormalizerBlocks
def augmentationFixture (xs : List CNFLiteral) : Augmentation.State :=
  ⟨⟨Occurrence.initialRegisters [], PathData.encode xs, MatchingTable.encode [none,none], []⟩, []⟩
example : (Augmentation.phaseResult (augmentationFixture [⟨false,0⟩,⟨true,1⟩])).pairs.core.output =
    MatchingTable.encode [none,some 0] := by decide
example : (Augmentation.phaseResult (augmentationFixture [⟨false,0⟩,⟨true,1⟩,⟨false,2⟩,⟨true,1⟩])).pairs.core.output =
    MatchingTable.encode [none,some 2] := by decide
example : (Augmentation.phaseResult (augmentationFixture [⟨true,0⟩])).pairs.core.output =
    MatchingTable.encode [none,none] := by decide
#print axioms Augmentation.liftPairs_exec
#print axioms Augmentation.liftBatch_exec
#print axioms Augmentation.derivePairs_exec
#print axioms Augmentation.prepareBatch_exec
#print axioms Augmentation.applyUpdates_exec
#print axioms Augmentation.finish_exec
#print axioms Augmentation.prepare_exec
#print axioms Augmentation.phase_exec
#print axioms Augmentation.phase_canonical
end PNP.Concrete.NormalizerBlocks
