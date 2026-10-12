import PNP.Concrete.NormalizerSearchState
namespace PNP.Concrete.NormalizerBlocks
def searchStateFixture : Search.State := ⟨Exploration.initial [true, false], [false, true]⟩
example : searchStateFixture.store.get 28 = [false, true] := by decide
example : searchStateFixture.path.store.get 0 = [true, false] := by decide
example : searchStateFixture.candidate.store.get 0 = [true, false] := by decide
#print axioms Frame.core_bounded
#print axioms Search.liftExploration_exec
#print axioms Search.liftCore_exec
#print axioms Search.liftPath_exec
#print axioms Search.path_bounded
#print axioms Search.liftCandidate_exec
#print axioms Search.candidate_bounded
#print axioms Search.path_frame
#print axioms Search.candidate_frame
end PNP.Concrete.NormalizerBlocks
