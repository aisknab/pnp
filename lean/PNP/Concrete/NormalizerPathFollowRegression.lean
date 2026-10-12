import PNP.Concrete.NormalizerPathFollow
namespace PNP.Concrete.NormalizerBlocks
def pathFollowFixture : TracePath.State :=
  ⟨{ParentQuery.initial [] with pending := [false, true], output := [false]}, [true], TraceData.predecessor (some ⟨true, 3⟩) [true, false]⟩
example : (TracePath.parentFollowed pathFollowFixture).core.pending = [false, true] := by decide
example : (TracePath.parentFollowed pathFollowFixture).core.targetIndex = [true, true, true] := by decide
example : ForwardEdge.present (TracePath.parentFollowed pathFollowFixture).core.targetTag = true := by decide
example : (TracePath.rootFinished pathFollowFixture).core.pending = [] := by decide
example : (TracePath.rootFinished pathFollowFixture).core.output = [true] := by decide
#print axioms TracePath.followParent_exec
#print axioms TracePath.followFuel_bound
#print axioms TracePath.parentFollowed_preserves
#print axioms TracePath.parentFollowed_canonical
#print axioms TracePath.finishRoot_exec
#print axioms TracePath.choosePredecessor_exec
#print axioms TracePath.predecessorFuel_bound
end PNP.Concrete.NormalizerBlocks
