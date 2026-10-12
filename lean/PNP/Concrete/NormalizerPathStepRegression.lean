import PNP.Concrete.NormalizerPathStep
namespace PNP.Concrete.NormalizerBlocks
def pathStepFixture : TracePath.State :=
  ⟨{ParentQuery.initial [] with pending := TraceData.row (⟨false, 2⟩, some ⟨true, 1⟩) [true, false], targetIndex := [true, true], targetTag := [false], output := [false]}, [], []⟩
example : (TracePath.bodyResult pathStepFixture).core.pending = [true, false] := by decide
example : (TracePath.bodyResult pathStepFixture).core.targetIndex = [true] := by decide
example : (TracePath.bodyResult pathStepFixture).core.output = [false] := by decide
example : (TracePath.bodyResult pathStepFixture).buffer = [false, true, true, false] := by decide
#print axioms TracePath.acceptNode_exec
#print axioms TracePath.decideNode_exec
#print axioms TracePath.body_exec
#print axioms TracePath.accepted_pending
#print axioms TracePath.body_progress
#print axioms TracePath.bodyFuel_bound
#print axioms TracePath.stepBound_mono
#print axioms TracePath.body_preserves
end PNP.Concrete.NormalizerBlocks
