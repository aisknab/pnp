import PNP.Concrete.NormalizerPathPhase
namespace PNP.Concrete.NormalizerBlocks
def pathPhaseFixture : TracePath.State :=
  ⟨{ParentQuery.initial [] with pending := [], targetIndex := [true], output := [true]}, [true, false], [true]⟩
example : (TracePath.phaseResult pathPhaseFixture).registers.output = PathData.answer none := by decide
example : (TracePath.pathReset pathPhaseFixture).buffer = [] := by decide
#print axioms TracePath.resetPath_exec
#print axioms TracePath.front_exec
#print axioms TracePath.phase_exec
#print axioms TracePath.frontFuel_bound
#print axioms TracePath.phaseFuel_bound
#print axioms TracePath.phase_preserves
#print axioms TracePath.phase_canonical
end PNP.Concrete.NormalizerBlocks
