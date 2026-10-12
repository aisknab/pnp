import PNP.Concrete.NormalizerPairPhase
namespace PNP.Concrete.NormalizerBlocks
def pairPhaseFixture : PathPairs.State := ⟨Occurrence.initialRegisters [], PathData.encode [⟨false,1⟩,⟨true,0⟩], [], [true,true,true]⟩
example : (PathPairs.phaseResult pairPhaseFixture).core.output = TableBatch.encodeUpdates [(0,1)] := by decide
example : (PathPairs.phaseResult {pairPhaseFixture with pending := []}).core.output = [] := by decide
#print axioms PathPairs.finish_exec
#print axioms PathPairs.finished_output
#print axioms PathPairs.front_exec
#print axioms PathPairs.frontFuel_bound
#print axioms PathPairs.phase_exec
#print axioms PathPairs.phaseFuel_bound
#print axioms PathPairs.phase_canonical
end PNP.Concrete.NormalizerBlocks
