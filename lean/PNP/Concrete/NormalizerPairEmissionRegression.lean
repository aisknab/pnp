import PNP.Concrete.NormalizerPairEmission
namespace PNP.Concrete.NormalizerBlocks
def pairEmitFixture : PathPairs.State :=
  ⟨{Occurrence.initialRegisters [] with target := [true,true]}, [], [true], [true,false]⟩
example : (PathPairs.emitted pairEmitFixture).buffer = (TableBatch.encodePair 2 1 []).reverse ++ [true,false] := by decide
example : (PathPairs.emitted pairEmitFixture).pending = [] := by decide
example : PathPairs.emitFuel pairEmitFixture = 17 := by decide
#print axioms PathPairs.startEmission_exec
#print axioms PathPairs.prepend_exec
#print axioms PathPairs.startValue_exec
#print axioms PathPairs.saveEmission_exec
#print axioms PathPairs.emit_exec
#print axioms PathPairs.emitted_buffer
#print axioms PathPairs.emitted_pending
#print axioms PathPairs.emitted_canonical
#print axioms PathPairs.processPair_exec
#print axioms PathPairs.pairProcessed_canonical
end PNP.Concrete.NormalizerBlocks
