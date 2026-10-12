import PNP.Concrete.NormalizerSeenEmission
namespace PNP.Concrete.NormalizerBlocks
def seenEmissionFixture (node : CNFLiteral) : SeenTrace.State :=
  ⟨{ParentQuery.initial [] with pending := TraceData.row (node, some ⟨false, 7⟩) [true, false]}, [], []⟩
example : (SeenTrace.bodyResult (seenEmissionFixture ⟨true, 0⟩)).buffer = (SeenTrace.entryBytes none).reverse := by decide
example : (SeenTrace.bodyResult (seenEmissionFixture ⟨false, 2⟩)).buffer = (SeenTrace.entryBytes (some 2)).reverse := by decide
example : (SeenTrace.bodyResult (seenEmissionFixture ⟨false, 2⟩)).core.pending = [true, false] := by decide
#print axioms SeenTrace.appendEntry_exec
#print axioms SeenTrace.entryAppended_buffer
#print axioms SeenTrace.entryAppended_preserves
#print axioms SeenTrace.body_exec
#print axioms SeenTrace.body_pending
#print axioms SeenTrace.body_shorter
#print axioms SeenTrace.bodyFuel_bound
#print axioms SeenTrace.stepBound_mono
#print axioms SeenTrace.body_preserves
#print axioms SeenTrace.body_canonical
end PNP.Concrete.NormalizerBlocks
