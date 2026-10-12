import PNP.Concrete.NormalizerExtractFinish

namespace PNP.Concrete.NormalizerBlocks
open Extraction
def extractionFinishFixture (clauses : List (List CNFLiteral)) (trace : List TraceData.Row) (vertices : List CNFLiteral) : State :=
  ⟨⟨ParentQuery.loaded (ParentQuery.encode ⟨false, 0⟩ clauses [none] []), []⟩,
    SearchVertices.encodeVertices vertices, [], TraceData.encode trace, [true], []⟩
example : (phaseResult (extractionFinishFixture [] [] [⟨false, 2⟩, ⟨true, 0⟩, ⟨false, 7⟩])).output =
    answer (some ((⟨true, 0⟩, none), [⟨false, 2⟩, ⟨false, 7⟩])) := by decide
example : (phaseResult (extractionFinishFixture [[⟨true, 2⟩]] [(⟨true, 0⟩, none)] [⟨true, 0⟩, ⟨false, 2⟩])).output =
    answer (some ((⟨false, 2⟩, some ⟨true, 0⟩), [⟨true, 0⟩])) := by decide
example : (phaseResult (extractionFinishFixture [] [] [⟨false, 2⟩])).output = answer none := by decide

#print axioms Extraction.packVertex_exec
#print axioms Extraction.vertexPacked_output
#print axioms Extraction.finishSome_exec
#print axioms Extraction.someFinished_output
#print axioms Extraction.finishSomeFuel_bound
#print axioms Extraction.finish_exec
#print axioms Extraction.finished_output
#print axioms Extraction.finishFuel_bound
#print axioms Extraction.phase_exec
#print axioms Extraction.phase_canonical

end PNP.Concrete.NormalizerBlocks
