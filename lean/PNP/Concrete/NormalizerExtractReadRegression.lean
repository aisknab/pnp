import PNP.Concrete.NormalizerExtractRead

namespace PNP.Concrete.NormalizerBlocks
open Extraction

def extractionReadFixture (input : BitString) : State :=
  ⟨Eligibility.initial [], input, [true, false], [false, true], [true], []⟩
example : (vertexRead (extractionReadFixture [])).pending = [] := by decide
example : (vertexRead (extractionReadFixture (SearchVertices.encodeVertices [⟨true, 3⟩, ⟨false, 7⟩]))).parent.targetIndex =
    [true, true, true] := by decide
example : (vertexRead (extractionReadFixture (SearchVertices.encodeVertices [⟨false, 0⟩, ⟨true, 2⟩]))).pending =
    SearchVertices.encodeVertices [⟨true, 2⟩] := by decide

#print axioms Extraction.liftCore_exec
#print axioms Extraction.prepareRead_exec
#print axioms Extraction.readPairs_exec
#print axioms Extraction.readSuffix_exec
#print axioms Extraction.readVertex_exec
#print axioms Extraction.readFuel_bound
#print axioms Extraction.read_fields
#print axioms Extraction.read_index_bound
#print axioms Extraction.read_progress
#print axioms Extraction.read_canonical

end PNP.Concrete.NormalizerBlocks
