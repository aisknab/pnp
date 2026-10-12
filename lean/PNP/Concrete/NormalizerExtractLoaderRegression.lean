import PNP.Concrete.NormalizerExtractLoader

namespace PNP.Concrete.NormalizerBlocks
open Extraction
example : (loaded (encode [[⟨true, 2⟩]] [none] [(⟨true, 0⟩, none)] [⟨false, 2⟩])).pending =
    SearchVertices.encodeVertices [⟨false, 2⟩] := by decide
example : (loaded (encode [] [] [] [])).parent.output = [false] := by decide
example : (loaded (encode [] [] [] [])).active = [true] := by decide
example : (loaded [true, true, false, true]).pending = [] := by decide

#print axioms Extraction.loadData_exec
#print axioms Extraction.defaultAnswer_exec
#print axioms Extraction.loaded_fields
#print axioms Extraction.loader_exec
#print axioms Extraction.loader_cursors
#print axioms Extraction.loaded_size
#print axioms Extraction.loaderFuel_bound
#print axioms Extraction.loaded_canonical

end PNP.Concrete.NormalizerBlocks
