import PNP.Concrete.NormalizerOutputLoaderCanonical
namespace PNP.Concrete.NormalizerBlocks
example (F : CNFFormula) : (OutputLoader.originalHeader (NANDFrontend.recordData 0 F)).target = [] := by
  rw [OutputLoader.originalHeader_canonical]
  rfl
example (F : CNFFormula) (width : Nat) :
    (OutputLoader.originalHeader (NANDFrontend.recordData width F)).target.length = width := by
  rw [OutputLoader.originalHeader_canonical]
  exact List.length_replicate ..
example : OutputLoader.initial [] = OutputBranches.extend (CutDriver.initial []) [] := rfl
#print axioms OutputLoader.headers_result
#print axioms OutputLoader.frameInput_result
#print axioms OutputLoader.commitInput_result
#print axioms OutputLoader.loaded_result
#print axioms OutputLoader.loaded_initial
#print axioms OutputLoader.loader_exec
#print axioms OutputLoader.initial_bounded
#print axioms OutputLoader.originalHeader_canonical
#print axioms OutputLoader.frontendHeader_canonical
#print axioms OutputLoader.checkerInput_canonical
#print axioms OutputLoader.ready_canonical
end PNP.Concrete.NormalizerBlocks
