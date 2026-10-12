import PNP.Concrete.NormalizerExplorationRuntime

namespace PNP.Concrete.NormalizerBlocks
open Exploration
example : (scan 0 ⟨Extraction.loaded [], [true, true]⟩).fuel = 1 := by decide
example : (scan 3 ⟨Extraction.loaded [], []⟩).fuel = 1 := by decide
example : (whole ⟨Extraction.loaded (Extraction.encode [] [] [] []), [true]⟩).state.remaining = [] := by decide

#print axioms Exploration.scan_fuel_bound
#print axioms Exploration.whole_fuel_bound

end PNP.Concrete.NormalizerBlocks
