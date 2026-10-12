import PNP.Concrete.NormalizerExplorationScan

namespace PNP.Concrete.NormalizerBlocks
open Exploration
def explorationScanFixture : State :=
  ⟨Extraction.loaded (Extraction.encode [[⟨true, 2⟩]] [none] []
    [⟨true, 0⟩, ⟨false, 0⟩, ⟨false, 1⟩, ⟨false, 2⟩]), [true, true, true, true]⟩
example : (whole explorationScanFixture).state.remaining = [] := by decide
example : (whole explorationScanFixture).state.core.trace =
    TraceData.encode [(⟨false, 2⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] := by decide
example : (whole ⟨explorationScanFixture.core, []⟩).state.core.trace = [] := by decide
example : (whole ⟨Extraction.loaded (Extraction.encode [] [] [] []), [false]⟩).state.core.trace = [] := by decide

#print axioms Exploration.State.get_remaining
#print axioms Exploration.body_shorter
#print axioms Exploration.scan_exec
#print axioms Exploration.scan_stopped
#print axioms Exploration.scan_preserves
#print axioms Exploration.whole_exec
#print axioms Exploration.whole_stopped

end PNP.Concrete.NormalizerBlocks
