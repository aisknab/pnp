import PNP.Concrete.NormalizerExplorationStep

namespace PNP.Concrete.NormalizerBlocks
open Exploration
def explorationStepFixture : State :=
  ⟨Extraction.loaded (Extraction.encode [] [none] [] [⟨false, 2⟩, ⟨true, 0⟩]), [true, true]⟩
example : (bodyResult explorationStepFixture).remaining = [true] := by decide
example : (bodyResult explorationStepFixture).core.pending = SearchVertices.encodeVertices [⟨false, 2⟩] := by decide
example : (bodyResult explorationStepFixture).core.trace = TraceData.encode [(⟨true, 0⟩, none)] := by decide
example : (bodyResult ⟨Extraction.loaded
    (Extraction.encode [] [some 0] [] [⟨true, 0⟩]), [true, true]⟩).remaining = [] := by decide
example : (bodyResult ⟨Extraction.loaded
    (Extraction.encode [[⟨true, 2⟩]] [none] [(⟨true, 0⟩, none)] [⟨false, 2⟩]), [true]⟩).core.trace =
    TraceData.encode [(⟨false, 2⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] := by decide

#print axioms Exploration.stop_exec
#print axioms Exploration.choose_exec
#print axioms Exploration.body_exec
#print axioms Exploration.body_preserves
#print axioms Exploration.body_progress
#print axioms Exploration.body_range
#print axioms Exploration.body_none
#print axioms Exploration.body_some

end PNP.Concrete.NormalizerBlocks
