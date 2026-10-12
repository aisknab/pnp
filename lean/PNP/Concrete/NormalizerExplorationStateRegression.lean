import PNP.Concrete.NormalizerExplorationState

namespace PNP.Concrete.NormalizerBlocks
open Exploration
def explorationStateFixture : State :=
  ⟨Extraction.loaded (Extraction.encode [] [none] [] [⟨false, 2⟩, ⟨true, 0⟩]), [true, true]⟩
example : (prepared explorationStateFixture).remaining = [true, true] := by decide
example : (begun explorationStateFixture).remaining = [true, true] := by decide
example : (begun explorationStateFixture).core.parent.output = [true, false] := by decide
example : (begun explorationStateFixture).core.skipped = (UnseenData.entry ⟨false, 2⟩).reverse := by decide

#print axioms Exploration.lift_exec
#print axioms Exploration.liftCore_exec
#print axioms Exploration.prepareCore_exec
#print axioms Exploration.begin_exec
#print axioms Exploration.begun_fields
#print axioms Exploration.begun_range
#print axioms Exploration.begun_outcome
#print axioms Exploration.beginFuel_bound

end PNP.Concrete.NormalizerBlocks
