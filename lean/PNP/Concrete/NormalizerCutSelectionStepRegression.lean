import PNP.Concrete.NormalizerCutSelectionStep
namespace PNP.Concrete.NormalizerBlocks
example (r : CutSelection.State) (tag : Bool) :
    (CutSelection.stepped tag r).remaining = r.remaining.tail :=
  (CutSelection.stepped_frame tag r).2.1
example : TraceMember.value ⟨true,0⟩ [(⟨false,0⟩,some ⟨true,0⟩)] = false := by decide
#print axioms CutSelection.chosen_frame
#print axioms CutSelection.chooseFuel_bound
#print axioms CutSelection.advance_exec
#print axioms CutSelection.step_exec
#print axioms CutSelection.stepped_frame
#print axioms CutSelection.stepFuel_bound
#print axioms CutSelection.query_canonical
#print axioms CutSelection.stepped_buffer
end PNP.Concrete.NormalizerBlocks
