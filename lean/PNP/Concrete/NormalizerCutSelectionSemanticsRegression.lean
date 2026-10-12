import PNP.Concrete.NormalizerCutSelectionSemantics
namespace PNP.Concrete.NormalizerBlocks
example : CutSelection.selected true
    [(⟨true,2⟩,none),(⟨false,1⟩,some ⟨true,1⟩),(⟨true,0⟩,none),(⟨true,2⟩,none)] 3 0 =
    [⟨true,0⟩,⟨true,2⟩] := by decide
example : CutSelection.selected false [(⟨true,0⟩,some ⟨false,0⟩)] 1 0 = [] := by decide
example (tag : Bool) (trace : List TraceData.Row) (index : Nat) :
    CutSelection.selected tag trace 0 index = [] := rfl
#print axioms CutSelection.selectedBits_succ
#print axioms CutSelection.selected_finRange
#print axioms CutSelection.selected_length
#print axioms CutSelection.run_buffer
#print axioms CutSelection.whole_buffer
end PNP.Concrete.NormalizerBlocks
