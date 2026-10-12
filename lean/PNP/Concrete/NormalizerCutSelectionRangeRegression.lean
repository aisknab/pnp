import PNP.Concrete.NormalizerCutSelectionRange
namespace PNP.Concrete.NormalizerBlocks
example (r : CutSelection.State) (tag : Bool) : (CutSelection.run tag [] r).fuel = 1 := rfl
example (r : CutSelection.State) (tag : Bool) (bits : BitString) :
    (CutSelection.run tag bits r).state.remaining = [] := CutSelection.run_stopped tag bits r
#print axioms CutSelection.run_exec
#print axioms CutSelection.run_trace
#print axioms CutSelection.run_tag
#print axioms CutSelection.run_stopped
#print axioms CutSelection.run_index_length
#print axioms CutSelection.run_fuel_bound
#print axioms CutSelection.whole_exec
#print axioms CutSelection.whole_fuel_bound
end PNP.Concrete.NormalizerBlocks
