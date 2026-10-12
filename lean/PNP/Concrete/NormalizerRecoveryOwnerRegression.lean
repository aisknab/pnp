import PNP.Concrete.NormalizerRecoveryOwner
namespace PNP.Concrete.NormalizerBlocks
example (r : Recovery.State) : Recovery.ownerWord .selected r = r.variables := rfl
example (r : Recovery.State) : Recovery.ownerWord .matching r = r.matching := rfl
example : TableOwner.answer (some 0) ≠ TableOwner.answer none := by decide
#print axioms Recovery.lift_exec
#print axioms Recovery.loadOwner_exec
#print axioms Recovery.prepareOwner_exec
#print axioms Recovery.owner_exec
#print axioms Recovery.owned_data
#print axioms Recovery.owned_frame
#print axioms Recovery.ownerFuel_bound
#print axioms Recovery.owned_output_bound
#print axioms Recovery.owned_matching
#print axioms Recovery.owned_selected
end PNP.Concrete.NormalizerBlocks
