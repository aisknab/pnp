import PNP.Concrete.NormalizerRecoveryPreferred
namespace PNP.Concrete.NormalizerBlocks
example : Recovery.preferredValue [] [] 0 = false := rfl
example : Recovery.literalValue [[⟨true,0⟩,⟨false,0⟩]] 0 0 = true := rfl
example : Recovery.literalValue [[⟨false,0⟩,⟨true,0⟩]] 0 0 = false := rfl
#print axioms Recovery.prepareOccurrence_exec
#print axioms Recovery.occurrence_exec
#print axioms Recovery.sign_exec
#print axioms Recovery.literal_exec
#print axioms Recovery.literalFuel_bound
#print axioms Recovery.literal_canonical
#print axioms Recovery.choosePreferred_exec
#print axioms Recovery.preferred_exec
#print axioms Recovery.preferred_frame
#print axioms Recovery.preferredFuel_bound
#print axioms Recovery.preferred_canonical
end PNP.Concrete.NormalizerBlocks
