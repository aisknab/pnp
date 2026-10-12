import PNP.Concrete.NormalizerRecoveryBit
namespace PNP.Concrete.NormalizerBlocks
example : Recovery.bitValue [] [] [⟨false,0⟩] [true] 0 = true := rfl
example : Recovery.bitValue [] [] [⟨false,0⟩] [true] 1 = false := rfl
example : Recovery.bitValue [] [] [⟨false,4⟩] [] 4 = false := rfl
#print axioms Recovery.frame_fields
#print axioms Recovery.dense_exec
#print axioms Recovery.denseFuel_bound
#print axioms Recovery.dense_canonical
#print axioms Recovery.chooseBit_exec
#print axioms Recovery.bit_exec
#print axioms Recovery.bit_frame
#print axioms Recovery.bit_fields
#print axioms Recovery.bitFuel_bound
#print axioms Recovery.bit_canonical
end PNP.Concrete.NormalizerBlocks
