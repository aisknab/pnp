import PNP.Concrete.NormalizerPairReader
namespace PNP.Concrete.NormalizerBlocks
example : PathPairs.value [⟨false, 2⟩, ⟨true, 3⟩, ⟨false, 0⟩, ⟨true, 1⟩] = [(3,2),(1,0)] := by decide
example : PathPairs.value [⟨true, 2⟩, ⟨false, 3⟩] = [] := by decide
example : PathPairs.value [⟨false, 2⟩] = [] := by decide
example : PathPairs.value [⟨false, 2⟩, ⟨false, 1⟩, ⟨true, 0⟩] = [] := by decide
#print axioms PathPairs.pair_reverse
#print axioms PathPairs.liftCore_exec
#print axioms PathPairs.readHeader_exec
#print axioms PathPairs.readFirst_exec
#print axioms PathPairs.readSecond_exec
#print axioms PathPairs.firstRead_canonical
#print axioms PathPairs.secondRead_canonical
end PNP.Concrete.NormalizerBlocks
