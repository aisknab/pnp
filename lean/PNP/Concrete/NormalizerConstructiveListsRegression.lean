import PNP.Concrete.NormalizerConstructiveLists

namespace PNP.Concrete.NormalizerBlocks

example : ([2, 1, 2] : List (Fin 4)).idxOf 2 = 0 := by decide
example : ([2, 1, 2] : List (Fin 4)).idxOf 1 = 1 := by decide
example (n : Nat) (xs : List (Fin n)) (x : Fin n) (h : x ∈ xs) :
    xs.idxOf x < xs.length := ConstructiveLists.finiteIndexBound xs x h

#print axioms ConstructiveLists.finiteLawful
#print axioms ConstructiveLists.lookup
#print axioms ConstructiveLists.indexBound
#print axioms ConstructiveLists.finiteIndexBound

end PNP.Concrete.NormalizerBlocks
