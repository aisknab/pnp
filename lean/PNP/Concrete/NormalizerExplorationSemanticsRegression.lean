import PNP.Concrete.NormalizerExplorationSemantics

namespace PNP.Concrete.NormalizerBlocks
open Exploration
example : value [[⟨true, 2⟩]] [none] 4
    [⟨true, 0⟩, ⟨false, 0⟩, ⟨false, 1⟩, ⟨false, 2⟩] [] =
    [(⟨false, 2⟩, some ⟨true, 0⟩), (⟨true, 0⟩, none)] := by decide
example : value [[⟨true, 2⟩]] [none] 1 [⟨true, 0⟩, ⟨false, 2⟩] [] =
    [(⟨true, 0⟩, none)] := by decide
example : value [] [some 0] 2 [⟨true, 0⟩] [] = [] := by decide
example : value [] [] 0 [⟨true, 0⟩] [(⟨false, 3⟩, none)] =
    [(⟨false, 3⟩, none)] := by decide

#print axioms Exploration.scan_value
#print axioms Exploration.whole_value

end PNP.Concrete.NormalizerBlocks
