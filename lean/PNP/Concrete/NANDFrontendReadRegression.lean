import PNP.Concrete.NANDFrontendRead

namespace PNP.Concrete.NANDFrontend

private def probe := tokenTree 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
example : probe.size = 45 := rfl
example : probe.depth = 4 := rfl
example : (probe.scan 99 [false, false, false, true]).address = 1 := rfl
example : (probe.scan 99 [false, false, true, false]).address = 2 := rfl
example : (probe.scan 99 [true, false, false, false]).address = 8 := rfl
example : (probe.scan 99 [true, false, true, true]).address = 11 := rfl
example : (probe.scan 99 [true, false]).address = 99 := rfl
example : (probe.scan 99 [true, false]).fuel = 5 := rfl
example (tail : BitString) :
    probe.scan 99 (true :: true :: false :: true :: tail) = ⟨8, tail, 13⟩ := by
  simp only [probe, tokenTree, ReadTree.scan, Bool.false_eq_true, ↓reduceIte]
example (tree : ReadTree) (failure : Nat) (input : BitString) :
    (tree.scan failure input).rest.length ≤ input.length := tree.scan_rest_le failure input
example (tree : ReadTree) (failure : Nat) (input : BitString) :
    (tree.scan failure input).fuel ≤ 2 * tree.depth := tree.scan_fuel_le failure input

#print axioms ReadTree.code_length
#print axioms ReadTree.scan_rest_le
#print axioms ReadTree.scan_fuel_le
#print axioms ReadTree.run
#print axioms tokenTree_size
#print axioms tokenTree_depth

end PNP.Concrete.NANDFrontend
