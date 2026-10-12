import PNP.Concrete.NANDFrontendUnary

namespace PNP.Concrete.NANDFrontend

private def program : BitRegister.Program 9 := ⟨unaryCode 0 .left 46 47 ++ [.accept, .reject], 0, 0, 4⟩
private theorem placed : Segment program 0 (unaryCode 0 .left 46 47) := by
  intro offset inside
  simp only [program, Nat.zero_add]
  exact lookup_append_left _ _ offset inside

example : (unaryCode 0 .left 46 47).length = 46 := rfl
example : (unaryScan []).valid = false := rfl
example : (unaryScan [false, false, true, false]).valid = true := rfl
example : (unaryScan [false, false, true]).valid = false := rfl
example : (unaryScan [false, false, true, true]).valid = false := rfl
example : (unaryScan [false, false, false, true]).added = 1 := rfl
example : (unaryScan [false, false, false, true]).valid = false := rfl
example (n : Nat) (suffix : BitString) :
    unaryScan (LockedNAND.encodeTokens (LockedNAND.encodeNatTokens n) ++ suffix) =
      ⟨9 * n + 8, suffix, n, true⟩ := unaryScan_canonical n suffix
example (input : BitString) : (unaryScan input).fuel ≤ 3 * input.length + 1 :=
  (unaryScan_bounds input).1
example (r : Registers) (input : BitString) :
    BitRegister.run program (unaryScan input).fuel ({r with input := input}.state 0) =
      (unaryResultRegisters .left r (unaryScan input)).state
        (readerExit (unaryScan input).valid 46 47) :=
  unary_run program 0 .left 46 47 r input placed

#print axioms Operand.value_write
#print axioms Operand.write_value
#print axioms Operand.write_write
#print axioms Operand.write_input
#print axioms Operand.value_input
#print axioms unaryCode_length
#print axioms unaryCode_tree
#print axioms unary_unit
#print axioms unary_run
#print axioms unaryScan_bounds
#print axioms unaryScan_success_consumes
#print axioms unaryScan_canonical

end PNP.Concrete.NANDFrontend
