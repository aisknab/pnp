import PNP.Concrete.NANDFrontendLiteral

namespace PNP.Concrete.NANDFrontend

private def literalProgram (operand : Operand) (positive : Bool) : BitRegister.Program 9 :=
  ⟨literalCode 0 operand positive 9 ++ [.accept], 0, 0, 8⟩

private theorem literalProgram_segment (operand : Operand) (positive : Bool) :
    Segment (literalProgram operand positive) 0 (literalCode 0 operand positive 9) := by
  intro offset inside
  simp only [literalProgram, Nat.zero_add]
  exact lookup_append_left _ _ offset inside

example (program : BitRegister.Program 9) (base next : Nat) (first second : Bool) (r : Registers)
    (placed : Segment program base (pairCode base first second next)) :
    BitRegister.run program 2 (r.state base) =
      ({r with reversed := second :: first :: r.reversed}).state next :=
  pair_run program base next first second r placed
example (r : Registers) :
    BitRegister.run (literalProgram .left false) (4 * r.left.length + 6) (r.state 0) =
      ({r with temp := [], reversed := (literalBits false r.left.length).reverse ++ r.reversed}).state 9 :=
  literal_run (literalProgram .left false) 0 9 .left false r (literalProgram_segment .left false)
example (r : Registers) :
    BitRegister.run (literalProgram .right true) (4 * r.right.length + 6) (r.state 0) =
      ({r with temp := [], reversed := (literalBits true r.right.length).reverse ++ r.reversed}).state 9 :=
  literal_run (literalProgram .right true) 0 9 .right true r (literalProgram_segment .right true)
example (r : Registers) :
    BitRegister.run (literalProgram .gate true) (4 * r.gate.length + 6) (r.state 0) =
      ({r with temp := [], reversed := (literalBits true r.gate.length).reverse ++ r.reversed}).state 9 :=
  literal_run (literalProgram .gate true) 0 9 .gate true r (literalProgram_segment .gate true)
example (operand : Operand) (positive : Bool) (r : Registers) :
    (BitRegister.run (literalProgram operand positive) (4 * (operand.value r).length + 6)
      (r.state 0)).store.get 6 = [] := by
  rw [literal_run _ 0 9 operand positive r (literalProgram_segment operand positive)]
  rfl
example (operand : Operand) (positive : Bool) (r : Registers) :
    (BitRegister.run (literalProgram operand positive) (4 * (operand.value r).length + 6)
      (r.state 0)).store.get 0 = r.input := by
  rw [literal_run _ 0 9 operand positive r (literalProgram_segment operand positive)]
  rfl

#print axioms pair_run
#print axioms literal_start
#print axioms literal_loop_empty
#print axioms literal_loop_cons
#print axioms literal_loop
#print axioms literal_run

end PNP.Concrete.NANDFrontend
