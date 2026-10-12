import PNP.Concrete.NANDFrontendClause

namespace PNP.Concrete.NANDFrontend

private def clauseProgram (first second third : Operand × Bool) : BitRegister.Program 9 :=
  ⟨clauseCode 0 first second third 31 ++ [.accept], 0, 0, 8⟩

private theorem clauseProgram_segment (first second third : Operand × Bool) :
    Segment (clauseProgram first second third) 0 (clauseCode 0 first second third 31) := by
  intro offset inside
  simp only [clauseProgram, Nat.zero_add]
  exact lookup_append_left _ _ offset inside

example (first second third : Operand × Bool) (r : Registers) :
    BitRegister.run (clauseProgram first second third) (clauseFuel first second third r) (r.state 0) =
      ({r with temp := [], reversed := (clauseBits first second third r).reverse ++ r.reversed}).state 31 :=
  clause_run _ 0 31 first second third r (clauseProgram_segment first second third)
example (r : Registers) :
    BitRegister.run (clauseProgram (.left, false) (.right, true) (.gate, false))
        (4 * r.left.length + 4 * r.right.length + 4 * r.gate.length + 22) (r.state 0) =
      ({r with temp := [], reversed :=
        (threeBits ⟨false, r.left.length⟩ ⟨true, r.right.length⟩ ⟨false, r.gate.length⟩).reverse ++ r.reversed}).state 31 :=
  clause_run _ 0 31 (.left, false) (.right, true) (.gate, false) r
    (clauseProgram_segment (.left, false) (.right, true) (.gate, false))
example (operand : Operand) (positive : Bool) (r : Registers) :
    BitRegister.run (clauseProgram (operand, positive) (operand, positive) (operand, positive))
        (12 * (operand.value r).length + 22) (r.state 0) =
      ({r with temp := [], reversed :=
        (encodeTokenPairs (encodeClauseTokens (unitClause (operand.value r).length positive))).reverse ++ r.reversed}).state 31 :=
  unit_run _ 0 31 operand positive r (clauseProgram_segment (operand, positive) (operand, positive) (operand, positive))
example (first second third : Operand × Bool) (r : Registers) :
    (BitRegister.run (clauseProgram first second third) (clauseFuel first second third r) (r.state 0)).store.get 0 =
      r.input := by
  rw [clause_run _ 0 31 first second third r (clauseProgram_segment first second third)]
  rfl
example (first second third : Operand × Bool) (r : Registers) :
    (BitRegister.run (clauseProgram first second third) (clauseFuel first second third r) (r.state 0)).store.get 8 =
      r.output := by
  rw [clause_run _ 0 31 first second third r (clauseProgram_segment first second third)]
  rfl

#print axioms Segment.head
#print axioms Segment.tail
#print axioms clause_segments
#print axioms clause_run
#print axioms unit_run

end PNP.Concrete.NANDFrontend
