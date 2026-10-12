import PNP.Concrete.NormalizerOccurrenceCanonical

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example (target : Nat) (clause : List CNFLiteral) :
    Occurrence.polynomial.output (Occurrence.encodeQuery target clause) =
      Occurrence.answer (clause.find? (fun literal => literal.variableIndex == target)) :=
  Occurrence.polynomial_canonical target clause
example (target : Nat) (clause : List CNFLiteral) :
    machineOutput (CompilerIO.rawMachine Occurrence.program)
      ((CompilerIO.runtimePolynomial 9 Occurrence.sourceFuel).eval (Occurrence.encodeQuery target clause).length)
      (Occurrence.encodeQuery target clause) =
      Occurrence.answer (clause.find? (fun literal => literal.variableIndex == target)) :=
  Occurrence.machine_canonical target clause
example (target : Nat) (clause : List CNFLiteral) :
    (Occurrence.polynomial.output (Occurrence.encodeQuery target clause)).length ≤ 2 :=
  Occurrence.polynomial_canonical_length target clause
example : Occurrence.polynomial.output (Occurrence.encodeQuery 0 [⟨false, 0⟩, ⟨true, 0⟩]) = [true, false] := by
  rw [Occurrence.polynomial_canonical]
  rfl
example : Occurrence.polynomial.output (Occurrence.encodeQuery 3 [⟨true, 2⟩, ⟨false, 3⟩]) = [true, false] := by
  rw [Occurrence.polynomial_canonical]
  rfl
example : Occurrence.polynomial.output (Occurrence.encodeQuery 2 [⟨true, 1⟩, ⟨false, 3⟩]) = [false] := by
  rw [Occurrence.polynomial_canonical]
  rfl
example (target : Nat) : Occurrence.polynomial.output (Occurrence.encodeQuery target []) = [false] := by
  rw [Occurrence.polynomial_canonical]
  rfl

#print axioms Occurrence.header_canonical
#print axioms Occurrence.canonical_block_exec
#print axioms Occurrence.polynomial_canonical
#print axioms Occurrence.machine_canonical
#print axioms Occurrence.polynomial_canonical_length

end PNP.Concrete.NormalizerBlocks
