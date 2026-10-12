import PNP.Concrete.NormalizerClauseCanonical

namespace PNP.Concrete.NormalizerBlocks

open BitRegister

example (target index : Nat) (clauses : List (List CNFLiteral)) :
    ClauseQuery.polynomial.output (ClauseQuery.encodeQuery target index clauses) =
      Occurrence.encodeQuery target (clauses[index]?.getD []) :=
  ClauseQuery.polynomial_canonical target index clauses
example (target index : Nat) (clauses : List (List CNFLiteral)) :
    machineOutput (CompilerIO.rawMachine ClauseQuery.program)
      ((CompilerIO.runtimePolynomial 9 ClauseQuery.sourceFuel).eval (ClauseQuery.encodeQuery target index clauses).length)
      (ClauseQuery.encodeQuery target index clauses) =
      Occurrence.encodeQuery target (clauses[index]?.getD []) :=
  ClauseQuery.machine_canonical target index clauses
example (target index : Nat) :
    ClauseQuery.polynomial.output (ClauseQuery.encodeQuery target index []) = Occurrence.encodeQuery target [] := by
  rw [ClauseQuery.polynomial_canonical]
  rfl
example : ClauseQuery.polynomial.output (ClauseQuery.encodeQuery 1 2 [[⟨false, 2⟩], [], [⟨true, 1⟩, ⟨false, 1⟩]]) =
    Occurrence.encodeQuery 1 [⟨true, 1⟩, ⟨false, 1⟩] := by rw [ClauseQuery.polynomial_canonical]; rfl
example : ClauseQuery.polynomial.output (ClauseQuery.encodeQuery 1 3 [[⟨false, 2⟩], [], [⟨true, 1⟩]]) =
    Occurrence.encodeQuery 1 [] := by rw [ClauseQuery.polynomial_canonical]; rfl

#print axioms ClauseQuery.canonical_block_exec
#print axioms ClauseQuery.packed_canonical
#print axioms ClauseQuery.polynomial_canonical
#print axioms ClauseQuery.machine_canonical

end PNP.Concrete.NormalizerBlocks
