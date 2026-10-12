/-
Copyright (c) 2026 PNP Labs.

Closed clause-root test for the alternating search graph. A clause is a root
exactly when its indexed matching entry is absent. Both table access and the
Boolean decision run as composed finite machines; no lookup result is given.
The graph controller must separately dispatch the variable-vertex case.
-/

import PNP.Concrete.NormalizerBooleanHead

namespace PNP.Concrete.NormalizerBlocks.MatchingRoot

def polynomial : PolynomialTimeFunction :=
  PolynomialTimeFunction.compose MatchingRead.polynomial (BooleanHead.polynomial false)

theorem polynomial_program :
    polynomial.program = .compose MatchingRead.polynomial.program (BooleanHead.polynomial false).program := rfl

private theorem output_projection (input : BitString) :
    polynomial.output input =
      (PolynomialTimeFunction.compose MatchingRead.polynomial (BooleanHead.polynomial false)).output input := rfl

theorem polynomial_output (input : BitString) :
    polynomial.output input = (BooleanHead.polynomial false).output (MatchingRead.polynomial.output input) := by
  rw [output_projection, PolynomialTimeFunction.compose_output]

theorem polynomial_canonical (index : Nat) (entries : MatchingTable.Entries) :
    polynomial.output (MatchingRead.encodeQuery index entries) = [(MatchingTable.read entries index).isNone] := by
  rw [polynomial_output, MatchingRead.polynomial_canonical, BooleanHead.absence_answer]

def rawRefinement : FunctionProgram.RawRefinement polynomial.program := by
  rw [polynomial_program]
  exact FunctionProgram.RawRefinement.compose MatchingRead.rawRefinement (BooleanHead.rawRefinement false)

theorem machine_output (input : BitString) :
    machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input =
      polynomial.output input :=
  rawRefinement.output_eq input (polynomial.haltsWithin input)

theorem machine_canonical (index : Nat) (entries : MatchingTable.Entries) :
    machineOutput rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size (MatchingRead.encodeQuery index entries)))
      (MatchingRead.encodeQuery index entries) = [(MatchingTable.read entries index).isNone] := by
  rw [machine_output, polynomial_canonical]

theorem machine_halts (input : BitString) :
    boundedDecide rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  rawRefinement.haltsWithin input (polynomial.haltsWithin input)

theorem machine_output_size (input : BitString) :
    BitString.size (machineOutput rawRefinement.machine (rawRefinement.timeBound.eval (BitString.size input)) input) ≤
      polynomial.outputSizeBound.eval (BitString.size input) :=
  FunctionProgram.RawRefinement.output_size_le polynomial rawRefinement input

end PNP.Concrete.NormalizerBlocks.MatchingRoot
