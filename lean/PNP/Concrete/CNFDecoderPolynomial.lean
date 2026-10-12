/-
Copyright (c) 2026 PNP Labs.

An unconditional concrete polynomial-time implementation of the strict CNF
decoder. Its output is the explicit validity tag and finite formula-data record.
This is a parser, not a SAT solver or a complete normalization algorithm.
-/

import PNP.Concrete.CNFDecoderExecution
import PNP.Concrete.BitRegisterCompilerIOPolynomial

namespace PNP.Concrete.CNFRegisterDecoder

open BitRegister

def sourceFuel : NatPolynomial := .linear 6 16

theorem sourceFuel_eval (length : Nat) : sourceFuel.eval length = 6 * length + 16 :=
  NatPolynomial.eval_linear 6 16 length

theorem acceptsWithin : CompilerIO.AcceptsWithin program sourceFuel := by
  intro input
  change (BitRegister.run program (sourceFuel.eval input.length)
    (BitRegister.initial program input)).control = .accepted
  rw [sourceFuel_eval]
  exact source_accepts input

/-- A closed finite machine, with no supplied termination or correctness premise. -/
def polynomial : PolynomialTimeFunction :=
  CompilerIO.compilePolynomial program sourceFuel acceptsWithin

theorem polynomial_program :
    polynomial.program =
      .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 3 sourceFuel) :=
  CompilerIO.compilePolynomial_program program sourceFuel acceptsWithin

private theorem output_projection (input : BitString) :
    polynomial.output input =
      (CompilerIO.compilePolynomial program sourceFuel acceptsWithin).output input := rfl

theorem polynomial_output (input : BitString) :
    polynomial.output input = resultData (decodeEncodedCNF input) := by
  rw [output_projection, CompilerIO.compilePolynomial_output]
  change (BitRegister.run program (sourceFuel.eval input.length)
    (BitRegister.initial program input)).store.get 2 = _
  rw [sourceFuel_eval]
  exact source_output input

theorem polynomial_canonical (formula : CNFFormula) :
    polynomial.output (encodeCNF formula) = true :: formulaData formula := by
  rw [polynomial_output, decodeEncodedCNF_canonical]
  rfl

theorem polynomial_malformed (input : BitString) (invalid : decodeEncodedCNF input = none) :
    polynomial.output input = [false] := by
  rw [polynomial_output, invalid]
  rfl

theorem polynomial_machine_accepts (input : BitString) :
    boundedDecide (CompilerIO.rawMachine program)
      ((CompilerIO.runtimePolynomial 3 sourceFuel).eval input.length) input = .accept :=
  CompilerIO.compilePolynomial_accepts program sourceFuel acceptsWithin input

theorem polynomial_output_length (input : BitString) :
    (polynomial.output input).length ≤ input.length + 1 := by
  rw [polynomial_output, ← decodedData_eq_result]
  exact decodedData_length input

end PNP.Concrete.CNFRegisterDecoder
