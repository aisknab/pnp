/-
Copyright (c) 2026 PNP Labs.

Closed original-input frontend. The strict source compiler derives the circuit
internally; the concrete frontend then emits its exact formula and original
width. Malformed source words produce the false-tag record. All runtime and
output bounds belong to the complete executable pipeline, not supplied traces.
This preprocessing result is not a SAT decision procedure.
-/

import PNP.Concrete.NANDFrontendCanonical
import PNP.Concrete.CNFToNANDCompilerCompiled

namespace PNP.Concrete.NANDFrontend

def sourceData (input : BitString) : BitString :=
  match decodeEncodedCNF input with
  | none => [false]
  | some original => recordData original.variableCount (formula (CNFToNAND.compileFormula original))

def sourcePolynomial : PolynomialTimeFunction :=
  PolynomialTimeFunction.compose CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction polynomial

theorem sourcePolynomial_program :
    sourcePolynomial.program =
      .compose CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction.program polynomial.program := rfl

private theorem source_output_projection (input : BitString) :
    sourcePolynomial.output input =
      (PolynomialTimeFunction.compose
        CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction polynomial).output input := rfl

theorem sourcePolynomial_output (input : BitString) :
    sourcePolynomial.output input = sourceData input := by
  rw [source_output_projection, PolynomialTimeFunction.compose_output,
    CNFToNANDCompilerCompiled.cnfToNANDPolynomialTimeFunction_output]
  cases decoded : decodeEncodedCNF input with
  | none =>
      rw [CNFToNAND.compileEncodedCNFToNAND_of_malformed input decoded, polynomial_empty]
      simp only [sourceData, decoded]
  | some original =>
      rw [CNFToNAND.compileEncodedCNFToNAND_of_decoded input original decoded, polynomial_canonical]
      simp only [circuitData, CNFToNAND.compileFormula_inputCount, sourceData, decoded]

theorem sourcePolynomial_malformed (input : BitString) (malformed : decodeEncodedCNF input = none) :
    sourcePolynomial.output input = [false] := by
  rw [sourcePolynomial_output]
  simp only [sourceData, malformed]

theorem sourcePolynomial_decoded (input : BitString) (original : CNFFormula)
    (decoded : decodeEncodedCNF input = some original) :
    sourcePolynomial.output input =
      recordData original.variableCount (formula (CNFToNAND.compileFormula original)) := by
  rw [sourcePolynomial_output]
  simp only [sourceData, decoded]

def rawRefinement : FunctionProgram.RawRefinement polynomial.program := by
  rw [polynomial_program]
  exact FunctionProgram.RawRefinement.ofMachine (BitRegister.CompilerIO.rawMachine program)
    (BitRegister.CompilerIO.runtimePolynomial 9 sourceFuel)

def sourceRawRefinement : FunctionProgram.RawRefinement sourcePolynomial.program := by
  rw [sourcePolynomial_program]
  exact FunctionProgram.RawRefinement.compose
    CNFToNANDCompilerCompiled.cnfToNANDRawRefinement rawRefinement

theorem sourceMachine_output (input : BitString) :
    machineOutput sourceRawRefinement.machine
      (sourceRawRefinement.timeBound.eval (BitString.size input)) input = sourceData input :=
  (sourceRawRefinement.output_eq input (sourcePolynomial.haltsWithin input)).trans
    (sourcePolynomial_output input)

theorem sourceMachine_halts (input : BitString) :
    boundedDecide sourceRawRefinement.machine
      (sourceRawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  sourceRawRefinement.haltsWithin input (sourcePolynomial.haltsWithin input)

theorem sourceMachine_output_size (input : BitString) :
    BitString.size (machineOutput sourceRawRefinement.machine
      (sourceRawRefinement.timeBound.eval (BitString.size input)) input) ≤
        sourcePolynomial.outputSizeBound.eval (BitString.size input) :=
  FunctionProgram.RawRefinement.output_size_le sourcePolynomial sourceRawRefinement input

end PNP.Concrete.NANDFrontend
