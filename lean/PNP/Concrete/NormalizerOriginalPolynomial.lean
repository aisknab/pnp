/-
Copyright (c) 2026 PNP Labs.

The strict raw-CNF frontend and complete output routine compose into one
polynomially bounded raw machine. Every malformed source word emits the
malformed packet. Valid words use only the internally derived frontend,
candidate, first failure and original-width recovery data. The system branch
is a residual problem, not a decision or a refutation.
-/
import PNP.Concrete.NANDFrontendOriginal
import PNP.Concrete.NormalizerOutputPostprocessPolynomial

namespace PNP.Concrete.NormalizerBlocks.OriginalNormalizer

def transformed (original : CNFFormula) : CNFFormula :=
  NANDFrontend.formula (CNFToNAND.compileFormula original)
def decodedPacket (original : CNFFormula) : BitString :=
  (OutputBranches.dispatched
    (SourceCheck.result (MatchingDriver.encode (transformed original).variableCount (transformed original).clauses))
    (List.replicate original.variableCount true)).registers.output
def data (input : BitString) : BitString :=
  match decodeEncodedCNF input with
  | none => [false,false,false]
  | some original => decodedPacket original

def polynomial : PolynomialTimeFunction :=
  PolynomialTimeFunction.compose NANDFrontend.sourcePolynomial OutputPostprocess.polynomial
theorem polynomial_program :
    polynomial.program = .compose NANDFrontend.sourcePolynomial.program OutputPostprocess.polynomial.program := rfl
private theorem output_projection (input : BitString) :
    polynomial.output input =
      (PolynomialTimeFunction.compose NANDFrontend.sourcePolynomial OutputPostprocess.polynomial).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input = data input := by
  rw [output_projection,PolynomialTimeFunction.compose_output,NANDFrontend.sourcePolynomial_output,
    OutputPostprocess.polynomial_output]
  cases decoded : decodeEncodedCNF input with
  | none =>
      simp only [NANDFrontend.sourceData,decoded,data]
      exact OutputPostprocess.malformed_output [false] rfl
  | some original =>
      simp only [NANDFrontend.sourceData,decoded,data]
      rw [OutputPostprocess.canonical_result]
      rfl
theorem polynomial_malformed (input : BitString) (malformed : decodeEncodedCNF input = none) :
    polynomial.output input = [false,false,false] := by
  rw [polynomial_output]
  simp only [data,malformed]
theorem polynomial_decoded (input : BitString) (original : CNFFormula)
    (decoded : decodeEncodedCNF input = some original) :
    polynomial.output input = decodedPacket original := by
  rw [polynomial_output]
  simp only [data,decoded]

def outputRawRefinement : FunctionProgram.RawRefinement OutputPostprocess.polynomial.program := by
  rw [OutputPostprocess.polynomial_program]
  exact FunctionProgram.RawRefinement.ofMachine
    (BitRegister.CompilerIO.rawMachine OutputPostprocess.program)
    (BitRegister.CompilerIO.runtimePolynomial 38 OutputPostprocess.sourceFuel)
def rawRefinement : FunctionProgram.RawRefinement polynomial.program := by
  rw [polynomial_program]
  exact FunctionProgram.RawRefinement.compose NANDFrontend.sourceRawRefinement outputRawRefinement
theorem machine_output (input : BitString) :
    machineOutput rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input = data input :=
  (rawRefinement.output_eq input (polynomial.haltsWithin input)).trans (polynomial_output input)
theorem machine_halts (input : BitString) :
    boundedDecide rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  rawRefinement.haltsWithin input (polynomial.haltsWithin input)
theorem machine_output_size (input : BitString) :
    BitString.size (machineOutput rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input) ≤
        polynomial.outputSizeBound.eval (BitString.size input) :=
  FunctionProgram.RawRefinement.output_size_le polynomial rawRefinement input
theorem machine_malformed (input : BitString) (malformed : decodeEncodedCNF input = none) :
    machineOutput rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input = [false,false,false] := by
  rw [machine_output]
  simp only [data,malformed]
theorem machine_decoded (input : BitString) (original : CNFFormula)
    (decoded : decodeEncodedCNF input = some original) :
    machineOutput rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input = decodedPacket original := by
  rw [machine_output]
  simp only [data,decoded]

end PNP.Concrete.NormalizerBlocks.OriginalNormalizer
