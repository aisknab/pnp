import PNP.Concrete.ResidualReduction.SourcePolynomialMatrix
import PNP.Concrete.ResidualReduction.MatrixPolynomialSolver

/-! Polynomial construction and solution of the source affine-mask equations.
Both pipeline leaves are literal compiled machines; composition includes the
intermediate encoded-size and runtime bounds. The returned full affine Space
has exactly the existing solver's parameter and coordinate order. Selecting
an active affine witness, the remaining query alternatives, and the complete
contraction loop are not established by this component. -/

namespace PNP.Concrete.ResidualReduction.SourcePolynomialAffineSpace
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def polynomial : PolynomialTimeFunction :=
  PolynomialTimeFunction.compose SourcePolynomialMatrix.polynomial MatrixPolynomialSolver.polynomial

private theorem output_projection (input : BitString) : polynomial.output input =
    (PolynomialTimeFunction.compose SourcePolynomialMatrix.polynomial MatrixPolynomialSolver.polynomial).output input := rfl

theorem polynomial_output (input : BitString) : polynomial.output input =
    MatrixInputEncoding.solveEncoded (SourceFamilyInput.matrixEncoded input) := by
  rw [output_projection, PolynomialTimeFunction.compose_output,
    SourcePolynomialMatrix.polynomial_output, MatrixPolynomialSolver.polynomial_output]

theorem polynomial_canonical (n : Nat) (F : Family n) :
    polynomial.output (codec.encode ⟨n, F⟩) =
      (solutionCodec F.length).encode (solve F.length (SourceClosure.affineMaskRows F)) := by
  rw [output_projection, PolynomialTimeFunction.compose_output, SourcePolynomialMatrix.polynomial_canonical]
  exact MatrixPolynomialSolver.polynomial_canonical F.length (SourceClosure.affineMaskRows F)

theorem polynomial_malformed (input : BitString) (invalid : codec.decode input = none) :
    polynomial.output input = [false] := by
  rw [output_projection, PolynomialTimeFunction.compose_output, SourcePolynomialMatrix.polynomial_malformed input invalid]
  exact MatrixPolynomialSolver.polynomial_malformed [false] rfl

theorem exact_decoded_space (n : Nat) (F : Family n) :
    (solutionCodec F.length).decode (polynomial.output (codec.encode ⟨n, F⟩)) =
      some (solve F.length (SourceClosure.affineMaskRows F)) := by
  rw [polynomial_canonical]
  exact solution_roundtrip F.length _

private theorem program_projection : polynomial.program =
    FunctionProgram.compose SourcePolynomialMatrix.polynomial.program MatrixPolynomialSolver.polynomial.program := rfl

theorem pipeline_program : polynomial.program =
    .compose
      (.machine (BitRegister.CompilerIO.rawMachine SourcePolynomialMatrix.program)
        (BitRegister.CompilerIO.runtimePolynomial 16 SourcePolynomialMatrix.sourceFuel))
      (.machine (BitRegister.CompilerIO.rawMachine MatrixPolynomialSolver.program)
        (BitRegister.CompilerIO.runtimePolynomial 12 MatrixPolynomialSolver.sourceFuel)) := by
  rw [program_projection, SourcePolynomialMatrix.polynomial_program, MatrixPolynomialSolver.polynomial_program]

end PNP.Concrete.ResidualReduction.SourcePolynomialAffineSpace
