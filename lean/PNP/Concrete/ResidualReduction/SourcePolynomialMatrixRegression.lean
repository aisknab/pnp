import Lean
import PNP.Concrete.ResidualReduction.SourcePolynomialAffineSpace
import PNP.Concrete.ResidualReduction.SourceMatrixRowRegression

namespace PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

private def cross : Row 2 := ⟨true, (true, (false, true)), (false, (true, false))⟩
private def parallel : Row 2 := ⟨false, (true, (true, false)), (true, (true, true))⟩
private def source : Family 2 := [cross, parallel]

-- Both omitted headers, either missing terminator, truncated rows and trailing bits.
example : polynomial.output [] = [false] := polynomial_malformed [] rfl
example : polynomial.output [false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [true, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true, false, false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true, false, true, true, true, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true, false, true, true, true, true] = [false] := polynomial_malformed _ rfl

-- Zero dimensions and empty families still retain their explicit dimensions.
example : polynomial.output [false, false] = [false, false] := by rw [polynomial_output]; rfl
example : polynomial.output [true, false, false] = [false, true, false, false] := by rw [polynomial_output]; rfl
example : polynomial.output [true, true, false, false] =
    [false, true, true, true, true, false, false, false, false, false] := by rw [polynomial_output]; rfl
example : polynomial.output [false, true, false, true, true, true] = [true, false, false] := by
  rw [polynomial_output]; rfl
example : polynomial.output (codec.encode ⟨2, source⟩) =
    [true, true, false, true, true, true, true, false,
      false, false, false, true, false, false, true, false, false, false, false, false] := by
  rw [polynomial_canonical]; rfl

-- Literal closed program runs from the normal raw-input initial store.
set_option maxRecDepth 8192 in
example : (BitRegister.run program 64 (BitRegister.initial program [])).control = .accepted := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run program 64 (BitRegister.initial program [false, false, true])).store.get 8 = [false] := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run program (SourceEncodedMatrix.validFuel 0 [] + 1)
    (BitRegister.initial program [false, false])).store.get 8 = [false, false] := rfl

-- Composition covers construction, handoff and the exact complete solution map.
example : SourcePolynomialAffineSpace.polynomial.output [] = [false] :=
  SourcePolynomialAffineSpace.polynomial_malformed _ rfl
example : SourcePolynomialAffineSpace.polynomial.output [false, false] = [true, false] := by
  rw [SourcePolynomialAffineSpace.polynomial_output]; rfl
example : SourcePolynomialAffineSpace.polynomial.output (codec.encode ⟨2, source⟩) =
    [true, true, false, false, false, true, false] := by
  rw [SourcePolynomialAffineSpace.polynomial_canonical]; rfl
example : SourcePolynomialAffineSpace.polynomial.output (codec.encode ⟨2, [cross]⟩) =
    [true, false, false] := by rw [SourcePolynomialAffineSpace.polynomial_canonical]; rfl
example : SourcePolynomialAffineSpace.polynomial.output (codec.encode ⟨3, ([] : Family 3)⟩) =
    [true, false] := by rw [SourcePolynomialAffineSpace.polynomial_canonical]; rfl
example : SourcePolynomialAffineSpace.polynomial.output (codec.encode ⟨0, ([⟨true, true, false⟩] : Family 0)⟩) =
    [true, true, false, true, false] := by rw [SourcePolynomialAffineSpace.polynomial_canonical]; rfl

-- Arbitrary input and arbitrary source family, not only regression fixtures.
example : CompilerIO.AcceptsWithin program sourceFuel := acceptsWithin
example (input : BitString) : polynomial.output input = SourceFamilyInput.matrixEncoded input := polynomial_output input
example (n : Nat) (F : Family n) : polynomial.output (codec.encode ⟨n, F⟩) = affineMatrixPacket F :=
  polynomial_canonical n F
example (n : Nat) (F : Family n) :
    (solutionCodec F.length).decode (SourcePolynomialAffineSpace.polynomial.output (codec.encode ⟨n, F⟩)) =
      some (BinaryLinear.solve F.length (SourceClosure.affineMaskRows F)) :=
  SourcePolynomialAffineSpace.exact_decoded_space n F
example (length : Nat) : sourceFuel.eval length =
    24 * length * length * length * length + 66 * length * length * length +
      32 * length * length + 57 * length + 58 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, NatPolynomial.eval_variable, NatPolynomial.eval_linear, Nat.mul_assoc]
  omega
example : polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 16 sourceFuel) :=
  polynomial_program
example (input : BitString) : boundedDecide (CompilerIO.rawMachine program)
    ((CompilerIO.runtimePolynomial 16 sourceFuel).eval input.length) input = .accept := polynomial_machine_accepts input
example (input : BitString) : (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  polynomial_output_bound input

-- Fail closed if an unproved premise enters any new load-bearing dependency.
run_cmd do
  for name in [``PNP.Concrete.ResidualReduction.SourceMatrixConstruction.payload_exec,
    ``PNP.Concrete.ResidualReduction.SourceMatrixPacket.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceFamilyLoader.seed_exec,
    ``PNP.Concrete.ResidualReduction.SourceFamilyInput.payload_complete,
    ``PNP.Concrete.ResidualReduction.SourceEncodedMatrix.block_exec,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.acceptsWithin,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.polynomial_output,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.polynomial_canonical,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.polynomial_malformed,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.polynomial_machine_accepts,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.polynomial_output_bound,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialAffineSpace.polynomial_canonical,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialAffineSpace.exact_decoded_space,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialAffineSpace.polynomial_malformed,
    ``PNP.Concrete.ResidualReduction.SourcePolynomialAffineSpace.pipeline_program] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.polynomial_machine_accepts
#print axioms PNP.Concrete.ResidualReduction.SourcePolynomialAffineSpace.exact_decoded_space

end PNP.Concrete.ResidualReduction.SourcePolynomialMatrix.Regression
