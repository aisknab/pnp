import Lean
import PNP.Concrete.ResidualReduction.MatrixPolynomialSolver
import PNP.Concrete.ResidualReduction.MatrixSolutionRegression

namespace PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInputEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

-- Missing either terminator, too few coefficients, and either trailing bit.
example : codec.decode [] = none := rfl
example : codec.decode [true, true] = none := rfl
example : codec.decode [false] = none := rfl
example : codec.decode [false, true] = none := rfl
example : codec.decode [true, false, true, false, false] = none := rfl
example : codec.decode [true, false, true, false, false, false, true] = none := rfl
example : codec.decode [false, false, false] = none := rfl
example : codec.decode [false, false, true] = none := rfl

example : polynomial.output [] = [false] := polynomial_malformed [] rfl
example : polynomial.output [true, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [true, false, true, false, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [true, false, true, false, false, false, true] = [false] :=
  polynomial_malformed _ rfl
example : polynomial.output [false, false, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false, true] = [false] := polynomial_malformed _ rfl

-- Fully parsed valid inputs: empty, contradictory, free, and pivoted systems.
example : polynomial.output [false, false] = [true, false] := by rw [polynomial_output]; rfl
example : polynomial.output [false, true, false, true] = [false] := by rw [polynomial_output]; rfl
example : polynomial.output [false, true, false, false] = [true, false] := by rw [polynomial_output]; rfl
example : polynomial.output [true, false, false] = [true, true, false, true, false] := by
  rw [polynomial_output]; rfl
example : polynomial.output (codec.encode ⟨1, [(true, true)]⟩) = [true, false, true] := by
  rw [polynomial_canonical]; rfl
example : polynomial.output (codec.encode ⟨1, [(false, true)]⟩) = [false] := by
  rw [polynomial_canonical]; rfl
example : polynomial.output (codec.encode ⟨1, [(true, false), (true, true)]⟩) = [false] := by
  rw [polynomial_canonical]; rfl
example : polynomial.output (codec.encode ⟨2, [(false, (true, false))]⟩) =
    [true, true, false, true, false, false, false] := by rw [polynomial_canonical]; rfl
example : polynomial.output (codec.encode ⟨2, [(true, (true, true))]⟩) =
    [true, true, false, true, true, true, false] := by rw [polynomial_canonical]; rfl

-- Literal closed source execution starts from its normal raw-input initial state.
set_option maxRecDepth 4096 in
example : (BitRegister.run program 64 (BitRegister.initial program [])).control = .accepted := rfl
set_option maxRecDepth 4096 in
example : (BitRegister.run program 64 (BitRegister.initial program [])).store.get 8 = [false] := rfl
set_option maxRecDepth 4096 in
example : (BitRegister.run program 64 (BitRegister.initial program [false, false, true])).store.get 8 =
    [false] := rfl
set_option maxRecDepth 4096 in
example : (BitRegister.run program (MatrixEncodedSolver.validFuel 0 [] + 1)
    (BitRegister.initial program [false, false])).store.get 8 = [true, false] := rfl
set_option maxRecDepth 4096 in
example : (BitRegister.run program (MatrixEncodedSolver.validFuel 1 [] + 1)
    (BitRegister.initial program [true, false, false])).store.get 8 =
    [true, true, false, true, false] := rfl

-- Uniform statements: arbitrary dimensions, arbitrary matrices, all bitstrings.
example : CompilerIO.AcceptsWithin program sourceFuel := acceptsWithin
example (input : BitString) : polynomial.output input = solveEncoded input := polynomial_output input
example (n : Nat) (rows : System n) :
    polynomial.output (codec.encode ⟨n, rows⟩) = (solutionCodec n).encode (solve n rows) :=
  polynomial_canonical n rows
example (n : Nat) (rows : System n) :
    (solutionCodec n).decode (polynomial.output (codec.encode ⟨n, rows⟩)) = some (solve n rows) := by
  rw [polynomial_canonical]
  exact solution_roundtrip n (solve n rows)
example (length : Nat) : sourceFuel.eval length =
    130 * length * length * length + 238 * length * length + 133 * length + 57 := by
  simp only [sourceFuel, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, NatPolynomial.eval_variable, NatPolynomial.eval_linear,
    Nat.mul_assoc]
  omega
example : polynomial.program =
    .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 12 sourceFuel) :=
  polynomial_program
example (input : BitString) : boundedDecide (CompilerIO.rawMachine program)
    ((CompilerIO.runtimePolynomial 12 sourceFuel).eval input.length) input = .accept :=
  polynomial_machine_accepts input
example (input : BitString) :
    (polynomial.output input).length ≤ input.length + sourceFuel.eval input.length :=
  polynomial_output_bound input

-- Fail closed on project axioms, sorryAx, or accidental classical-choice use.
run_cmd do
  for name in [``PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.acceptsWithin,
    ``PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.polynomial_output,
    ``PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.polynomial_canonical,
    ``PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.polynomial_malformed,
    ``PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.polynomial_machine_accepts,
    ``PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.polynomial_output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.acceptsWithin
#print axioms PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.polynomial_machine_accepts

end PNP.Concrete.ResidualReduction.MatrixPolynomialSolver.Regression
