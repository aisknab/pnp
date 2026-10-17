import Lean
import PNP.Concrete.ResidualReduction.MatrixKernelSolver
import PNP.Concrete.ResidualReduction.MatrixPolynomialSolverRegression
import PNP.Concrete.ResidualReduction.SourcePolynomialAffineQueryRegression

namespace PNP.Concrete.ResidualReduction.MatrixKernelSolver.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixInputEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

private def fullTwo : Space 2 := ⟨2, ((true, (false, false)), ((false, (true, false)), ()))⟩
private def constrained : System 2 := [(true, (false, true))]

-- The literal pass changes only constants, including zero-width rows.
example : affineWord (n := 0) (homogeneousRow (n := 0) true) = [false] := rfl
example : affineWord (n := 2) (homogeneousRow (n := 2) (true, (false, true))) = [true, false, false] := rfl
example : MatrixHomogeneous.fuel 0 [true] = 14 := rfl
example : MatrixHomogeneous.fuel 2 constrained = 32 := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run (MatrixHomogeneous.block.program 0 8) 15
    ⟨.running 0, (MatrixSolutionInstructions.start 0 [true]).store⟩).store.get 0 = [false] := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run (MatrixHomogeneous.block.program 0 8) 15
    ⟨.running 0, (MatrixSolutionInstructions.start 0 [true]).store⟩).store.get 7 = [false] := rfl

-- Missing headers/terminators, short payloads and trailing bytes fail closed.
example : polynomial.output [] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [true, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, true, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [true, false, true, false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false, false] = [false] := polynomial_malformed _ rfl
example : polynomial.output [false, false, true] = [false] := polynomial_malformed _ rfl
example : polynomial.output [true, false, true, false, true, true, false] = [false] := polynomial_malformed _ rfl

-- Homogenization is essential: an inconsistent affine system still has a
-- homogeneous kernel. Returning the old affine solver result would fail here.
example : MatrixPolynomialSolver.polynomial.output [false, true, false, true] = [false] := by
  rw [MatrixPolynomialSolver.polynomial_output]; rfl
example : polynomial.output [false, true, false, true] = [true, false] := by
  rw [polynomial_output]; rfl
example : polynomial.output [false, true, false, false] = [true, false] := by
  rw [polynomial_output]; rfl
example : polynomial.output [false, false] = [true, false] := by rw [polynomial_output]; rfl
example : polynomial.output (codec.encode ⟨1, ([(false, true)] : System 1)⟩) = [true, true, false, true, false] := by
  rw [polynomial_canonical]; rfl
example : polynomial.output (codec.encode ⟨1, ([(true, true)] : System 1)⟩) = [true, false, false] := by
  rw [polynomial_canonical]; rfl
example : polynomial.output (codec.encode ⟨2, constrained⟩) = [true, true, false, false, false, true, false] := by
  rw [polynomial_canonical]; rfl
example : (solutionCodec 2).decode (polynomial.output (codec.encode ⟨2, ([] : System 2)⟩)) = some (some fullTwo) :=
  exact_decoded_kernel 2 []
example : (solutionCodec 1).decode [true, true] = none := rfl
example : (solutionCodec 0).decode [true, false, true] = none := rfl

-- Direct raw-input runs check entry wiring independently of the output theorem.
set_option maxRecDepth 8192 in
example : (BitRegister.run program 128 (BitRegister.initial program [])).control = .accepted := rfl
set_option maxRecDepth 8192 in
example : (BitRegister.run program 128 (BitRegister.initial program [false, false, true])).store.get 8 = [false] := rfl

-- General contracts cover all source matrices and every input bitstring.
example (n : Nat) (rows : System n) :
    NormalizerBlocks.Exec MatrixHomogeneous.block (MatrixSolutionInstructions.start n rows).store
      (MatrixHomogeneous.fuel n rows) (MatrixSolutionInstructions.start n (homogeneous rows)).store :=
  MatrixHomogeneous.block_exec n rows
example (n : Nat) (rows : System n) :
    NormalizerBlocks.Exec consumer (MatrixSolutionInstructions.start n rows).store
      (MatrixHomogeneous.fuel n rows + MatrixSolutionInstructions.phaseFuel n (homogeneous rows))
      (MatrixSolutionSerialization.result (kernelSpace rows)).store := consumer_exec n rows
example (input : BitString) : polynomial.output input = answer input := polynomial_output input
example (L : Nat) : sourceFuel.eval L = sourceBudget L + 1 := sourceFuel_eval L
example : CompilerIO.AcceptsWithin program sourceFuel := acceptsWithin
example : polynomial.program = .machine (CompilerIO.rawMachine program) (CompilerIO.runtimePolynomial 12 sourceFuel) :=
  polynomial_program
example (input : BitString) : boundedDecide (CompilerIO.rawMachine program)
    ((CompilerIO.runtimePolynomial 12 sourceFuel).eval input.length) input = .accept := polynomial_machine_accepts input
example (input : BitString) : (polynomial.output input).length ≤ (input.length + 1) * (input.length + 1) + 1 :=
  polynomial_output_bound input
example (n : Nat) (rows : System n) (s : Space n)
    (returned : (solutionCodec n).decode (polynomial.output (codec.encode ⟨n, rows⟩)) = some (some s)) :
    ∀ v, satisfies (homogeneous rows) v = true ↔ ∃ z, s.direction z = v := by
  rw [exact_decoded_kernel] at returned
  have same : kernelSpace rows = s := Option.some.inj (Option.some.inj returned)
  rw [← same]
  exact kernelSpace_iff rows

run_cmd do
  for name in [``PNP.Concrete.ResidualReduction.MatrixHomogeneous.homogeneous_bits,
    ``PNP.Concrete.ResidualReduction.MatrixHomogeneous.row_exec,
    ``PNP.Concrete.ResidualReduction.MatrixHomogeneous.loop_exec,
    ``PNP.Concrete.ResidualReduction.MatrixHomogeneous.block_exec,
    ``PNP.Concrete.ResidualReduction.MatrixHomogeneous.fuel_bound,
    ``PNP.Concrete.ResidualReduction.MatrixInputConsumer.complete_check,
    ``PNP.Concrete.ResidualReduction.MatrixInputConsumer.valid_exec,
    ``PNP.Concrete.ResidualReduction.MatrixInputConsumer.loadFuel_bound,
    ``PNP.Concrete.ResidualReduction.MatrixInputConsumer.short_check,
    ``PNP.Concrete.ResidualReduction.MatrixInputConsumer.extra_check,
    ``PNP.Concrete.ResidualReduction.MatrixInputConsumer.failed_header,
    ``PNP.Concrete.ResidualReduction.MatrixInputConsumer.failed_payload,
    ``PNP.Concrete.ResidualReduction.MatrixInputConsumer.block_exec,
    ``computedSpace_eq, ``result_eq, ``consumer_exec, ``consumer_bound, ``consumer_ready,
    ``block_exec, ``sourceFuel_eval, ``source_result, ``acceptsWithin, ``source_output,
    ``polynomial_program, ``polynomial_output, ``polynomial_canonical, ``polynomial_malformed,
    ``exact_decoded_kernel, ``polynomial_machine_accepts, ``polynomial_output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.MatrixHomogeneous.block_exec
#print axioms PNP.Concrete.ResidualReduction.MatrixInputConsumer.block_exec
#print axioms PNP.Concrete.ResidualReduction.MatrixKernelSolver.polynomial_output
#print axioms PNP.Concrete.ResidualReduction.MatrixKernelSolver.exact_decoded_kernel
#print axioms PNP.Concrete.ResidualReduction.MatrixKernelSolver.polynomial_machine_accepts

end PNP.Concrete.ResidualReduction.MatrixKernelSolver.Regression
