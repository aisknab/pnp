import Lean
import PNP.Concrete.ResidualReduction.SourceBilinearPullbackInstructions
import PNP.Concrete.ResidualReduction.SourceLineQueryMatricesRegression

namespace PNP.Concrete.ResidualReduction.SourceBilinearPullback.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

private def identity : Matrix 2 2 := fun i j => i == j
private def shiftedLeft : Space 2 := ⟨2, ((true, (false, true)), ((true, (true, true)), ()))⟩
private def shiftedRight : Space 2 := ⟨2, ((true, (false, true)), ((false, (true, false)), ()))⟩
private def linearLeft : Space 2 := ⟨2, ((true, (false, false)), ((true, (true, false)), ()))⟩
private def linearRight : Space 2 := ⟨2, ((true, (false, false)), ((false, (true, false)), ()))⟩
private def noParameters : Space 2 := ⟨0, (true, (false, ()))⟩
private def redundantLeft : Space 0 := ⟨2, ()⟩
private def redundantRight : Space 0 := ⟨3, ()⟩
private def zero00 : Matrix 0 0 := fun _ _ => false
private def zero20 : Matrix 2 0 := fun _ _ => false
private def rectangular : Matrix 2 1 := fun i _ => i == 0
private def duplicatedRight : Space 1 := ⟨2, ((true, (true, true)), ())⟩

-- S has columns (1,1) and (0,1); T is the identity. Hence S^T M T
-- is [[1,1],[0,1]], not its transpose. Affine origins must not enter it.
example : coefficientMatrixBits identity = [true, false, false, true] := rfl
example : coefficientMatrixBits (pullMatrix identity shiftedLeft shiftedRight) = [true, true, false, true] := rfl
example : coefficientMatrixBits (pullMatrix identity linearLeft linearRight) = [true, true, false, true] := rfl
example : (SourceEncoding.pointCodec 2).encode (shiftedLeft.direction (unitPoint 2 0)) = [true, true] := rfl
example : (SourceEncoding.pointCodec 2).encode (shiftedRight.direction (unitPoint 2 1)) = [false, true] := rfl
example : mapEval shiftedLeft.forms (unitPoint 2 0) = (false, (false, ())) := rfl
example : coefficientMatrixBits (pullMatrix rectangular shiftedLeft duplicatedRight) = [true, true, false, false] := rfl
example : matrixBytes identity shiftedLeft shiftedRight 0 2 = [true, true, false, true] := rfl
example : matrixBytes identity shiftedLeft shiftedRight 1 1 = [false, true] := rfl
example : columnBytes identity shiftedLeft shiftedRight 0 1 1 = [true] := rfl
example : coefficient identity shiftedLeft shiftedRight 2 0 = false := rfl
example : coefficient identity shiftedLeft shiftedRight 0 2 = false := rfl

-- Empty source dimensions need not imply empty parameter lists; the generic
-- map interface permits redundant parameters and must emit every zero entry.
example : coefficientMatrixBits (pullMatrix zero00 redundantLeft redundantRight) =
    [false, false, false, false, false, false] := rfl
example : coefficientMatrixBits (pullMatrix identity noParameters shiftedRight) = [] := rfl
example : coefficientMatrixBits (pullMatrix identity shiftedLeft noParameters) = [] := rfl
example : fuel 0 0 0 3 = 5 := rfl
example : fuel 0 0 3 0 = 23 := rfl
example : SourceBilinearEvaluation.fuel 2 0 = 14 := rfl
example : bilinearEval identity (true, (true, ())) (true, (true, ())) = false := rfl
example : bilinearEval identity (true, (false, ())) (true, (true, ())) = true := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run (SourceBilinearEvaluation.block.program 0 8) 15
    ⟨.running 0, ({base 0 [] with target := [true, false]}).store⟩).store.get 8 = [false] := rfl
set_option maxRecDepth 16384 in
example : (BitRegister.run (SourceBilinearEvaluation.block.program 0 8)
    (SourceBilinearEvaluation.fuel 2 2 + 1)
    ⟨.running 0, ({base 0 [] with input := [true, false, false, true], target := [true, true], reserved := [true, true]}).store⟩).store.get 8 =
      [false] := rfl

example : (SourceMapUnit.result shiftedLeft.forms (0 : Fin 2)).core.output = [true, true] := rfl
example : (SourceBilinearPullbackEntry.result identity shiftedLeft shiftedRight (0 : Fin 2) (1 : Fin 2)).store.get 8 = [true] := rfl
example : (SourceBilinearPullbackEntry.result identity shiftedLeft shiftedRight (1 : Fin 2) (0 : Fin 2)).store.get 8 = [false] := rfl
example : (SourceBilinearPullbackEntry.result identity shiftedLeft shiftedRight (1 : Fin 2) (0 : Fin 2)).store.get 15 = [true] := rfl
example : (SourceBilinearPullbackEntry.result identity shiftedLeft shiftedRight (1 : Fin 2) (0 : Fin 2)).store.get 16 = [] := rfl

example : (BitRegister.run program (fuel 2 2 2 2 + 1)
    ⟨.running 0, (start identity shiftedLeft shiftedRight).store⟩).store.get 8 = [true, true, false, true] := by
  exact congrArg (fun c => c.store.get (8 : Fin 21)) (program_run identity shiftedLeft shiftedRight)
example : (BitRegister.run program (fuel 0 0 2 3 + 1)
    ⟨.running 0, (start zero00 redundantLeft redundantRight).store⟩).store.get 8 =
      [false, false, false, false, false, false] := by
  exact congrArg (fun c => c.store.get (8 : Fin 21)) (program_run zero00 redundantLeft redundantRight)
example : (BitRegister.run program (fuel 2 2 2 0 + 1)
    ⟨.running 0, (start identity shiftedLeft noParameters).store⟩).control = .accepted := by
  exact congrArg (fun c => c.control) (program_run identity shiftedLeft noParameters)
example : (BitRegister.run program (fuel 2 2 0 2 + 1)
    ⟨.running 0, (start identity noParameters shiftedRight).store⟩).store.get 8 = [] := by
  exact congrArg (fun c => c.store.get (8 : Fin 21)) (program_run identity noParameters shiftedRight)
example : (result identity shiftedLeft shiftedRight).store.get 10 = [true, false, false, true] := rfl
example : (result identity shiftedLeft shiftedRight).store.get 11 = mapBits shiftedLeft.forms := rfl
example : (result identity shiftedLeft shiftedRight).store.get 12 = mapBits shiftedRight.forms := rfl
example : (result identity shiftedLeft shiftedRight).store.get 15 = [true, true] := rfl
example : (result identity shiftedLeft shiftedRight).store.get 16 = [] := rfl
example : (result identity shiftedLeft shiftedRight).store.get 18 = [] := rfl
example : (result identity shiftedLeft shiftedRight).store.get 19 = [] := rfl
example : (result identity shiftedLeft shiftedRight).store.get 20 = [] := rfl

-- Uniform statements, not only the fixtures above.
example {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) :
    Exec block (start M s t).store (fuel m n s.parameters t.parameters) (result M s t).store := block_exec M s t
example {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) :
    (result M s t).store.get 8 = coefficientMatrixBits (pullMatrix M s t) := result_output M s t
example (m n p q L : Nat) (hm : m ≤ L) (hn : n ≤ L) (hp : p ≤ L) (hq : q ≤ L) :
    fuel m n p q ≤ costPolynomial.eval L := bounded_fuel m n p q L hm hn hp hq
example {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) (L : Nat)
    (hp : s.parameters ≤ L) (hq : t.parameters ≤ L) :
    ((result M s t).store.get 8).length ≤ L * L := output_bound M s t L hp hq
example {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel (n + F.length) (directionSpace F [alpha]).parameters
      (kernelSpace (SourceLine.rankOneRows F alpha)).parameters
      (kernelSpace ([] : System (directionSpace F [alpha]).parameters)).parameters ≤
      costPolynomial.eval (2 * (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length) :=
  original_line_bound F alpha

run_cmd do
  for name in [``SourceBilinearEvaluation.rowBits_cons,
    ``SourceBilinearEvaluation.columnStep_exec,
    ``SourceBilinearEvaluation.columnLoop_exec,
    ``SourceBilinearEvaluation.readTarget_exec,
    ``SourceBilinearEvaluation.row_exec,
    ``SourceBilinearEvaluation.matrixLoop_exec,
    ``SourceBilinearEvaluation.block_exec,
    ``SourceBilinearEvaluation.fuel_mono,
    ``SourceMapUnit.lift_exec,
    ``SourceMapUnit.unit_exec,
    ``SourceMapUnit.reverse_exec,
    ``SourceMapUnit.prepare_exec,
    ``SourceMapUnit.map_exec,
    ``SourceMapUnit.block_exec,
    ``SourceMapUnit.fuel_bound,
    ``SourceMapUnit.budget_mono,
    ``SourceBilinearPullbackEntry.lifted_exec,
    ``SourceBilinearPullbackEntry.small_exec,
    ``SourceBilinearPullbackEntry.prepareLeft_exec,
    ``SourceBilinearPullbackEntry.left_exec,
    ``SourceBilinearPullbackEntry.prepareRight_exec,
    ``SourceBilinearPullbackEntry.right_exec,
    ``SourceBilinearPullbackEntry.prepareEval_exec,
    ``SourceBilinearPullbackEntry.eval_exec,
    ``SourceBilinearPullbackEntry.finish_exec,
    ``SourceBilinearPullbackEntry.block_exec,
    ``SourceBilinearPullbackEntry.result_output,
    ``SourceBilinearPullbackEntry.fuel_bound,
    ``SourceBilinearPullbackEntry.budget_mono,
    ``SourceBilinearPullback.coefficient_fin,
    ``SourceBilinearPullback.columnBytes_succ,
    ``SourceBilinearPullback.matrixBytes_succ,
    ``SourceBilinearPullback.matrixBytes_exact,
    ``SourceBilinearPullback.matrixBytes_length,
    ``SourceBilinearPullback.lifted_exec,
    ``SourceBilinearPullback.small_exec,
    ``SourceBilinearPullback.emit_exec,
    ``SourceBilinearPullback.columnStep_exec,
    ``SourceBilinearPullback.columnLoop_exec,
    ``SourceBilinearPullback.columnFuel_bound,
    ``SourceBilinearPullback.row_exec,
    ``SourceBilinearPullback.matrixLoop_exec,
    ``SourceBilinearPullback.matrixFuel_bound,
    ``SourceBilinearPullback.reorder_exec,
    ``SourceBilinearPullback.block_exec,
    ``SourceBilinearPullback.result_output,
    ``SourceBilinearPullback.fuel_bound,
    ``SourceBilinearPullback.budget_mono,
    ``SourceBilinearPullback.program_run,
    ``SourceBilinearPullback.costPolynomial_eval,
    ``SourceBilinearPullback.bounded_fuel,
    ``SourceBilinearPullback.output_bound,
    ``SourceBilinearPullback.original_line_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceBilinearEvaluation.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceMapUnit.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceBilinearPullbackEntry.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceBilinearPullback.matrixBytes_exact
#print axioms PNP.Concrete.ResidualReduction.SourceBilinearPullback.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceBilinearPullback.original_line_bound

end PNP.Concrete.ResidualReduction.SourceBilinearPullback.Regression
