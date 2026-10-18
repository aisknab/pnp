import PNP.Concrete.ResidualReduction.MatrixPivotMapInstructions
import PNP.Concrete.ResidualReduction.MatrixSweepRegression

namespace PNP.Concrete.ResidualReduction.MatrixSolutionEncoding.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions

-- The Option tag, dimension-delimited coefficients, and end of input are exact.
example : (solutionCodec 1).decode [false] = some none := rfl
example : (solutionCodec 1).decode [false, true] = none := rfl
example : (solutionCodec 1).decode [] = none := rfl
example : (solutionCodec 1).decode [true, true] = none := rfl
example : (solutionCodec 1).decode [true, false] = none := rfl
example : (solutionCodec 1).decode [true, false, true] =
    some (some ⟨0, (true, ())⟩) := rfl
example : (solutionCodec 1).decode [true, false, true, false] = none := rfl
example (n : Nat) (s : Option (Space n)) :
    (solutionCodec n).decode ((solutionCodec n).encode s) = some s := solution_roundtrip n s
example (n : Nat) (rows : System n) :
    ((solutionCodec n).encode (solve n rows)).length ≤ (n + 1) * (n + 1) + 1 :=
  solve_solution_bound n rows

private def twoRows : AffineMap 2 1 := ((true, true), ((false, true), ()))
private def duplicatedRows : AffineMap 2 1 := ((true, true), ((true, true), ()))
private def mixedPivot : Affine 2 := (true, (false, true))

example : mapBits (freeMap (n := 0) (k := 0) ()) = [true, false] := rfl
example : mapBits (freeMap twoRows) =
    [true, false, false, false, true, true, false, false, true] := rfl
example : mapBits (pivotMap mixedPivot twoRows) = [true, false, true, true, false, true] := rfl
example : mapBits (pivotMap (n := 2) (k := 1) (true, (true, false)) duplicatedRows) =
    [false, false, true, true, true, true] := rfl
example : mapBits (pivotMap (n := 0) (k := 2) true ()) = [false, false, true] := rfl

-- These reduce the actual instruction program, rather than invoking its theorem.
set_option maxRecDepth 4096 in
example : BitRegister.run MatrixFreeInstructions.program (MatrixFreeInstructions.fuel 0 0 + 1)
    ⟨.running 0, (MatrixFreeInstructions.raising (n := 0) (k := 0) () [] []).store⟩ =
    ⟨.accepted, ({base 2 [] with output := [true, false]}).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run MatrixFreeInstructions.program (MatrixFreeInstructions.fuel 1 0 + 1)
    ⟨.running 0, (MatrixFreeInstructions.raising (n := 1) (k := 0) (true, ()) [true] []).store⟩ =
    ⟨.accepted, ({base 2 [true] with output := [true, false, false, true]}).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run MatrixPivotMapInstructions.program
    (MatrixPivotMapInstructions.fuel (n := 0) 0 true + 1)
    ⟨.running 0, (MatrixPivotMapInstructions.start (n := 0) (k := 0) true () []).store⟩ =
    ⟨.accepted, ({base 1 [] with output := [true]}).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run MatrixPivotMapInstructions.program
    (MatrixPivotMapInstructions.fuel (n := 1) 0 (true, true) + 1)
    ⟨.running 0, (MatrixPivotMapInstructions.start (n := 1) (k := 0) (true, true) (true, ()) [true]).store⟩ =
    ⟨.accepted, ({base 1 [true] with output := [false, true]}).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run MatrixPivotMapInstructions.program
    (MatrixPivotMapInstructions.fuel (n := 1) 0 (false, true) + 1)
    ⟨.running 0, (MatrixPivotMapInstructions.start (n := 1) (k := 0) (false, true) (true, ()) [true]).store⟩ =
    ⟨.accepted, ({base 1 [true] with output := [true, true]}).store⟩ := rfl

example {n k : Nat} (m : AffineMap n k) (saved : BitString) :
    Exec MatrixFreeInstructions.block (MatrixFreeInstructions.raising m saved []).store
      (MatrixFreeInstructions.fuel n k)
      ({base (k + 2) saved with output := mapBits (freeMap m)}).store :=
  MatrixFreeInstructions.block_exec m saved
example (n k : Nat) : MatrixFreeInstructions.fuel n k ≤ 20 * (k + 2) * (n + 1) :=
  MatrixFreeInstructions.fuel_bound n k
example {n k : Nat} (p : Affine n) (m : AffineMap n k) :
    Exec MatrixPivotMapInstructions.block (MatrixPivotMapInstructions.start p m (mapBits m)).store
      (MatrixPivotMapInstructions.fuel k p)
      ({base (k + 1) (mapBits m) with output := mapBits (pivotMap p m)}).store :=
  MatrixPivotMapInstructions.block_exec p m
example {n : Nat} (k : Nat) (p : Affine n) :
    MatrixPivotMapInstructions.fuel k p ≤ 30 * (k + 2) * (n + 1) :=
  MatrixPivotMapInstructions.fuel_bound k p

end PNP.Concrete.ResidualReduction.MatrixSolutionEncoding.Regression
