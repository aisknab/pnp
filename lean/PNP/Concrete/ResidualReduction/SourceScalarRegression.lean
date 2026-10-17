import PNP.Concrete.ResidualReduction.SourceScalarFamily
import Lean

/-! All-family scalar contracts and focused execution boundaries: empty and
zero-dimensional sources, ignored rows, repeated-row cancellation, nonzero
incoming accumulators, charted families, suffix preservation and derived widths.
Strict axiom guards cover every public theorem in the constructor. -/

namespace PNP.Concrete.ResidualReduction.SourceScalarFamily.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceScalarState

private def x : Affine 2 := (true,(false,false))
private def y : Affine 2 := (false,(true,false))
private def one : Affine 2 := (false,(false,true))
private def r : Row 2 := ⟨true,x,y⟩
private def mixed : Family 2 := [r,⟨false,one,one⟩,⟨true,aAdd x one,y⟩]
private def f : Affine 3 := (true,(false,(true,true)))
private def g : Affine 3 := (false,(true,(true,false)))
private def large : Family 3 := [⟨true,f,g⟩,⟨false,g,g⟩,⟨true,aAdd f g,aConst 3 true⟩]
private def charted : Family 2 := SourceChartFamily.result [r,{r with selected := false}]
  (false,(true,())) 1 (true,())

example : SourceQuadraticEncoding.word (scalar (n := 0) []) = [false] := rfl
example : SourceQuadraticEncoding.word (scalar (n := 3) []) = List.replicate 7 false := rfl
example : SourceQuadraticEncoding.word (scalar [{r with selected := false}]) = List.replicate 4 false := rfl
example : SourceQuadraticEncoding.word (scalar [r,r]) = List.replicate 4 false := rfl
example : SourceQuadraticEncoding.word (scalar [r,r,r]) = [true,false,false,false] := rfl
example : SourceQuadraticEncoding.word (scalar mixed) = [false,false,true,false] := rfl
example : SourceScalarRow.fuel 0 false = 13 := rfl
example : SourceScalarRow.fuel 0 true = 69 := rfl
example : SourceScalarInitialization.fuel 0 = 15 := rfl
example : fuel (n := 0) [] = 17 := rfl
example : fuel (n := 0) [⟨true,true,true⟩] = 87 := rfl
example : fuel (n := 3) [] = 65 := rfl

example {n : Nat} (F : Family n) (q : Quadratic n) :
    Exec rowLoop (state (familyBits F) q) (loopFuel F) (state [] (qAdd q (scalar F))) :=
  loop_exec F q
example {n : Nat} (F : Family n) :
    Exec block (initial n (familyBits F)) (fuel F) (finished (scalar F)) := block_exec F
example {n : Nat} (F : Family n) :
    fuel F ≤ sourceBound (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := fuel_source_bound F
example {n : Nat} (F : Family n) :
    (SourceQuadraticEncoding.codec n).decode ((finished (scalar F)).get 8) = some (scalar F) := output_decode F

private def expectStore (final : BitRegister.Configuration 16) (expected : Store 16) (label : String) : IO Unit := do
  if final.control != .accepted then
    throw (IO.userError (label ++ ": instruction bound exhausted"))
  for index in List.finRange 16 do
    if final.store.get index != expected.get index then
      throw (IO.userError (label ++ ": exact register-state mismatch"))

private def checkInitialization (n : Nat) : IO Unit := do
  let input := [false,true,true,false,false,true]
  let final := BitRegister.run (SourceScalarInitialization.block.program 0 8)
    (SourceScalarInitialization.fuel n + 1) ⟨.running 0,initial n input⟩
  expectStore final (state input (zero n)) "Scalar initialization"

private def checkRow {n : Nat} (a : Row n) : IO Unit := do
  let suffix := [true,false,false,true,false]
  let savedStream := [false,true,false]
  let q := qAdd (qProduct a.left a.right) (qOfAffine (aConst n true))
  let before := full (work (rowWord a ++ suffix)) emptySaved (data savedStream q)
  let final := BitRegister.run (SourceScalarRow.block.program 0 8)
    (SourceScalarRow.fuel n a.selected + 1) ⟨.running 0,before⟩
  expectStore final (state suffix (SourceScalarState.step q a)) "Scalar row"

private def checkFamily {n : Nat} (F : Family n) : IO Unit := do
  let final := BitRegister.run (block.program 0 8) (fuel F + 1) ⟨.running 0,initial n (familyBits F)⟩
  expectStore final (finished (scalar F)) "Complete scalar"
  let q := qAdd (scalar F) (qOfAffine (aConst n true))
  let loopRun := BitRegister.run (rowLoop.program 0 8) (loopFuel F + 1) ⟨.running 0,state (familyBits F) q⟩
  expectStore loopRun (state [] (qAdd q (scalar F))) "Scalar accumulator"

private def checkAdd {n : Nat} (p q : Quadratic n) : IO Unit := do
  let suffix := [false,true,false,true]
  let saved : SourceQuadraticProduct.Saved := ⟨[true,false],[false,true]⟩
  let before := full {work [] with output := SourceQuadraticEncoding.word p} saved (data suffix q)
  let final := BitRegister.run (SourceScalarRow.accumulate.program 0 8)
    (SourceScalarRow.addFuel n + 1) ⟨.running 0,before⟩
  expectStore final (state suffix (qAdd q p)) "Scalar xor and scratch cleanup"

#eval (show IO Unit from do
  for n in [0,1,2,3,5,8] do checkInitialization n
  for b in [false,true] do
    for a in [false,true] do
      for c in [false,true] do checkRow (n := 0) ⟨b,a,c⟩
    checkRow (n := 1) ⟨b,(true,true),(true,false)⟩
    checkRow {r with selected := b}
    checkRow (n := 2) ⟨b,aAdd x one,aAdd y one⟩
    checkRow (n := 3) ⟨b,f,g⟩
  checkFamily (n := 0) []
  checkFamily (n := 3) []
  checkFamily (n := 0) [⟨false,true,true⟩]
  checkFamily (n := 0) [⟨true,true,true⟩]
  checkFamily (n := 0) [⟨true,true,false⟩,⟨true,false,true⟩]
  checkFamily (n := 1) [⟨true,(true,false),(true,false)⟩]
  checkFamily (n := 1) [⟨false,(true,true),(true,true)⟩]
  checkFamily [r]
  checkFamily [r,r]
  checkFamily [r,r,r]
  checkFamily mixed
  checkFamily large
  checkFamily charted
  checkFamily (n := 5) [⟨true,aConst 5 true,aConst 5 true⟩,⟨false,aConst 5 false,aConst 5 true⟩]
  checkAdd (n := 0) true false
  checkAdd (qProduct x y) (qProduct (aAdd x one) y)
  checkAdd (qProduct f g) (qOfAffine (aConst 3 true))
  checkAdd (zero 5) (qOfAffine (aConst 5 true))
  IO.println "SCALAR_FAMILY_RUNTIME_REGRESSIONS_GREEN: 54 executions")

run_cmd do
  for name in [
    ``SourceScalarState.add_assoc,
    ``SourceScalarState.add_zero_left,
    ``SourceScalarState.add_zero_right,
    ``SourceScalarState.step_scalar,
    ``SourceScalarState.core_exec,
    ``SourceScalarState.product_exec,
    ``SourceScalarState.output_get,
    ``SourceScalarState.input_get,
    ``SourceScalarInitialization.zero_exec,
    ``SourceScalarInitialization.triangle_bits,
    ``SourceScalarInitialization.outer_exec,
    ``SourceScalarInitialization.outerFuel_exact,
    ``SourceScalarInitialization.block_exec,
    ``SourceScalarInitialization.fuel_exact,
    ``SourceScalarInitialization.fuel_bound,
    ``SourceScalarRow.factor_exec,
    ``SourceScalarRow.load_exec,
    ``SourceScalarRow.accumulate_exec,
    ``SourceScalarRow.selected_exec,
    ``SourceScalarRow.skip_exec,
    ``SourceScalarRow.block_exec,
    ``SourceScalarRow.fuel_le_selected,
    ``SourceScalarRow.selected_fuel,
    ``SourceScalarFamily.loop_exec,
    ``SourceScalarFamily.loopFuel_bound,
    ``SourceScalarFamily.block_exec,
    ``SourceScalarFamily.output_get,
    ``SourceScalarFamily.output_decode,
    ``SourceScalarFamily.output_length,
    ``SourceScalarFamily.rowFuel_bound,
    ``SourceScalarFamily.rowBound_mono,
    ``SourceScalarFamily.fuel_source_bound,
    ``SourceScalarFamily.output_source_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceScalarInitialization.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceScalarRow.selected_exec
#print axioms PNP.Concrete.ResidualReduction.SourceScalarFamily.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceScalarFamily.fuel_source_bound

end PNP.Concrete.ResidualReduction.SourceScalarFamily.Regression
