import PNP.Concrete.ResidualReduction.SourceChartSelectedFamily
import Lean

/-! General family-constructor contracts and boundary fixtures: empty families,
zero-dimensional tails, early and late pivots, mixed replacement flags, repeated
rows, arbitrary surrounding bytes, canonical output and zero-direction rejection.
The fixtures supplement arbitrary-family proofs; they do not award progress. -/

namespace PNP.Concrete.ResidualReduction.SourceChartSelectedFamily.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceChartStream

private def firstRow : Row 2 := ⟨true,(true,(false,true)),(false,(true,false))⟩
private def otherRow : Row 2 := ⟨false,(false,(true,true)),(true,(true,false))⟩
private def family : Family 2 := [firstRow,otherRow,firstRow]
private def weights : Point family.length := (false,(true,(true,())))
private def expected : Family 2 :=
  [⟨false,(false,(true,true)),(true,(false,false))⟩,
   ⟨true,(true,(false,true)),(true,(true,false))⟩,
   ⟨true,(false,(true,true)),(true,(false,false))⟩]
private def small : Family 1 := [⟨true,(true,false),(false,true)⟩]
private def larger : Family 3 :=
  [⟨true,(true,(false,(true,true))),(false,(true,(false,false)))⟩,
   ⟨false,(false,(true,(true,false))),(true,(true,(false,true)))⟩]

example : SourceChartFamily.result family weights 1 (false,()) = expected := rfl
example : (SourceChartFamily.result family weights 1 (false,())).map Row.selected =
    [false,true,true] := rfl
example : (SourceChartFamily.result family weights 1 (false,())).length = 3 := rfl
example : SourceChartFamily.result (n := 2) [] () 2 (true,(false,())) = [] := rfl
example : (SourceEncoding.familyCodec 2).encode (SourceChartFamily.result family weights 1 (false,())) =
    natural 3 ++
      ([false,false,true,true,true,false,false] ++
       [true,true,false,true,true,true,false] ++
       [true,false,true,true,true,false,false]) := rfl
example : ((SourceEncoding.familyCodec 2).encode (SourceChartFamily.result family weights 1 (false,()))).length = 25 := rfl
example : answer family weights (false,(false,())) = [false] := rfl
example : answer (n := 2) [] () (false,(false,(true,()))) = [true,false] := rfl
example : answer family weights (false,(true,())) =
    true :: (SourceEncoding.familyCodec 2).encode expected := rfl
example : SourceChartFamily.result
    [{firstRow with selected := false},{otherRow with selected := true},{firstRow with selected := false}]
    (false,(true,(true,()))) 1 (false,()) = expected := rfl

example {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) (t : Point n)
    (suffix savedStream ws accumulator : BitString) :
    Exec SourceChartStream.block
      (full (work n (affineWord f ++ suffix)) (data k t savedStream ws accumulator))
      (SourceChartStream.fuel n k.val)
      (full (work n suffix) (data k t suffix ws ((affineWord (transformed f k t)).reverse ++ accumulator))) :=
  SourceChartStream.block_exec f k t suffix savedStream ws accumulator
example {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (t : Point n) :
    Exec SourceChartFamily.block (SourceChartFamily.rowInitial F w k t [])
      (SourceChartFamily.fuel n k.val F.length)
      (SourceChartFamily.finished k t ((SourceEncoding.familyCodec (n + 1)).encode (SourceChartFamily.result F w k t))) :=
  SourceChartFamily.block_exec F w k t
example {n : Nat} (F : Family (n + 1)) (w : Point F.length) (v : Point (n + 1)) :
    let L := (codec.encode ⟨n + 1,F⟩).length
    ∃ ticks after, Exec block (initial F w v) ticks after ∧
      ticks ≤ (70 * L + 159) * L + 40 ∧ after.get 8 = answer F w v := block_exec F w v
example {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (t : Point n) (x : Point (n + 1)) :
    models (SourceChartFamily.result F w k t) x = models F (unchart k t x) :=
  result_models F w k t x

private def checkFamily {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (t : Point n) : IO Unit := do
  let final := BitRegister.run (SourceChartFamily.block.program 0 8)
    (SourceChartFamily.fuel n k.val F.length + 1)
    ⟨.running 0,SourceChartFamily.rowInitial F w k t []⟩
  let expected := (SourceEncoding.familyCodec (n + 1)).encode (SourceChartFamily.result F w k t)
  if final.control != .accepted || final.store.get 8 != expected ||
      final.store.get 0 != [] || final.store.get 9 != [] ||
      final.store.get 13 != [] || final.store.get 14 != [] ||
      final.store.get 10 != List.replicate k.val true ||
      final.store.get 11 != (SourceEncoding.pointCodec n).encode t then
    throw (IO.userError "Full marked-family stream regression failed")

private def checkSelected {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (v : Point (n + 1)) : IO Unit := do
  let L := (codec.encode ⟨n + 1,F⟩).length
  let final := BitRegister.run (block.program 0 8) ((70 * L + 159) * L + 41) ⟨.running 0,initial F w v⟩
  if final.control != .accepted || final.store.get 8 != answer F w v ||
      final.store.get 0 != [] || final.store.get 12 != List.replicate (n + 2) true then
    throw (IO.userError "Selected family construction regression failed")
  match chooseChart v with
  | none =>
    if final.store.get 13 != (SourceEncoding.pointCodec F.length).encode w then
      throw (IO.userError "Rejected direction unexpectedly consumed weights")
  | some c =>
    if final.store.get 10 != List.replicate c.1.val true ||
        final.store.get 11 != (SourceEncoding.pointCodec n).encode c.2 ||
        final.store.get 13 != [] || final.store.get 14 != [] then
      throw (IO.userError "Selected chart data preservation regression failed")

#eval (show IO Unit from do
  let cases : List (Sigma fun n => Fin (n + 1) × Affine (n + 1) × Point n) :=
    [⟨0,0,(true,false),()⟩,⟨0,0,(false,true),()⟩,
     ⟨2,0,(true,(false,(true,true))),(false,(true,()))⟩,
     ⟨2,2,(false,(true,(false,true))),(true,(false,()))⟩]
  for ⟨n,k,f,t⟩ in cases do
    let suffix := [false,true,false,true]
    let old := [true,true,false]
    let ws := [false,true,true]
    let acc := [true,false,true,false]
    let final := BitRegister.run (SourceChartStream.block.program 0 8)
      (SourceChartStream.fuel n k.val + 1)
      ⟨.running 0,full (work n (affineWord f ++ suffix)) (data k t old ws acc)⟩
    if final.control != .accepted || final.store.get 0 != suffix || final.store.get 8 != [] ||
        final.store.get 9 != suffix || final.store.get 13 != ws ||
        final.store.get 14 != (affineWord (transformed f k t)).reverse ++ acc ||
        final.store.get 10 != List.replicate k.val true ||
        final.store.get 11 != (SourceEncoding.pointCodec n).encode t then
      throw (IO.userError "Framed factor stream regression failed")
  checkFamily (n := 0) [] () 0 ()
  checkFamily (n := 2) [] () 2 (true,(false,()))
  checkFamily small (false,()) 0 ()
  checkFamily family weights 0 (true,())
  checkFamily family weights 1 (false,())
  checkFamily larger (true,(false,())) 2 (true,(false,()))
  checkSelected (n := 0) [] () (true,())
  checkSelected (n := 2) [] () (false,(false,(true,())))
  checkSelected (n := 2) [] () (false,(false,(false,())))
  checkSelected small (true,()) (true,())
  checkSelected small (false,()) (false,())
  checkSelected family weights (false,(false,()))
  checkSelected family weights (true,(true,()))
  checkSelected family weights (false,(true,()))
  IO.println "CHART_FAMILY_RUNTIME_REGRESSIONS_GREEN: 18 executions")

run_cmd do
  for name in [
    ``SourceChartStream.block_exec,
    ``SourceChartStream.fuel_bound,
    ``SourceChartFamily.result_cons,
    ``SourceChartFamily.result_length,
    ``SourceChartFamily.output_bytes,
    ``SourceChartFamily.output_length,
    ``SourceChartFamily.takeWeight_exec,
    ``SourceChartFamily.row_exec,
    ``SourceChartFamily.rowLoop_exec,
    ``SourceChartFamily.unary_exec,
    ``SourceChartFamily.header_exec,
    ``SourceChartFamily.finish_exec,
    ``SourceChartFamily.block_exec,
    ``SourceChartFamily.output_get,
    ``SourceChartFamily.fuel_source_bound,
    ``SourceChartSelectedFamily.construct_exec,
    ``SourceChartSelectedFamily.chosen_exec,
    ``SourceChartSelectedFamily.absent_exec,
    ``SourceChartSelectedFamily.block_exec,
    ``SourceChartSelectedFamily.result_models] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceChartFamily.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceChartSelectedFamily.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceChartSelectedFamily.result_models

end PNP.Concrete.ResidualReduction.SourceChartSelectedFamily.Regression
