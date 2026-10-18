import PNP.Concrete.ResidualReduction.SourceChartApply
import Lean

/-! Exact pivot deletion, zero-direction rejection, arbitrary affine charting
and composed selection/transformation regressions. Runtime fixtures supplement
the general kernel proofs and do not award a proof checkpoint. -/

namespace PNP.Concrete.ResidualReduction.SourceChartApply.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.MatrixInstructions

private def factor : Affine 3 := (true,(false,(true,true)))
private def first : Point 3 := (true,(true,(false,())))
private def middle : Point 3 := (false,(true,(true,())))
private def last : Point 3 := (false,(false,(true,())))
private def zero : Point 3 := (false,(false,(false,())))

example : chooseChart first = some (0,(true,(false,()))) := rfl
example : chooseChart middle = some (1,(false,(true,()))) := rfl
example : chooseChart last = some (2,(false,(false,()))) := rfl
example : chooseChart zero = none := rfl
example : answer factor first = [true,true,false,true,true] := by decide
example : answer factor middle = [true,true,true,true,true] := by decide
example : answer factor last = [true,true,true,false,true] := by decide
example : answer factor zero = [false] := rfl
example : answer (n := 0) (false,true) (true,()) = [true,false,true] := rfl
example : answer (n := 0) (true,false) (false,()) = [false] := rfl

example (word : BitString) :
    ∃ ticks, ∃ out : Registers,
      Exec SourceChartSelection.block (SourceChartSelection.ready word).store ticks out.store ∧
      ticks ≤ 9 * word.length + 9 := SourceChartSelection.block_exec word
example {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) (t : Point n) :
    Exec SourceChartAffine.block (SourceChartAffine.ready f k t).store
      (SourceChartAffine.fuel n k.val) (SourceChartAffine.finished f k t).store :=
  SourceChartAffine.block_exec f k t
example {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) (t : Point n) (x : Point (n + 1)) :
    aEval (aShear t (cut n k f)) x = aEval f (unchart k t x) := by
  rw [aShear_eval]
  simpa only [cut_insert,unchart] using aEval_cut n k f (insert n k (shear t x))
example {n : Nat} (f : Affine (n + 1)) (v : Point (n + 1)) :
    ∃ ticks after, Exec block (initial f v) ticks after ∧
      ticks ≤ 31 * n + 39 ∧ after.get 8 = answer f v := block_exec f v
example {n : Nat} (v : Point (n + 1)) (c : Fin (n + 1) × Point n)
    (h : chooseChart v = some c) :
    (SourceEncoding.pointCodec (n + 1)).encode (insert n c.1 (true,c.2)) =
      (SourceEncoding.pointCodec (n + 1)).encode v :=
  congrArg _ (chooseChart_sound v c h)

#eval (show IO Unit from do
  let scans : List (BitString × Nat × BitString × BitString) :=
    [([],0,[],[]),([false,false,false],3,[],[]),([true],0,[],[true]),
     ([false,true],1,[false],[true]),
     ([false,false,true,false,true],2,[false,false,false,true],[true]),
     ([true,false,true],0,[false,true],[true])]
  for (word,pivot,tail,flag) in scans do
    let final := BitRegister.run (SourceChartSelection.block.program 0 8)
      (9 * word.length + 10) ⟨.running 0,(SourceChartSelection.ready word).store⟩
    if final.control != .accepted || final.store.get 1 != natural pivot ||
        final.store.get 4 != flag || final.store.get 8 != tail || final.store.get 0 != [] then
      throw (IO.userError "First-pivot scan regression failed")
  let factors : List (Sigma fun n => Fin (n + 1) × Affine (n + 1) × Point n) :=
    [⟨0,0,(false,true),()⟩,⟨0,0,(true,false),()⟩,
     ⟨1,0,(true,(false,true)),(true,())⟩,
     ⟨1,1,(false,(true,false)),(true,())⟩,
     ⟨2,0,factor,(true,(false,()))⟩,
     ⟨2,1,factor,(false,(true,()))⟩,
     ⟨2,2,factor,(true,(false,()))⟩,
     ⟨2,2,(false,(true,(false,false))),(true,(true,()))⟩]
  for ⟨n,k,f,t⟩ in factors do
    let final := BitRegister.run (SourceChartAffine.block.program 0 8)
      (SourceChartAffine.fuel n k.val + 1) ⟨.running 0,(SourceChartAffine.ready f k t).store⟩
    if final.control != .accepted || final.store.get 8 != affineWord (aShear t (cut n k f)) ||
        final.store.get 0 != [] || final.store.get 1 != List.replicate n true ||
        final.store.get 7 != (SourceEncoding.pointCodec n).encode t then
      throw (IO.userError "Affine chart execution regression failed")
  let combined : List (Sigma fun n => Affine (n + 1) × Point (n + 1)) :=
    [⟨0,(false,true),(true,())⟩,⟨0,(true,false),(false,())⟩,
     ⟨1,(true,(false,true)),(false,(true,()))⟩,
     ⟨1,(false,(true,false)),(true,(true,()))⟩,
     ⟨2,factor,first⟩,⟨2,factor,middle⟩,⟨2,factor,last⟩,⟨2,factor,zero⟩]
  for ⟨n,f,v⟩ in combined do
    let final := BitRegister.run (block.program 0 8) (31 * n + 40)
      ⟨.running 0,initial f v⟩
    if final.control != .accepted || final.store.get 8 != answer f v ||
        final.store.get 9 != affineWord f || final.store.get 10 != List.replicate n true then
      throw (IO.userError "Computed chart application regression failed")
  IO.println "CHART_CONSTRUCTION_RUNTIME_REGRESSIONS_GREEN: 22 executions")

run_cmd do
  for name in [
    ``SourceChartCoordinates.point_cons,
    ``SourceChartCoordinates.firstOne_none_bytes,
    ``SourceChartCoordinates.firstOne_split,
    ``SourceChartCoordinates.chosen_split,
    ``SourceChartCoordinates.absent_bytes,
    ``SourceChartSelection.found_exec,
    ``SourceChartSelection.scan_found_exec,
    ``SourceChartSelection.scan_absent_exec,
    ``SourceChartSelection.block_found_exec,
    ``SourceChartSelection.block_absent_exec,
    ``SourceChartSelection.word_cases,
    ``SourceChartSelection.block_exec,
    ``SourceChartSelection.chosen_exec,
    ``SourceChartSelection.absent_exec,
    ``SourceChartAffine.cut_words,
    ``SourceChartAffine.readPivot_exec,
    ``SourceChartAffine.cut_exec,
    ``SourceChartAffine.block_exec,
    ``SourceChartAffine.fuel_bound,
    ``SourceChartApply.construct_exec,
    ``SourceChartApply.chosen_exec,
    ``SourceChartApply.absent_exec,
    ``SourceChartApply.output_get,
    ``SourceChartApply.block_exec] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceChartSelection.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceChartAffine.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceChartApply.block_exec

end PNP.Concrete.ResidualReduction.SourceChartApply.Regression
