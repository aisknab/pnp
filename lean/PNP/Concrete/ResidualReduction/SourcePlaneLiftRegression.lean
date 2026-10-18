import Lean
import PNP.Concrete.ResidualReduction.SourcePlanePreparedQuery
import PNP.Concrete.ResidualReduction.SourcePlanePipelineRegression

namespace PNP.Concrete.ResidualReduction.SourcePlaneLift.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourcePlane

private def forms : AffineMap 3 2 :=
  ((true, (true, true)), ((false, (true, true)), ((true, (false, false)), ())))
private def both : Point 2 := (true, (true, ()))
private def constants : AffineMap 2 0 := (true, (false, ()))
example : SourceLinearMap.value (k := 2) (true, (true, true)) both = false := rfl
example : aEval (n := 2) (true, (true, true)) both = true := rfl
example : linearMapEval forms both = (false, (true, (true, ()))) := rfl
example : mapEval forms both = (true, (false, (true, ()))) := rfl
example : linearMapEval forms (zeroPoint 2) = (false, (false, (false, ()))) := rfl
example : mapBits constants = [true, false] := rfl
example : linearMapEval constants () = (false, (false, ())) := rfl
example : linearMapEval (n := 0) (k := 2) () both = () := rfl
example : SourceLinearMap.fuel 2 0 = 32 := rfl
example : (BitRegister.run SourceLinearMap.program 33
    ⟨.running 0, (SourceLinearMap.ready (k := 0) () (mapBits constants) []).store⟩).store.get 8 = [false, false] := by
  exact congrArg (fun s => s.store.get 8) (SourceLinearMap.program_run constants ())
example : (BitRegister.run SourceLinearMap.program (SourceLinearMap.fuel 3 2 + 1)
    ⟨.running 0, (SourceLinearMap.ready both (mapBits forms) []).store⟩).store.get 8 = [false, true, true] := by
  rw [SourceLinearMap.program_run forms both]
  rfl
example : (BitRegister.run SourceLinearMap.program 5
    ⟨.running 0, (SourceLinearMap.ready both [] []).store⟩).control = .accepted := by
  exact congrArg (fun s => s.control) (SourceLinearMap.program_run (n := 0) (k := 2) () both)

private def data {n k : Nat} (forms : AffineMap n k) (m : Nat) : SourcePlanePipeline.Saved :=
  ⟨[], [], [], mapBits forms, List.replicate k true, List.replicate m true, List.replicate n true⟩
private def dirty (output : BitString) : Registers :=
  ⟨[false], [false], [true], [false], [true], [true], [false], [true], output⟩
private def LiftProduces {m n k : Nat} (forms : AffineMap n k)
    (witness : Option (Point m × Point k)) (word : BitString) : Prop :=
  ∃ used after, Exec block
      (store (dirty ((SourceAffineOutput.witnessCodec m k).encode witness)) (Store.empty 13) (data forms m)) used after ∧
    after.get 8 = word ∧ used ≤ successFuel m n k + 1
private theorem lift_produces {m n k : Nat} (forms : AffineMap n k)
    (witness : Option (Point m × Point k)) (word : BitString)
    (expected : (SourceAffineOutput.witnessCodec m n).encode (witness.map (translated forms)) = word) :
    LiftProduces forms witness word := by
  obtain ⟨used, after, checked, bytes, bound⟩ := block_exec
    (dirty ((SourceAffineOutput.witnessCodec m k).encode witness)) (Store.empty 13) (data forms m) forms witness rfl rfl rfl rfl
  exact ⟨used, store after (Store.empty 13) (data forms m), checked,
    (store_output after (Store.empty 13) (data forms m)).trans (bytes.trans expected), bound⟩

example : LiftProduces (m := 2) forms (some ((true, (false, ())), both)) [true, true, false, false, true, true] :=
  lift_produces forms _ _ rfl
example : LiftProduces forms (m := 2) none [false] := lift_produces forms _ _ rfl
example : LiftProduces (m := 1) constants (some ((true, ()), ())) [true, true, false, false] :=
  lift_produces constants _ _ rfl
example : LiftProduces (m := 0) forms (some ((), both)) [true, false, true, true] := lift_produces forms _ _ rfl
example : LiftProduces (m := 1) (n := 0) (k := 2) () (some ((true, ()), both)) [true, true] :=
  lift_produces (n := 0) (k := 2) () _ _ rfl

private def linear : Row 2 := ⟨false, (true, (false, false)), (false, (false, true))⟩
private def diagonal : Affine 2 := (true, (true, false))
private def inactive : Row 2 := ⟨false, (false, (false, false)), (false, (false, true))⟩
private def alpha : Affine 2 := (true, (false, true))
private def beta : Affine 2 := (false, (true, true))
-- The original witness is not the one-bit parameter vector: both original
-- coordinates change, and the original weight vector is preserved.
example : (directionSpace [linear] [diagonal, diagonal]).parameters = 1 := rfl
example : planeRawQuery [linear] diagonal diagonal = some ((true, ()), (true, ())) := rfl
example : sourcePlaneQuery [linear] diagonal diagonal = some ((true, ()), (true, (true, ()))) := rfl
example : sourcePlaneQuery [inactive, linear] diagonal diagonal =
    some ((false, (true, ())), (true, (true, ()))) := rfl
example : sourcePlaneQuery [inactive] diagonal diagonal = none := rfl
example : sourcePlaneQuery ([] : Family 2) alpha beta = none := rfl
example : sourcePlaneQuery ([] : Family 0) true false = none := rfl

private def ProgramProduces {n : Nat} (F : Family n) (a b : Affine n) (word : BitString) : Prop :=
  ∃ used after, BitRegister.run SourcePlanePreparedQuery.program (used + 1)
      ⟨.running 0, SourcePlanePipeline.start F a b⟩ = ⟨.accepted, after⟩ ∧ after.get 8 = word ∧
    used ≤ SourcePlanePreparedQuery.costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length
private theorem program_produces {n : Nat} (F : Family n) (a b : Affine n) (word : BitString)
    (expected : (SourceAffineOutput.witnessCodec F.length n).encode (sourcePlaneQuery F a b) = word) :
    ProgramProduces F a b word := by
  obtain ⟨used, after, checked, bytes, bound⟩ := SourcePlanePreparedQuery.program_run F a b
  exact ⟨used, after, checked, bytes.trans expected, bound⟩
example : ProgramProduces [linear] diagonal diagonal [true, true, true, true] :=
  program_produces [linear] diagonal diagonal _ rfl
example : ProgramProduces [inactive, linear] diagonal diagonal [true, false, true, true, true] :=
  program_produces [inactive, linear] diagonal diagonal _ rfl
example : ProgramProduces [inactive] diagonal diagonal [false] := program_produces [inactive] diagonal diagonal _ rfl
example : ProgramProduces ([] : Family 2) alpha beta [false] := program_produces ([] : Family 2) alpha beta _ rfl
example : ProgramProduces ([] : Family 0) true false [false] := program_produces ([] : Family 0) true false _ rfl
example : PlaneGood [linear] diagonal diagonal ((true, ()), (true, (true, ()))) :=
  sourcePlaneQuery_sound [linear] diagonal diagonal _ rfl
example {n : Nat} (F : Family n) (a b : Affine n) :
    ∃ used after, BitRegister.run SourcePlanePreparedQuery.program (used + 1)
        ⟨.running 0, SourcePlanePipeline.start F a b⟩ = ⟨.accepted, after⟩ ∧
      (SourceAffineOutput.witnessCodec F.length n).decode (after.get 8) = some (sourcePlaneQuery F a b) ∧
      used ≤ SourcePlanePreparedQuery.costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length :=
  SourcePlanePreparedQuery.exact_decoded_output F a b

run_cmd do
  for name in [
    ``SourceLinearMap.value_zero, ``SourceLinearMap.value_cons, ``SourceLinearMap.point_bits_cons,
    ``SourceLinearMap.linearMap_cons, ``SourceLinearMap.readSign_exec, ``SourceLinearMap.accumulate_exec,
    ``SourceLinearMap.dotStep_exec, ``SourceLinearMap.dotLoop_exec, ``SourceLinearMap.rowFinish_exec,
    ``SourceLinearMap.row_exec, ``SourceLinearMap.loop_exec, ``SourceLinearMap.reorder_exec,
    ``SourceLinearMap.block_exec, ``SourceLinearMap.space_exec, ``SourceLinearMap.fuel_mono,
    ``SourceLinearMap.costPolynomial_eval, ``SourceLinearMap.bounded_cost, ``SourceLinearMap.program_run,
    ``view_store, ``view_output, ``store_output, ``lift_exec, ``copySaved_exec, ``seed_exec,
    ``copyWeights_exec, ``prepare_exec, ``prepared_weights, ``success_exec, ``block_exec,
    ``costPolynomial_eval, ``bounded_cost, ``SourcePlanePreparedQuery.lift_exec,
    ``SourcePlanePreparedQuery.block_exec, ``SourcePlanePreparedQuery.program_run,
    ``SourcePlanePreparedQuery.output_bound, ``SourcePlanePreparedQuery.exact_decoded_output] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceLinearMap.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlanePreparedQuery.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlanePreparedQuery.exact_decoded_output

end PNP.Concrete.ResidualReduction.SourcePlaneLift.Regression
