import Lean
import PNP.Concrete.ResidualReduction.SourceLinePreparedQuery
import PNP.Concrete.ResidualReduction.SourceLineWitnessRegression

namespace PNP.Concrete.ResidualReduction.SourceLineOutput.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceLinePreparedQuery

private def alpha : Affine 2 := (true, (false, true))
private def diagonal : Affine 2 := (true, (true, false))
private def linear : Row 2 := ⟨true, aConst 2 true, (false, (true, false))⟩
private def sample : Row 2 := ⟨true, alpha, (false, (true, false))⟩
private def expected : LineWitness 2 1 := ⟨(true, ()), (false, (false, ())), (false, (true, ()))⟩
private def diagonalExpected : LineWitness 2 1 := ⟨(true, ()), (false, (false, ())), (true, (true, ()))⟩

example : sourceLineQuery [linear] alpha = some expected := rfl
example : sourceLineQuery [linear] diagonal = some diagonalExpected := rfl
example : (codec 2 1).encode (some expected) = [true, true, false, false, false, true] := rfl
example : (codec 2 1).encode (some diagonalExpected) = [true, true, false, false, true, true] := rfl
example : (codec 2 1).decode [true, true, false, false, false, true] = some (some expected) := rfl
example : (codec 2 1).decode [true, true, false, false, false] = none := rfl
example : (codec 2 1).decode [true, true, false, false, false, true, false] = none := rfl
example : (codec 2 1).decode [false] = some none := rfl
example : (codec 2 1).decode [false, true] = none := rfl
example : (codec 2 1).decode [] = none := rfl
example : (codec 0 0).encode (some ⟨(), (), ()⟩) = [true] := rfl
example : (codec 0 0).decode [true] = some (some ⟨(), (), ()⟩) := rfl
example : (codec 0 0).decode [false] = some none := rfl

private def ProgramProduces {n : Nat} (F : Family n) (a : Affine n) (word : BitString) : Prop :=
  ∃ steps after, BitRegister.run SourceLinePreparedQuery.program steps
      ⟨.running 0, SourceLinePullback.start F a⟩ = ⟨.accepted, after⟩ ∧ after.get 8 = word ∧
    steps ≤ SourceLinePreparedQuery.costPolynomial.eval
      (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1
private theorem program_produces {n : Nat} (F : Family n) (a : Affine n) (word : BitString)
    (bytes : (codec n F.length).encode (sourceLineQuery F a) = word) : ProgramProduces F a word :=
  ⟨SourceLinePreparedQuery.fuel F a + 1, SourceLinePreparedQuery.result F a,
    SourceLinePreparedQuery.program_run F a, (result_output F a).trans bytes,
    Nat.add_le_add_right (SourceLinePreparedQuery.original_input_bound F a) 1⟩

-- The original direction has two coordinates, not the one-bit search parameter.
example : ProgramProduces [linear] alpha [true, true, false, false, false, true] :=
  program_produces [linear] alpha _ rfl
example : ProgramProduces [linear] diagonal [true, true, false, false, true, true] :=
  program_produces [linear] diagonal _ rfl
example : ProgramProduces [sample] alpha [false] := program_produces [sample] alpha _ rfl
example : ProgramProduces [sample] (aConst 2 false) [false] := program_produces [sample] (aConst 2 false) _ rfl
example : ProgramProduces ([] : Family 2) alpha [false] := program_produces ([] : Family 2) alpha _ rfl
example : ProgramProduces ([] : Family 0) true [false] := program_produces ([] : Family 0) true _ rfl
example : ProgramProduces (n := 0) [⟨true, true, false⟩] true [false] :=
  program_produces (n := 0) [⟨true, true, false⟩] true _ rfl

private def dirty (word : BitString) : Registers :=
  ⟨[true, false], [false], [true, false], [false], [false, true], [true], [true, true], [false], word⟩
private def liftData {j n k : Nat} (joint : Point j) (forms : AffineMap n k) : Store 29 :=
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons ((SourceEncoding.pointCodec j).encode joint) <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons (mapBits forms) <|
  .cons (List.replicate k true) <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .nil

private def LiftProduces {j n k : Nat} (joint : Point j) (forms : AffineMap n k) (z : Point k) (word : BitString) : Prop :=
  ∃ after, Exec success (SourceWitnessLift.store (dirty ((SourceEncoding.pointCodec k).encode z)) (liftData joint forms))
      (successFuel j n k) after ∧ after.get 8 = word ∧
    after.get 28 = mapBits forms ∧ after.get 29 = List.replicate k true
private theorem lift_produces {j n k : Nat} (joint : Point j) (forms : AffineMap n k) (z : Point k) (word : BitString)
    (bytes : true :: pairBytes joint forms z = word) : LiftProduces joint forms z word := by
  refine ⟨SourceWitnessLift.store (SourceLineOutput.finished joint forms z) (liftData joint forms),
    success_exec (dirty ((SourceEncoding.pointCodec k).encode z)) (liftData joint forms)
      joint forms z rfl rfl rfl rfl, ?_⟩
  exact ⟨(Frame.get_core _ _ (8 : Fin 9)).trans bytes, rfl, rfl⟩

private def joint : Point 3 := (true, (false, (true, ())))
private def forms : AffineMap 2 1 := ((true, true), ((false, true), ()))
private def z : Point 1 := (true, ())
private def constants : AffineMap 2 0 := (true, (false, ()))
example : linearMapEval forms z = (true, (false, ())) := rfl
example : mapEval forms z = (false, (true, ())) := rfl
example : LiftProduces joint forms z [true, true, false, true, true, false] :=
  lift_produces joint forms z _ rfl
example : LiftProduces joint constants () [true, true, false, true, false, false] :=
  lift_produces joint constants () _ rfl
example : LiftProduces (j := 0) () forms z [true, true, false] := lift_produces (j := 0) () forms z _ rfl
example : LiftProduces joint (n := 0) (k := 1) () z [true, true, false, true] :=
  lift_produces joint (n := 0) (k := 1) () z _ rfl
example : LiftProduces (j := 0) (n := 0) (k := 0) () () () [true] :=
  lift_produces (j := 0) (n := 0) (k := 0) () () () _ rfl
example : successFuel 0 0 0 = 15 := rfl
example (s : Store 38) : (BitRegister.run (reject.program 0 8) 3 ⟨.running 0, s⟩).store.get 8 = [false] :=
  (congrArg (fun c => c.store.get (8 : Fin 38)) ((reject_exec s).program_run 0 8)).trans (rejected_output s)

-- Generic original-source claims cover all finite dimensions and families.
example {n : Nat} (F : Family n) (a : Affine n) :
    Exec SourceLinePreparedQuery.block (SourceLinePullback.start F a)
      (SourceLinePreparedQuery.fuel F a) (SourceLinePreparedQuery.result F a) := SourceLinePreparedQuery.block_exec F a
example {n : Nat} (F : Family n) (a : Affine n) :
    (SourceLinePreparedQuery.result F a).get 8 = (codec n F.length).encode (sourceLineQuery F a) :=
  result_output F a
example {n : Nat} (F : Family n) (a : Affine n) :
    SourceLinePreparedQuery.fuel F a ≤ SourceLinePreparedQuery.costPolynomial.eval
      (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length := SourceLinePreparedQuery.original_input_bound F a
example {n : Nat} (F : Family n) (a : Affine n) :
    ((SourceLinePreparedQuery.result F a).get 8).length ≤
      3 * (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1 := output_original_bound F a
example {n : Nat} (F : Family n) (a : Affine n) (w : LineWitness n F.length)
    (h : (codec n F.length).decode ((SourceLinePreparedQuery.result F a).get 8) = some (some w)) :
    LineGood F a w := decoded_sound F a w h
example {n : Nat} (F : Family n) (a : Affine n) :
    (codec n F.length).decode ((SourceLinePreparedQuery.result F a).get 8) = some none ↔ ¬ ∃ w, LineGood F a w :=
  decoded_none_iff F a

run_cmd do
  for name in [
    ``SourceLineOutput.point_append_bytes,
    ``SourceLineOutput.some_bytes,
    ``SourceLineOutput.none_bytes,
    ``SourceLineOutput.lift_bytes,
    ``SourceLineOutput.bytes_bound,
    ``SourceLineOutput.roundtrip,
    ``SourceLineOutput.load_exec,
    ``SourceLineOutput.clear_exec,
    ``SourceLineOutput.seed_exec,
    ``SourceLineOutput.success_exec,
    ``SourceLineOutput.reject_exec,
    ``SourceLineOutput.rejected_output,
    ``SourceLineOutput.costPolynomial_eval,
    ``SourceLineOutput.bounded_cost,
    ``SourceLinePreparedQuery.selection_raw,
    ``SourceLinePreparedQuery.retained_map,
    ``SourceLinePreparedQuery.retained_width,
    ``SourceLinePreparedQuery.retained_joint,
    ``SourceLinePreparedQuery.lift_exec,
    ``SourceLinePreparedQuery.finish_exec,
    ``SourceLinePreparedQuery.block_exec,
    ``SourceLinePreparedQuery.result_output,
    ``SourceLinePreparedQuery.finish_original_bound,
    ``SourceLinePreparedQuery.original_input_bound,
    ``SourceLinePreparedQuery.output_original_bound,
    ``SourceLinePreparedQuery.program_run,
    ``SourceLinePreparedQuery.exact_decoded_output,
    ``SourceLinePreparedQuery.decoded_sound,
    ``SourceLinePreparedQuery.decoded_none_iff] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceLineOutput.success_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLinePreparedQuery.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLinePreparedQuery.result_output
#print axioms PNP.Concrete.ResidualReduction.SourceLinePreparedQuery.original_input_bound
#print axioms PNP.Concrete.ResidualReduction.SourceLinePreparedQuery.exact_decoded_output
#print axioms PNP.Concrete.ResidualReduction.SourceLinePreparedQuery.decoded_sound
#print axioms PNP.Concrete.ResidualReduction.SourceLinePreparedQuery.decoded_none_iff

end PNP.Concrete.ResidualReduction.SourceLineOutput.Regression
