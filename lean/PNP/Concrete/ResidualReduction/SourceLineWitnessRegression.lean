import Lean
import PNP.Concrete.ResidualReduction.SourceLineWitnessBudget
import PNP.Concrete.ResidualReduction.SourceAxisWitnessRegression

namespace PNP.Concrete.ResidualReduction.SourceLineWitness.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

private def alpha : Affine 2 := (true, (false, true))
private def sample : Row 2 := ⟨true, alpha, (false, (true, false))⟩
private def linear : Row 2 := ⟨true, aConst 2 true, (false, (true, false))⟩

-- Original source entry contains neither maps nor transformed matrices.
example : (SourceLinePullback.start [linear] alpha).get 32 = [] :=
  (SourceLinePullback.initial_no_derived_data [linear] alpha).2.2.2.1
example : (SourceLinePullback.start [linear] alpha).get 34 = [] :=
  (SourceLinePullback.initial_no_derived_data [linear] alpha).2.2.2.2.1
example : (SourceLinePullback.start [linear] alpha).get 36 = [] :=
  (SourceLinePullback.initial_no_derived_data [linear] alpha).2.2.2.2.2.1
example : (SourceLinePullback.start [linear] alpha).get 37 = [] :=
  (SourceLinePullback.initial_no_derived_data [linear] alpha).2.2.2.2.2.2

private def ProgramProduces {n : Nat} (F : Family n) (a : Affine n)
    (answer : Option (BitString × BitString)) : Prop :=
  ∃ steps after, BitRegister.run program steps ⟨.running 0, SourceLinePullback.start F a⟩ =
      ⟨.accepted, after⟩ ∧ observed after = answer ∧
    steps ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1
private theorem program_produces {n : Nat} (F : Family n) (a : Affine n)
    (answer : Option (BitString × BitString)) (expected : queryBytes F a = answer) :
    ProgramProduces F a answer := by
  obtain ⟨steps, bound, checked⟩ := program_original_bound F a
  exact ⟨steps, result F a, checked, (result_exact F a).trans expected, bound⟩

-- The result is the original line-query witness, not its seed indices or
-- parameter pair. A missing route is not a claim of unsatisfiability.
example : queryBytes [linear] alpha = some ([true, false, false], [true]) := rfl
example : queryBytes [sample] alpha = none := rfl
example : ProgramProduces [linear] alpha (some ([true, false, false], [true])) :=
  program_produces [linear] alpha _ rfl
example : ProgramProduces [sample] alpha none := program_produces [sample] alpha _ rfl
example : ProgramProduces ([] : Family 2) alpha none := program_produces ([] : Family 2) alpha _ rfl
example : ProgramProduces ([] : Family 0) true none := program_produces ([] : Family 0) true _ rfl
example : ProgramProduces (n := 0) [⟨true, true, false⟩] true none :=
  program_produces (n := 0) [⟨true, true, false⟩] true _ rfl
example : ProgramProduces [sample] (aConst 2 false) none :=
  program_produces [sample] (aConst 2 false) _ rfl
example : finishFuel [sample] alpha = 2 := rfl
example : finishFuel ([] : Family 0) true = 2 := rfl
example : (parameterResult [sample] alpha).get 32 =
    [false, true, false, true, false, false, false, true, false] := retained_left_map [sample] alpha
example : (parameterResult [sample] alpha).get 34 = [true, false] := retained_right_map [sample] alpha
example : (parameterResult [sample] alpha).get 33 = [true, true] := retained_left_width [sample] alpha
example : (parameterResult [sample] alpha).get 35 = [true] := retained_right_width [sample] alpha

-- Both maps are independently non-identity and have nonzero affine offsets.
-- Only their homogeneous parts act on the recovered parameter vectors.
private def left : AffineMap 3 2 :=
  ((true, (true, true)), ((false, (true, true)), ((true, (false, false)), ())))
private def right : AffineMap 2 1 := ((true, true), ((false, true), ()))
private def x : Point 2 := (true, (true, ()))
private def y : Point 1 := (true, ())
private def constants : AffineMap 2 0 := (true, (false, ()))
private def dirty (word : BitString) : Registers :=
  ⟨[true, false], [false], [true], [false, true], [false], [true], [false], [true], word⟩
private def data {m n p q : Nat} (a : AffineMap m p) (b : AffineMap n q) (v : Point p) : Store 29 :=
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons [] <|
  .cons ((SourceEncoding.pointCodec p).encode v) <|
  .cons [] <|
  .cons [false, true] <|
  .cons [true, false] <|
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
  .cons (mapBits a) <|
  .cons (List.replicate p true) <|
  .cons (mapBits b) <|
  .cons (List.replicate q true) <|
  .cons [] <|
  .cons [] <|
  .nil
private def LiftProduces {m n p q : Nat} (a : AffineMap m p) (b : AffineMap n q)
    (v : Point p) (w : Point q) (first second : BitString) : Prop :=
  ∃ after, Exec SourceWitnessLift.block
      (SourceWitnessLift.store (dirty ((SourceEncoding.pointCodec q).encode w)) (data a b v))
      (SourceWitnessLift.fuel m n p q) after ∧
    after.get 20 = first ∧ after.get 8 = second ∧ after.get 4 = [true] ∧
    after.get 32 = mapBits a ∧ after.get 34 = mapBits b
private theorem lift_produces {m n p q : Nat} (a : AffineMap m p) (b : AffineMap n q)
    (v : Point p) (w : Point q) (first second : BitString)
    (hfirst : (SourceEncoding.pointCodec m).encode (linearMapEval a v) = first)
    (hsecond : (SourceEncoding.pointCodec n).encode (linearMapEval b w) = second) :
    LiftProduces a b v w first second := by
  have firstMap : (SourceWitnessLift.resultData (data a b v) a b v w).get 23 = mapBits a := by
    simp only [SourceWitnessLift.resultData, SourceWitnessLift.saveLeft, SourceWitnessLift.saveParameter,
      Store.get_set, show (23 : Fin 29) ≠ 11 by decide, show (23 : Fin 29) ≠ 10 by decide, if_false]
    rfl
  have secondMap : (SourceWitnessLift.resultData (data a b v) a b v w).get 25 = mapBits b := by
    simp only [SourceWitnessLift.resultData, SourceWitnessLift.saveLeft, SourceWitnessLift.saveParameter,
      Store.get_set, show (25 : Fin 29) ≠ 11 by decide, show (25 : Fin 29) ≠ 10 by decide, if_false]
    rfl
  refine ⟨SourceWitnessLift.store (SourceWitnessLift.resultCore b w)
      (SourceWitnessLift.resultData (data a b v) a b v w),
    SourceWitnessLift.block_exec (dirty ((SourceEncoding.pointCodec q).encode w)) (data a b v)
      a b v w rfl rfl rfl rfl rfl rfl, ?_⟩
  exact ⟨(SourceWitnessLift.result_left _ _ _ _ _).trans hfirst,
    (SourceWitnessLift.result_right _ _ _ _ _).trans hsecond,
    SourceWitnessLift.result_present _ _ _ _ _,
    (Frame.get_frame _ _ (23 : Fin 29)).trans firstMap,
    (Frame.get_frame _ _ (25 : Fin 29)).trans secondMap⟩

example : linearMapEval left x = (false, (true, (true, ()))) := rfl
example : mapEval left x = (true, (false, (true, ()))) := rfl
example : linearMapEval right y = (true, (false, ())) := rfl
example : mapEval right y = (false, (true, ())) := rfl
example : LiftProduces left right x y [false, true, true] [true, false] :=
  lift_produces left right x y _ _ rfl rfl
example : LiftProduces constants right () y [false, false] [true, false] :=
  lift_produces constants right () y _ _ rfl rfl
example : LiftProduces left constants x () [false, true, true] [false, false] :=
  lift_produces left constants x () _ _ rfl rfl
example : LiftProduces (m := 0) (p := 2) () right x y [] [true, false] :=
  lift_produces (m := 0) (p := 2) () right x y _ _ rfl rfl
example : LiftProduces left (n := 0) (q := 1) () x y [false, true, true] [] :=
  lift_produces left (n := 0) (q := 1) () x y _ _ rfl rfl
example : LiftProduces (m := 0) (n := 0) (p := 0) (q := 0) () () () () [] [] :=
  lift_produces (m := 0) (n := 0) (p := 0) (q := 0) () () () () _ _ rfl rfl

-- All-input theorems: no supplied basis, coverage, rank or witness premise.
example {n : Nat} (F : Family n) (a : Affine n) :
    Exec parameterBlock (SourceLinePullback.start F a) (parameterFuel F a) (parameterResult F a) :=
  parameter_exec F a
example {n : Nat} (F : Family n) (a : Affine n) :
    Exec block (SourceLinePullback.start F a) (fuel F a) (result F a) := block_exec F a
example {n : Nat} (F : Family n) (a : Affine n) :
    observed (result F a) = queryBytes F a := result_exact F a
example {n : Nat} (F : Family n) (a : Affine n) :
    fuel F a ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length :=
  original_input_bound F a
example {n : Nat} (F : Family n) (a : Affine n) (u v : BitString)
    (h : observed (result F a) = some (u, v)) :
    u.length = n + F.length ∧ v.length = (directionSpace F [a]).parameters := output_lengths F a u v h
example {n : Nat} (F : Family n) (a : Affine n) (u v : BitString)
    (h : observed (result F a) = some (u, v)) :
    u.length ≤ 2 * (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length ∧
      v.length ≤ (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length := output_original_bounds F a u v h
example {n : Nat} (F : Family n) (a : Affine n) :
    ∃ steps ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a], F⟩).length + 1,
      BitRegister.run program steps ⟨.running 0, SourceLinePullback.start F a⟩ = ⟨.accepted, result F a⟩ :=
  program_original_bound F a

run_cmd do
  for name in [
    ``pullback_state,
    ``clearPositions_exec,
    ``clearEnds_exec,
    ``load_exec,
    ``prepare_exec,
    ``ready_state,
    ``source_prepare_exec,
    ``saved_get,
    ``search_exec,
    ``parameter_exec,
    ``observed_store,
    ``parameter_exact,
    ``retained_left_map,
    ``retained_right_map,
    ``retained_left_width,
    ``retained_right_width,
    ``parameter_original_bound,
    ``parameter_program_run,
    ``SourceWitnessLift.loadLeft_exec,
    ``SourceWitnessLift.clearFirst_exec,
    ``SourceWitnessLift.clearSecond_exec,
    ``SourceWitnessLift.clearWork_exec,
    ``SourceWitnessLift.prepareLeft_exec,
    ``SourceWitnessLift.prepareRight_exec,
    ``SourceWitnessLift.saved_other,
    ``SourceWitnessLift.block_exec,
    ``SourceWitnessLift.result_left,
    ``SourceWitnessLift.result_right,
    ``SourceWitnessLift.result_present,
    ``parameter_some_state,
    ``parameter_none_flag,
    ``parameter_some_flag,
    ``lift_exec,
    ``finish_exec,
    ``block_exec,
    ``lifted_observed,
    ``selection_query,
    ``result_exact,
    ``program_run,
    ``liftCostPolynomial_eval,
    ``lift_original_bound,
    ``finish_original_bound,
    ``original_input_bound,
    ``output_lengths,
    ``output_original_bounds,
    ``program_original_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceLineWitness.parameter_exec
#print axioms PNP.Concrete.ResidualReduction.SourceWitnessLift.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineWitness.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceLineWitness.result_exact
#print axioms PNP.Concrete.ResidualReduction.SourceLineWitness.original_input_bound
#print axioms PNP.Concrete.ResidualReduction.SourceLineWitness.program_original_bound

end PNP.Concrete.ResidualReduction.SourceLineWitness.Regression
