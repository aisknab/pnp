import Lean
import PNP.Concrete.ResidualReduction.SourcePlanePipeline
import PNP.Concrete.ResidualReduction.SourceBilinearSearchRegression

namespace PNP.Concrete.ResidualReduction.SourcePlanePipeline.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

private def linear : Row 1 := ⟨false, (true, false), (false, true)⟩
private def inactive : Row 1 := ⟨false, (false, false), (false, true)⟩
private def zeroNormal : Affine 1 := (false, false)
private def restricted : Affine 1 := (true, false)
private def freeWeight : Space 1 := ⟨1, ((true, false), ())⟩
private def alpha : Affine 2 := (true, (false, true))
private def beta : Affine 2 := (false, (true, true))

example : (start [linear] zeroNormal zeroNormal).get 24 = [] := rfl
example : (start [linear] zeroNormal zeroNormal).get 25 = [] := rfl
example : (captured [linear] zeroNormal zeroNormal).get 24 = [true] := rfl
example : (captured [linear] zeroNormal zeroNormal).get 25 = [true, false] := rfl
example : (captured [linear] zeroNormal zeroNormal).get 26 = [true] := rfl
example : (planeStart [linear] zeroNormal zeroNormal).get 16 = [false, false, false, false] := rfl
example : solve 1 (planeRows [linear] zeroNormal zeroNormal) = some freeWeight := rfl
example : (searchView (planeSolution [linear] zeroNormal zeroNormal freeWeight)).store.get 0 = [true, false] := rfl
-- The constructor leaves its source at register 12; the search must clear it.
example : ((searchView (planeSolution [linear] zeroNormal zeroNormal freeWeight)).store.get 12).isEmpty = false := rfl
example : (preparedSearch (searchView (planeSolution [linear] zeroNormal zeroNormal freeWeight))
    (derivedData [linear] zeroNormal zeroNormal)).store.get 12 = [] := rfl
example : (preparedSearch (searchView (planeSolution [linear] zeroNormal zeroNormal freeWeight))
    (derivedData [linear] zeroNormal zeroNormal)).store.get 13 = [] := rfl
example : (preparedSearch (searchView (planeSolution [linear] zeroNormal zeroNormal freeWeight))
    (derivedData [linear] zeroNormal zeroNormal)).store.get 16 = [true, false] := rfl
example : (preparedSearch (searchView (planeSolution [linear] zeroNormal zeroNormal freeWeight))
    (derivedData [linear] zeroNormal zeroNormal)).store.get 17 = [true] := rfl

example : planeRawQuery [linear] zeroNormal zeroNormal = some ((true, ()), (true, ())) := rfl
-- The first row's unit weight is unsuccessful; the later row must still be tried.
example : planeRawQuery [inactive, linear] zeroNormal zeroNormal =
    some ((false, (true, ())), (true, ())) := rfl
example : (solve 1 (planeRows [inactive] zeroNormal zeroNormal)).isSome = true := rfl
example : planeRawQuery [inactive] zeroNormal zeroNormal = none := rfl
example : (directionSpace [linear] [restricted, restricted]).parameters = 0 := rfl
example : planeRawQuery [linear] restricted restricted = none := rfl
example : solve 0 (planeRows ([] : Family 2) alpha beta) = none := rfl
example : planeRawQuery ([] : Family 2) alpha beta = none := rfl
example : planeRawQuery ([] : Family 0) true false = none := rfl
example : planeRawQuery (n := 0) [⟨false, true, false⟩] true false = none := rfl

private def ProgramProduces {n : Nat} (F : Family n) (a b : Affine n) (word : BitString) : Prop :=
  ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, start F a b⟩ =
      ⟨.accepted, searchStore after (derivedData F a b)⟩ ∧
    (searchStore after (derivedData F a b)).get 8 = word ∧
    used ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length
private theorem program_produces {n : Nat} (F : Family n) (a b : Affine n) (word : BitString)
    (expected : (SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
      (planeRawQuery F a b) = word) : ProgramProduces F a b word := by
  obtain ⟨used, after, checked, bytes, bound⟩ := program_run F a b
  exact ⟨used, after, checked, (searchStore_output after (derivedData F a b)).trans (bytes.trans expected), bound⟩

example : ProgramProduces [linear] zeroNormal zeroNormal [true, true, true] :=
  program_produces [linear] zeroNormal zeroNormal _ rfl
example : ProgramProduces [inactive, linear] zeroNormal zeroNormal [true, false, true, true] :=
  program_produces [inactive, linear] zeroNormal zeroNormal _ rfl
example : ProgramProduces [inactive] zeroNormal zeroNormal [false] :=
  program_produces [inactive] zeroNormal zeroNormal _ rfl
example : ProgramProduces [linear] restricted restricted [false] :=
  program_produces [linear] restricted restricted _ rfl
example : ProgramProduces ([] : Family 2) alpha beta [false] :=
  program_produces ([] : Family 2) alpha beta _ rfl
example : ProgramProduces ([] : Family 0) true false [false] :=
  program_produces ([] : Family 0) true false _ rfl
example : ProgramProduces (n := 0) [⟨false, true, false⟩] true false [false] :=
  program_produces (n := 0) [⟨false, true, false⟩] true false _ rfl

example {n : Nat} (F : Family n) (a b : Affine n) :
    ∃ used after, Exec block (start F a b) used (searchStore after (derivedData F a b)) ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
        (planeRawQuery F a b) ∧
      used ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length :=
  block_exec F a b
example {n : Nat} (F : Family n) (a b : Affine n) (after : Store 22) :
    (searchStore after (derivedData F a b)).get 25 = mapBits (directionSpace F [a, b]).forms :=
  retained_direction F a b after
example {n : Nat} (F : Family n) (a b : Affine n) (after : Store 22) :
    (searchStore after (derivedData F a b)).get 28 = List.replicate n true := retained_dimension F a b after
example {n : Nat} (F : Family n) (a b : Affine n) :
    ((SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
      (planeRawQuery F a b)).length ≤ 2 * (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length + 1 :=
  output_bound F a b

run_cmd do
  for name in [``transfers_exec, ``save_exec, ``activity_exec, ``capture_exec,
    ``initial_no_matrix, ``initial_no_direction_map, ``captured_matrix,
    ``captured_direction_map, ``captured_direction_width, ``preparePlane_exec,
    ``plane_exec, ``construct_exec, ``plane_output, ``plane_retains_matrix,
    ``plane_retains_direction, ``searchView_store, ``transferSearchMap_exec,
    ``transferSearchMatrix_exec, ``cleanSearch_exec, ``transferSearchWidth_exec,
    ``transferSearchFrame_exec, ``transferSearchCount_exec, ``prepareSearch_words,
    ``bilinear_start_words, ``planeSolution_store, ``preparedSearch_eq, ``prepareSearch_exec,
    ``search_exec, ``searchStore_output, ``select_exec, ``block_exec, ``program_run,
    ``retained_data, ``retained_direction, ``retained_direction_width, ``retained_dimension,
    ``retained_source, ``output_bound] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourcePlanePipeline.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourcePlanePipeline.program_run

end PNP.Concrete.ResidualReduction.SourcePlanePipeline.Regression
