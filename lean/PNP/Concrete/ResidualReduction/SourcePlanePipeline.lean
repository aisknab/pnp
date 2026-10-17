import PNP.Concrete.ResidualReduction.SourcePlanePipelineSearch

/-! One literal prepared plane-query program: derive the direction space and
activity matrix, construct and solve the plane equations, and search the actual
computed map. Both no-result paths and all unsuccessful trials are charged.
The bound counts bit-register instructions in the original encoded input size.
Raw parsing, lifting a direction back to the original coordinates, literal tape
compilation and the whole contraction loop remain separate obligations. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePipeline
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def search : Block 29 := .seq prepareSearch (Frame.block 7 SourceBilinearSearch.block)
theorem search_exec {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length)
    (computed : solve F.length (planeRows F a b) = some s) :
    ∃ used after, Exec search (planeDone F a b) used (searchStore after (derivedData F a b)) ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
        (planeRawQuery F a b) ∧
      used ≤ 15 + SourceBilinearSearch.costPolynomial.eval
        (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length := by
  obtain ⟨used, after, checked, bytes, bound⟩ := SourcePlanePreparedSearch.original_input_bound F a b s computed
  exact ⟨15 + used, after, Exec.seq (prepareSearch_exec F a b s computed)
    (Frame.execution checked (derivedData F a b).store), bytes, Nat.add_le_add_left bound 15⟩

theorem searchStore_output (after : Store 22) (data : Saved) :
    (searchStore after data).get 8 = after.get 8 :=
  Frame.get_core after data.store 8

def select : Block 29 := .branch 8 .skip .skip search
/-- Failure of the plane weight system is failure of this route only. -/
theorem select_exec {n : Nat} (F : Family n) (a b : Affine n) :
    ∃ used after, Exec select (planeDone F a b) used (searchStore after (derivedData F a b)) ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
        (planeRawQuery F a b) ∧
      used ≤ 16 + SourceBilinearSearch.costPolynomial.eval
        (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length := by
  cases computed : solve F.length (planeRows F a b) with
  | none =>
    have output : (planeDone F a b).get 8 = [false] := by
      rw [plane_output, computed]
      rfl
    let after := (searchView (SourcePlaneSolver.result F a b)).store
    have same : searchStore after (derivedData F a b) = planeDone F a b :=
      searchView_store (SourcePlaneSolver.result F a b) (derivedData F a b)
    refine ⟨2, after, ?_, ?_, ?_⟩
    · rw [same]
      exact Exec.zero (source := (8 : Fin 29)) output (.skip _)
    · rw [← searchStore_output after (derivedData F a b), same, output,
        planeRawQuery, computed]
      rfl
    · omega
  | some s =>
    obtain ⟨used, after, checked, bytes, bound⟩ := search_exec F a b s computed
    have output : (planeDone F a b).get 8 = true ::
        (List.replicate s.parameters true ++ false :: mapBits s.forms) := by
      rw [plane_output, computed]
      exact MatrixSolutionSerialization.solution_some_bits s
    exact ⟨1 + used, after, Exec.one (source := (8 : Fin 29)) output checked, bytes, by omega⟩

def block : Block 29 := .seq construct select
def costPolynomial : NatPolynomial :=
  .add (.add SourceActivityConstruction.costPolynomial SourcePlaneSolver.costPolynomial)
    (.add (.constant 33) SourceBilinearSearch.costPolynomial)

/-- All solution data and the activity matrix are computed from the source.
No correctness, successful-search, supplied-map or coverage premise is required. -/
theorem block_exec {n : Nat} (F : Family n) (a b : Affine n) :
    ∃ used after, Exec block (start F a b) used (searchStore after (derivedData F a b)) ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
        (planeRawQuery F a b) ∧
      used ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length := by
  obtain ⟨used, after, checked, bytes, bound⟩ := select_exec F a b
  refine ⟨constructFuel F a b + used, after, Exec.seq (construct_exec F a b) checked, bytes, ?_⟩
  have activity := SourceActivityConstruction.original_input_bound F [a, b]
  have plane := SourcePlaneSolver.original_input_bound F a b
  simp only [costPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold constructFuel
  omega

def program : Program 29 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (a b : Affine n) :
    ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, start F a b⟩ =
        ⟨.accepted, searchStore after (derivedData F a b)⟩ ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
        (planeRawQuery F a b) ∧
      used ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length := by
  obtain ⟨used, after, checked, bytes, bound⟩ := block_exec F a b
  exact ⟨used, after, checked.program_run 0 8, bytes, bound⟩

theorem retained_data (after : Store 22) (data : Saved) (index : Fin 7) :
    (searchStore after data).get (Frame.frameIndex 22 index) = data.store.get index :=
  Frame.get_frame after data.store index
theorem retained_direction {n : Nat} (F : Family n) (a b : Affine n) (after : Store 22) :
    (searchStore after (derivedData F a b)).get 25 = mapBits (directionSpace F [a, b]).forms :=
  retained_data after (derivedData F a b) 3
theorem retained_direction_width {n : Nat} (F : Family n) (a b : Affine n) (after : Store 22) :
    (searchStore after (derivedData F a b)).get 26 = List.replicate (directionSpace F [a, b]).parameters true :=
  retained_data after (derivedData F a b) 4
theorem retained_dimension {n : Nat} (F : Family n) (a b : Affine n) (after : Store 22) :
    (searchStore after (derivedData F a b)).get 28 = List.replicate n true :=
  retained_data after (derivedData F a b) 6
theorem retained_source {n : Nat} (F : Family n) (a b : Affine n) (after : Store 22) :
    (searchStore after (derivedData F a b)).get 22 = SourceMatrixEncoding.familyBits F :=
  retained_data after (derivedData F a b) 0
theorem output_bound {n : Nat} (F : Family n) (a b : Affine n) :
    ((SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
      (planeRawQuery F a b)).length ≤ 2 * (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length + 1 :=
  SourcePlanePreparedSearch.original_output_bound F a b

end PNP.Concrete.ResidualReduction.SourcePlanePipeline
