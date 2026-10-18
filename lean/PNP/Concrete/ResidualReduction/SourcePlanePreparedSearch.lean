import PNP.Concrete.ResidualReduction.SourceBilinearSearch
import PNP.Concrete.ResidualReduction.SourcePlaneSolver
import PNP.Concrete.ResidualReduction.SourceActivityConstruction
import PNP.Concrete.ResidualReduction.SourceAffineInputBridge

/-! Exact prepared search for the existing source-plane query. Its matrix and
map agree byte-for-byte with the already verified source-derived constructors.
The bound is in the original source packet length. Physical register handoff,
the inconsistent solver branch and final direction lifting remain distinct
integration obligations; this file does not claim a complete raw plane query. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def start {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length) : SourceAffineSearch.State :=
  SourceBilinearSearch.start (activityMatrix (directionSpace F [a, b]) F) s

theorem matrix_from_source {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length) :
    (start F a b s).store.get 0 = (SourceActivityConstruction.result F [a, b]).store.get 8 := by
  rw [SourceActivityConstruction.result_output]
  rfl

theorem map_from_solver {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length)
    (computed : solve F.length (SourcePlane.planeRows F a b) = some s) :
    (start F a b s).store.get 16 = (SourcePlaneSolver.result F a b).store.get 0 := by
  rw [start, SourceBilinearSearch.start_map]
  change mapBits s.forms = (MatrixSolutionInstructions.result F.length (SourcePlane.planeRows F a b)).store.get 0
  rw [SourceAffineInput.result_some F.length (SourcePlane.planeRows F a b) s computed]
  rfl

theorem width_from_solver {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length)
    (computed : solve F.length (SourcePlane.planeRows F a b) = some s) :
    (start F a b s).store.get 17 = ((SourcePlaneSolver.result F a b).store.get 1).tail := by
  rw [start, SourceBilinearSearch.start_parameters]
  change List.replicate s.parameters true =
    ((MatrixSolutionInstructions.result F.length (SourcePlane.planeRows F a b)).store.get 1).tail
  rw [SourceAffineInput.result_some F.length (SourcePlane.planeRows F a b) s computed]
  rfl

theorem columns_from_direction {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length) :
    (start F a b s).store.get 1 = ((SourceActivityConstruction.result F [a, b]).store.get 1).tail := rfl

theorem original_input_bound {n : Nat} (F : Family n) (a b : Affine n) (s : Space F.length)
    (computed : solve F.length (SourcePlane.planeRows F a b) = some s) :
    ∃ used after, Exec SourceBilinearSearch.block (start F a b s).store used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
        (planeRawQuery F a b) ∧
      used ≤ SourceBilinearSearch.costPolynomial.eval
        (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length := by
  let L := (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F [a, b]
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [a, b]
  have hd : (directionSpace F [a, b]).parameters ≤ L :=
    Nat.le_trans (kernelSpace_parameter_bound (directionSystem F [a, b])) hn
  have hk : s.parameters ≤ L :=
    Nat.le_trans (solve_some_parameter_bound (SourcePlane.planeRows F a b) s computed) hm
  obtain ⟨used, after, checked, bytes, bound⟩ := SourceBilinearSearch.bounded_exec
    (activityMatrix (directionSpace F [a, b]) F) s L hm hd hk
  refine ⟨used, after, checked, ?_, bound⟩
  simpa only [planeRawQuery, computed, planeSpaceQuery_eq] using bytes

theorem original_output_bound {n : Nat} (F : Family n) (a b : Affine n) :
    ((SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode
      (planeRawQuery F a b)).length ≤
      2 * (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length + 1 := by
  let L := (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F [a, b]
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [a, b]
  have hd : (directionSpace F [a, b]).parameters ≤ L :=
    Nat.le_trans (kernelSpace_parameter_bound (directionSystem F [a, b])) hn
  have bound := SourceAffineOutput.witness_bytes_bound F.length (directionSpace F [a, b]).parameters
    (planeRawQuery F a b)
  omega

end PNP.Concrete.ResidualReduction.SourcePlanePreparedSearch
