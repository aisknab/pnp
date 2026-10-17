import PNP.Concrete.ResidualReduction.SourceLineWitnessState

/-! Exact original-source construction through parameter-witness recovery.
The original family and normal determine every map, matrix, seed and vector.
Lifting the two vectors and raw-machine runtime are downstream boundaries. -/

namespace PNP.Concrete.ResidualReduction.SourceLineWitness
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

def search : Block 38 := Frame.block 19 SourceMatrixWitness.block
def searchFuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  SourceMatrixWitness.fuel (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha)
def parameterResult {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  store (SourceMatrixWitness.result (fromPullback F alpha).core
    (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha))
    (SourceLinePullback.resultData F alpha)
theorem search_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec search (searchStart F alpha) (searchFuel F alpha) (parameterResult F alpha) :=
  Frame.execution (SourceMatrixWitness.block_exec (fromPullback F alpha).core
    (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha))
    (frame (SourceLinePullback.resultData F alpha))

def parameterBlock : Block 38 := .seq SourceLinePullback.block (.seq prepare search)
def parameterFuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  SourceLinePullback.fuel F alpha + (10 + searchFuel F alpha)
theorem parameter_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec parameterBlock (SourceLinePullback.start F alpha) (parameterFuel F alpha) (parameterResult F alpha) :=
  Exec.seq (SourceLinePullback.block_exec F alpha) (Exec.seq (source_prepare_exec F alpha) (search_exec F alpha))

def observedParameters (s : Store 38) : Option (BitString × BitString) :=
  if (s.get 4).isEmpty then none else some (s.get 17, s.get 8)
theorem observed_store (core : Store 19) (data : SourceLinePullback.Saved) :
    observedParameters (store core data) = SourceMatrixWitness.observed core := by
  have flag := Frame.get_core core (frame data) (4 : Fin 19)
  have left := Frame.get_core core (frame data) (17 : Fin 19)
  have right := Frame.get_core core (frame data) (8 : Fin 19)
  change (store core data).get 4 = core.get 4 at flag
  change (store core data).get 17 = core.get 17 at left
  change (store core data).get 8 = core.get 8 at right
  simp only [observedParameters, SourceMatrixWitness.observed, flag, left, right]
theorem parameter_exact {n : Nat} (F : Family n) (alpha : Affine n) :
    observedParameters (parameterResult F alpha) =
      (BilinearSelection.select (SourceLinePullback.normalPull F alpha)
        (SourceLinePullback.activityPull F alpha)).witness.map (fun w =>
          ((SourceEncoding.pointCodec (SourceLinePullback.leftSpace F alpha).parameters).encode (sumUnits w.1),
            (SourceEncoding.pointCodec (SourceLinePullback.rightSpace F alpha).parameters).encode (sumUnits w.2))) := by
  rw [parameterResult, observed_store]
  exact SourceMatrixWitness.result_exact _ _ _

theorem retained_left_map {n : Nat} (F : Family n) (alpha : Affine n) :
    (parameterResult F alpha).get 32 = mapBits (SourceLinePullback.leftSpace F alpha).forms :=
  saved_get _ _ 8
theorem retained_right_map {n : Nat} (F : Family n) (alpha : Affine n) :
    (parameterResult F alpha).get 34 = mapBits (SourceLinePullback.rightSpace F alpha).forms :=
  saved_get _ _ 10
theorem retained_left_width {n : Nat} (F : Family n) (alpha : Affine n) :
    (parameterResult F alpha).get 33 = List.replicate (SourceLinePullback.leftSpace F alpha).parameters true :=
  saved_get _ _ 9
theorem retained_right_width {n : Nat} (F : Family n) (alpha : Affine n) :
    (parameterResult F alpha).get 35 = List.replicate (SourceLinePullback.rightSpace F alpha).parameters true :=
  saved_get _ _ 11

def parameterCostPolynomial : NatPolynomial :=
  .add SourceLinePullback.costPolynomial (.add (.constant 10) SourceMatrixWitness.sourceCostPolynomial)
theorem parameter_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    parameterFuel F alpha ≤ parameterCostPolynomial.eval
      (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length := by
  have preparation := SourceLinePullback.original_input_bound F alpha
  have selection := SourceMatrixWitness.source_bound F alpha
  change SourceLinePullback.fuel F alpha + (10 + searchFuel F alpha) ≤
    SourceLinePullback.costPolynomial.eval _ + (10 + SourceMatrixWitness.sourceCostPolynomial.eval _)
  unfold searchFuel
  omega
def parameterProgram : Program 38 := parameterBlock.program 0 8
theorem parameter_program_run {n : Nat} (F : Family n) (alpha : Affine n) :
    BitRegister.run parameterProgram (parameterFuel F alpha + 1)
      ⟨.running 0, SourceLinePullback.start F alpha⟩ = ⟨.accepted, parameterResult F alpha⟩ :=
  (parameter_exec F alpha).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceLineWitness
