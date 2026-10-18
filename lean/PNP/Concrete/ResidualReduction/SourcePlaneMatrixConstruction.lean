import PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation

/-! Complete prepared construction of the exact plane-query matrix. The
original family and two normal words are the only source data. The program
materializes the extra row, runs the existing all-coordinate constructor,
then removes precisely the proved padding. Raw parsing and the subsequent
solver/search remain separate caller obligations. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMatrixConstruction
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourcePlaneMatrix
open PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation

def payload {n : Nat} (F : Family n) (alpha beta : Affine n) : State :=
  ⟨⟨SourceMatrixConstruction.ready (augmented F alpha beta) n 0 0 0
    (matrixBits (SourceClosure.affineMaskRows (augmented F alpha beta))), List.replicate F.length true⟩,
    matrixBits [alpha, beta]⟩
theorem payload_exec {n : Nat} (F : Family n) (alpha beta : Affine n) :
    Exec (lift15 SourceMatrixConstruction.payload) (augmentedInput F alpha beta).store
      (SourceMatrixConstruction.payloadFuel n (F.length + 1)) (payload F alpha beta).store := by
  simpa only [augmented_length, payload, augmentedInput] using
    lift15_exec SourceMatrixConstruction.payload (augmentedInput F alpha beta) _ (payload F alpha beta).core.core
      (SourceMatrixConstruction.payload_exec (augmented F alpha beta))

def projectionReady {n : Nat} (F : Family n) (alpha beta : Affine n) : State :=
  setRegisters (payload F alpha beta)
    {registers (payload F alpha beta) with input := paddedRows (SourcePlane.planeRows F alpha beta), target := List.replicate (F.length + 1) true, remaining := [], excess := [], output := []}
def result {n : Nat} (F : Family n) (alpha beta : Affine n) : State :=
  setRegisters (payload F alpha beta)
    {registers (payload F alpha beta) with input := [], target := List.replicate (F.length + 1) true, remaining := [], excess := [], output := matrixBits (SourcePlane.planeRows F alpha beta)}
def prepareProjection : Block 17 := .seq (.action (.copy 0 8)) <| .seq (.action (.clear 8)) <|
  .seq (.action (.copy 1 15)) (.action (.push 1 true))
theorem prepareProjection_exec {n : Nat} (F : Family n) (alpha beta : Affine n) :
    Exec prepareProjection (payload F alpha beta).store 4 (projectionReady F alpha beta).store := by
  simp only [payload, projectionReady, augmented_matrix]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
theorem projection_exec {n : Nat} (F : Family n) (alpha beta : Affine n) :
    Exec (lift9 SourcePlaneMatrixProjection.block) (projectionReady F alpha beta).store
      (SourcePlaneMatrixProjection.fuel F.length (SourcePlane.planeRows F alpha beta)) (result F alpha beta).store :=
  lift9_exec _ (projectionReady F alpha beta) _ (registers (result F alpha beta))
    (SourcePlaneMatrixProjection.block_exec (registers (payload F alpha beta)) F.length (SourcePlane.planeRows F alpha beta))

def block : Block 17 := .seq SourcePlaneMatrixAugmentation.block <|
  .seq (lift15 SourceMatrixConstruction.payload) <| .seq prepareProjection (lift9 SourcePlaneMatrixProjection.block)
def fuel {n : Nat} (F : Family n) (alpha beta : Affine n) : Nat :=
  SourcePlaneMatrixAugmentation.fuel F + (SourceMatrixConstruction.payloadFuel n (F.length + 1) +
    (4 + SourcePlaneMatrixProjection.fuel F.length (SourcePlane.planeRows F alpha beta)))
theorem block_exec {n : Nat} (F : Family n) (alpha beta : Affine n) :
    Exec block (start F alpha beta).store (fuel F alpha beta) (result F alpha beta).store :=
  Exec.seq (SourcePlaneMatrixAugmentation.block_exec F alpha beta)
    (Exec.seq (payload_exec F alpha beta) (Exec.seq (prepareProjection_exec F alpha beta) (projection_exec F alpha beta)))
theorem result_output {n : Nat} (F : Family n) (alpha beta : Affine n) :
    (result F alpha beta).store.get 8 = matrixBits (SourcePlane.planeRows F alpha beta) := rfl
theorem retained_normals {n : Nat} (F : Family n) (alpha beta : Affine n) :
    (result F alpha beta).store.get 16 = matrixBits [alpha, beta] := rfl
theorem retained_source_count {n : Nat} (F : Family n) (alpha beta : Affine n) :
    (result F alpha beta).store.get 15 = List.replicate F.length true := rfl
theorem output_length {n : Nat} (F : Family n) (alpha beta : Affine n) :
    ((result F alpha beta).store.get 8).length = (F.length + 1) * (n * n) := by
  rw [result_output, matrixBits_length, SourcePlane.planeRows_length]
def program : Program 17 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (alpha beta : Affine n) :
    BitRegister.run program (fuel F alpha beta + 1) ⟨.running 0, (start F alpha beta).store⟩ =
      ⟨.accepted, (result F alpha beta).store⟩ := (block_exec F alpha beta).program_run 0 8

end PNP.Concrete.ResidualReduction.SourcePlaneMatrixConstruction
