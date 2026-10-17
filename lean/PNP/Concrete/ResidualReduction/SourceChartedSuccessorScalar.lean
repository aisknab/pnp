import PNP.Concrete.ResidualReduction.SourceChartedSuccessorNormals

/-! Derive the scalar from the retained actual family. The canonical family
header is consumed, its payload becomes the scalar program's input, and the
complete computed coefficient word is copied out before workspace reuse. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorScalar
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorState

def before {n : Nat} (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Saved :=
  ⟨List.replicate n true,List.replicate k.val true,(normalsCodec n).encode normals,[],[],[]⟩
def computed {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Saved :=
  {data F k normals with quadratic := SourceQuadraticEncoding.word (scalar F)}

def prepareScalar : Block 29 := .seq (.action (.clear 4)) <|
  .seq (.action (.copy 1 23)) (.action (.push 1 true))
def load : Block 29 := .seq (.action (.copy 26 0)) <|
  .seq (core MatrixStrictHeader.block) prepareScalar
def loadFuel (rows : Nat) : Nat := 4 * rows + 13

theorem load_exec {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec load (work ((SourceEncoding.familyCodec (n + 1)).encode F) [] (before k normals))
      (loadFuel F.length)
      (state16 (SourceScalarState.initial (n + 1) (familyBits F)) (data F k normals)) := by
  let saved := data F k normals
  let ready := SourceScalarState.work ((SourceEncoding.familyCodec (n + 1)).encode F)
  let counted := {SourceScalarState.work (familyBits F) with target := List.replicate F.length true,sign := [true]}
  have retain : Exec (.action (.copy (26 : Fin 29) 0))
      (work ((SourceEncoding.familyCodec (n + 1)).encode F) [] (before k normals)) 1
      (withCore ready saved) := .action _ _
  have scan : Exec MatrixStrictHeader.block ready.store (4 * F.length + 9) counted.store := by
    simpa only [SourceCoefficientGateRaw.header_fuel,MatrixStrictHeader.result,
      MatrixStrictHeader.scan_canonical,if_true,ready,counted,SourceScalarState.work,
      SourceFamilyReductionEncoding.family_bytes,List.append_nil] using
      MatrixStrictHeader.block_exec (natural F.length ++ familyBits F)
        (SourceScalarState.work (natural F.length ++ familyBits F))
  have prepare : Exec prepareScalar (withCore counted saved) 3
      (state16 (SourceScalarState.initial (n + 1) (familyBits F)) saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : loadFuel F.length = 1 + ((4 * F.length + 9) + 3) := by unfold loadFuel; omega
  simpa only [load,cost,saved] using Exec.seq retain (Exec.seq (core_exec scan saved) prepare)

def save : Block 29 := .seq (.action (.copy 27 8)) reset

theorem save_exec {n : Nat} (q : Quadratic n) (s : Saved) :
    Exec save (state16 (SourceScalarFamily.finished q) s) 25
      (work [] [] {s with quadratic := SourceQuadraticEncoding.word q}) := by
  let saved := {s with quadratic := SourceQuadraticEncoding.word q}
  have copy : Exec (.action (.copy (27 : Fin 29) 8))
      (state16 (SourceScalarFamily.finished q) s) 1
      (state16 (SourceScalarFamily.finished q) saved) := .action _ _
  have clear := reset_exec (Frame.join (SourceScalarFamily.finished q) (Store.empty 7)) saved
  exact Exec.seq copy clear

def block : Block 29 := .seq load <| .seq (use16 SourceScalarFamily.block) save
def fuel {n : Nat} (F : Family (n + 1)) : Nat :=
  loadFuel F.length + (SourceScalarFamily.fuel F + 25)

theorem block_exec {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec block (work ((SourceEncoding.familyCodec (n + 1)).encode F) [] (before k normals))
      (fuel F) (work [] [] (computed F k normals)) := by
  have prepare := load_exec F k normals
  have scalarRun := use16_exec (SourceScalarFamily.block_exec F) (data F k normals)
  have retain := save_exec (scalar F) (data F k normals)
  exact Exec.seq prepare (Exec.seq scalarRun retain)

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorScalar
