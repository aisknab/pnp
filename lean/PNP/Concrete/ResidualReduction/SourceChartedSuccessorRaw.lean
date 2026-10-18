import PNP.Concrete.ResidualReduction.SourceChartedSuccessorFinish

/-! Canonical input-only charted successor. The source family drives scalar
construction, the scalar drives the tail candidate, both exact gates are
mandatory, and only then is the family reduced. Selection and chart construction,
malformed-input rejection and physical complete-history costs remain separate. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorRaw
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorState
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorInput (packet)
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorFinish (finished)

def block : Block 29 := .seq SourceChartedSuccessorInput.headers <|
  .seq SourceChartedSuccessorNormals.block <| .seq SourceChartedSuccessorScalar.block <|
  .seq SourceChartedSuccessorTail.block <| .seq SourceChartedSuccessorGate.block
    SourceChartedSuccessorFinish.block
def fuel {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) : Nat :=
  SourceChartedSuccessorInput.headersFuel n k.val + (SourceChartedSuccessorNormals.fuel n normals.isSome +
    (SourceChartedSuccessorScalar.fuel F + (SourceChartedSuccessorTail.fuel k normals +
      (SourceChartedSuccessorGate.fuel F k normals + SourceChartedSuccessorFinish.fuel F k normals))))

theorem block_exec {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    Exec block (SourceChartedSuccessorState.initial (packet F k normals)) (fuel F k normals)
      (finished F k normals) := by
  have headers := SourceChartedSuccessorInput.headers_exec n k.val
    ((normalsCodec n).encode normals ++ (SourceEncoding.familyCodec (n + 1)).encode F)
  have normalsRun := SourceChartedSuccessorNormals.block_exec normals
    ((SourceEncoding.familyCodec (n + 1)).encode F) (SourceChartedSuccessorInput.dimensions n k.val)
  have scalarRun := SourceChartedSuccessorScalar.block_exec F k normals
  have tail := SourceChartedSuccessorTail.block_exec F k normals
  have gates := SourceChartedSuccessorGate.block_exec F k normals
  have finish := SourceChartedSuccessorFinish.block_exec F k normals
  simpa only [block,fuel,packet,SourceChartedSuccessorInput.dimensions,SourceChartedSuccessorScalar.before] using
    Exec.seq headers (Exec.seq normalsRun (Exec.seq scalarRun (Exec.seq tail (Exec.seq gates finish))))

theorem program_run {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    BitRegister.run (block.program 0 8) (fuel F k normals + 1)
      ⟨.running 0,SourceChartedSuccessorState.initial (packet F k normals)⟩ =
      ⟨.accepted,finished F k normals⟩ := (block_exec F k normals).program_run 0 8

theorem program_output {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (BitRegister.run (block.program 0 8) (fuel F k normals + 1)
      ⟨.running 0,SourceChartedSuccessorState.initial (packet F k normals)⟩).store.get 8 =
      (SourceFamilyReductionEncoding.codec n).encode (result F k normals) := by
  rw [program_run]
  exact SourceChartedSuccessorFinish.output_eq F k normals

theorem output_decode {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1))
    (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    (SourceFamilyReductionEncoding.codec n).decode
      ((BitRegister.run (block.program 0 8) (fuel F k normals + 1)
        ⟨.running 0,SourceChartedSuccessorState.initial (packet F k normals)⟩).store.get 8) =
      some (result F k normals) := by
  rw [program_run]
  exact SourceChartedSuccessorFinish.output_decode F k normals

theorem charted_contract {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (c : Fin (n + 1) × Point n) (normals : Option (Affine (n + 1) × Affine (n + 1))) :
    let charted := chartRows (SourceBalance.markSource F w) c.1 c.2
    (BitRegister.run (block.program 0 8) (fuel charted c.1 normals + 1)
      ⟨.running 0,SourceChartedSuccessorState.initial (packet charted c.1 normals)⟩).store.get 8 =
      (SourceFamilyReductionEncoding.codec n).encode
        (contract (SourceBalance.markSource F w) c.1 c.2 (SourceClosure.computedTail F w c normals)) := by
  dsimp only
  rw [program_output,result_chart]

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorRaw
