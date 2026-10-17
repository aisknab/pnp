import PNP.Concrete.ResidualReduction.SourcePlaneLiftInstructions

/-! Complete prepared execution of the existing sourcePlaneQuery, including
the original-coordinate witness lift. All maps, matrices and candidates are
derived from the source. This is an original-input polynomial bit-register
instruction bound; raw parsing and the concrete tape interface remain separate. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePreparedQuery
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourcePlanePipeline (derivedData searchStore start)

theorem lift_exec {n : Nat} (F : Family n) (a b : Affine n) (after : Store 22)
    (output : after.get 8 =
      (SourceAffineOutput.witnessCodec F.length (directionSpace F [a, b]).parameters).encode (planeRawQuery F a b)) :
    ∃ used result, Exec SourcePlaneLift.block (searchStore after (derivedData F a b)) used
        (SourcePlaneLift.store result (SourcePlaneLift.view after).2 (derivedData F a b)) ∧
      result.output = (SourceAffineOutput.witnessCodec F.length n).encode (sourcePlaneQuery F a b) ∧
      used ≤ SourcePlaneLift.costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length := by
  obtain ⟨used, result, checked, bytes, bound⟩ := SourcePlaneLift.block_exec
    (SourcePlaneLift.view after).1 (SourcePlaneLift.view after).2 (derivedData F a b)
    (directionSpace F [a, b]).forms (planeRawQuery F a b)
    ((SourcePlaneLift.view_output after).trans output) rfl rfl rfl
  rw [SourcePlaneLift.view_store] at checked
  let L := (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F [a, b]
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [a, b]
  have hk : (directionSpace F [a, b]).parameters ≤ L :=
    Nat.le_trans (kernelSpace_parameter_bound (directionSystem F [a, b])) hn
  refine ⟨used, result, checked, bytes, ?_⟩
  exact Nat.le_trans bound (SourcePlaneLift.bounded_cost F.length n (directionSpace F [a, b]).parameters L hm hn hk)

def block : Block 29 := .seq SourcePlanePipeline.block SourcePlaneLift.block
def costPolynomial : NatPolynomial := .add SourcePlanePipeline.costPolynomial SourcePlaneLift.costPolynomial

/-- No computed-map, successful-candidate or completeness certificate is an input. -/
theorem block_exec {n : Nat} (F : Family n) (a b : Affine n) :
    ∃ used after, Exec block (start F a b) used after ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length n).encode (sourcePlaneQuery F a b) ∧
      used ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length := by
  obtain ⟨searched, searchAfter, searchRun, searchBytes, searchBound⟩ := SourcePlanePipeline.block_exec F a b
  obtain ⟨lifted, result, liftRun, resultBytes, liftBound⟩ := lift_exec F a b searchAfter searchBytes
  exact ⟨searched + lifted, SourcePlaneLift.store result (SourcePlaneLift.view searchAfter).2 (derivedData F a b),
    Exec.seq searchRun liftRun,
    (SourcePlaneLift.store_output result (SourcePlaneLift.view searchAfter).2 (derivedData F a b)).trans resultBytes,
    Nat.add_le_add searchBound liftBound⟩

def program : Program 29 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (a b : Affine n) :
    ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, start F a b⟩ = ⟨.accepted, after⟩ ∧
      after.get 8 = (SourceAffineOutput.witnessCodec F.length n).encode (sourcePlaneQuery F a b) ∧
      used ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length := by
  obtain ⟨used, after, checked, bytes, bound⟩ := block_exec F a b
  exact ⟨used, after, checked.program_run 0 8, bytes, bound⟩

theorem output_bound {n : Nat} (F : Family n) (a b : Affine n) :
    ((SourceAffineOutput.witnessCodec F.length n).encode (sourcePlaneQuery F a b)).length ≤
      2 * (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length + 1 := by
  have rows := SourceDirectionEncoding.family_bound n F [a, b]
  have dimension := SourceDirectionEncoding.dimension_bound n F [a, b]
  have bytes := SourceAffineOutput.witness_bytes_bound F.length n (sourcePlaneQuery F a b)
  omega

theorem exact_decoded_output {n : Nat} (F : Family n) (a b : Affine n) :
    ∃ used after, BitRegister.run program (used + 1) ⟨.running 0, start F a b⟩ = ⟨.accepted, after⟩ ∧
      (SourceAffineOutput.witnessCodec F.length n).decode (after.get 8) = some (sourcePlaneQuery F a b) ∧
      used ≤ costPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [a, b], F⟩).length := by
  obtain ⟨used, after, checked, bytes, bound⟩ := program_run F a b
  refine ⟨used, after, checked, ?_, bound⟩
  rw [bytes]
  exact NativeNormalization.NativeBitCodec.decode_encode _ _

end PNP.Concrete.ResidualReduction.SourcePlanePreparedQuery
