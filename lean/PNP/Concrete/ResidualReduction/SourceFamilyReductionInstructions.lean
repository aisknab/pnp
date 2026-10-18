import PNP.Concrete.ResidualReduction.SourceFamilyReductionOutput

/-! Exact full-family source program. It constructs the family header, consumes
every row, preserves an arbitrary external suffix and emits exactly the existing
optional reduction. Source instruction bounds do not stand for physical copy
costs or the complete contraction history's runtime. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyReductionInstructions
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits familyBits_length)
open PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding
open PNP.Concrete.ResidualReduction.SourceFamilyReductionState

def accumulator {n : Nat} (t : TailForm n) (F : Family (n + 1)) : BitString :=
  (familyBits (retained t F)).reverse ++ (natural F.length).reverse
theorem accumulator_reverse {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    (accumulator t F).reverse = natural F.length ++ familyBits (retained t F) := by
  simp only [accumulator,List.reverse_append,List.reverse_reverse]
theorem accumulator_length {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    (accumulator t F).length ≤ (2 * n + 4) * F.length + 1 := by
  simp only [accumulator,List.length_append,List.length_reverse,familyBits_length,natural_length]
  have payload := Nat.mul_le_mul_left (2 * n + 3) (retained_length_le t F)
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega
theorem accumulator_output {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    SourceFamilyReductionOutput.bytes (accumulator t F) (valid t F) = (codec n).encode (t.reduce F) := by
  rw [← output_eq]
  simp only [SourceFamilyReductionOutput.bytes,accumulator_reverse,output]

def block : Block 23 := .seq SourceFamilyReductionLoop.header <|
  .seq SourceFamilyReductionLoop.block SourceFamilyReductionOutput.block
def fuel {n : Nat} (t : TailForm n) (F : Family (n + 1)) : Nat :=
  (3 * F.length + 5) + (SourceFamilyReductionLoop.fuel t F +
    SourceFamilyReductionOutput.fuel (accumulator t F) (valid t F))

theorem block_exec {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    Exec block (SourceFamilyReductionState.initial t F suffix) (fuel t F)
      (finished t suffix ((codec n).encode (t.reduce F))) := by
  have start := SourceFamilyReductionLoop.header_exec t F suffix
  have rows : Exec SourceFamilyReductionLoop.block
      (loopState t F suffix (natural F.length).reverse true (List.replicate F.length true))
      (SourceFamilyReductionLoop.fuel t F)
      (done t suffix (accumulator t F) (valid t F) (List.replicate F.length true)) := by
    simpa only [accumulator,Bool.true_and] using
      SourceFamilyReductionLoop.block_exec t F suffix (natural F.length).reverse true (List.replicate F.length true)
  have stop := SourceFamilyReductionOutput.block_exec t suffix (accumulator t F)
    (valid t F) (List.replicate F.length true)
  rw [accumulator_output] at stop
  exact Exec.seq start (Exec.seq rows stop)

theorem program_run {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    BitRegister.run (block.program 0 8) (fuel t F + 1)
      ⟨.running 0,SourceFamilyReductionState.initial t F suffix⟩ =
      ⟨.accepted,finished t suffix ((codec n).encode (t.reduce F))⟩ :=
  (block_exec t F suffix).program_run 0 8

theorem fuel_bound {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    fuel t F ≤ (321 * (n + 1) + 247) * F.length + 18 := by
  have rows := SourceFamilyReductionLoop.fuel_bound t F
  have ending := SourceFamilyReductionOutput.fuel_bound (accumulator t F) (valid t F)
  have size := accumulator_length t F
  simp only [fuel,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc] at *
  omega
theorem fuel_encoded_bound {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    fuel t F + 1 ≤ 161 * ((SourceEncoding.familyCodec (n + 1)).encode F).length := by
  have bound := fuel_bound t F
  simp only [family_length,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc] at *
  omega

theorem output_decode {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    (codec n).decode ((finished t suffix ((codec n).encode (t.reduce F))).get 8) = some (t.reduce F) :=
  decode_encode _ _
theorem suffix_get {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    (finished t suffix ((codec n).encode (t.reduce F))).get 0 = suffix := rfl

end PNP.Concrete.ResidualReduction.SourceFamilyReductionInstructions
