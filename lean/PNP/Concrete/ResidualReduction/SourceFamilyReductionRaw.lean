import PNP.Concrete.ResidualReduction.SourceFamilyReductionLoad

/-! A fixed input-only program for canonical computed-tail/family packets.
Every dimension, tail parameter, row count and coefficient is read from bytes.
The output is exactly TailForm.reduce, including unknown failures and empty
families. This stage does not assert that an arbitrary tail passes contract's
separate coefficient-equality gates, reject every malformed packet, or establish
the physical machine cost of the complete contraction history. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyReductionRaw
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding
open PNP.Concrete.ResidualReduction.SourceFamilyReductionState (finished)

def block : Block 23 := .seq SourceFamilyReductionLoad.block SourceFamilyReductionInstructions.block
def fuel {n : Nat} (t : TailForm n) (F : Family (n + 1)) : Nat :=
  SourceFamilyReductionLoad.fuel t F + SourceFamilyReductionInstructions.fuel t F

theorem block_exec {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    Exec block (SourceFamilyReductionLoad.initial (packet t F ++ suffix)) (fuel t F)
      (finished t suffix ((codec n).encode (t.reduce F))) :=
  Exec.seq (SourceFamilyReductionLoad.block_exec t F suffix)
    (SourceFamilyReductionInstructions.block_exec t F suffix)

theorem program_run {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    BitRegister.run (block.program 0 8) (fuel t F + 1)
      ⟨.running 0,SourceFamilyReductionLoad.initial (packet t F ++ suffix)⟩ =
      ⟨.accepted,finished t suffix ((codec n).encode (t.reduce F))⟩ :=
  (block_exec t F suffix).program_run 0 8

theorem packet_length {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    (packet t F).length = (n + 1) + ((SourceComputedTailEncoding.codec n).encode t).length +
      ((SourceEncoding.familyCodec (n + 1)).encode F).length := by
  change (natural n ++ ((SourceComputedTailEncoding.codec n).encode t ++
    (SourceEncoding.familyCodec (n + 1)).encode F)).length = _
  simp only [List.length_append,natural_length,Nat.add_assoc]

theorem family_count_bound {n : Nat} (F : Family (n + 1)) :
    F.length ≤ ((SourceEncoding.familyCodec (n + 1)).encode F).length := by
  rw [family_bytes,List.length_append,natural_length]
  omega
theorem fuel_encoded_bound {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    fuel t F + 1 ≤ 165 * (packet t F).length + 43 := by
  have load := SourceFamilyReductionLoad.fuel_bound t F
  have transform := SourceFamilyReductionInstructions.fuel_encoded_bound t F
  have rows := family_count_bound F
  rw [packet_length]
  unfold fuel
  omega

theorem output_decode {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    (codec n).decode ((finished t suffix ((codec n).encode (t.reduce F))).get 8) = some (t.reduce F) :=
  decode_encode _ _
theorem output_bound {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    ((finished t suffix ((codec n).encode (t.reduce F))).get 8).length ≤ (2 * n + 4) * F.length + 2 := by
  change ((codec n).encode (t.reduce F)).length ≤ _
  rw [← output_eq]
  exact output_length t F
theorem suffix_get {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) :
    (finished t suffix ((codec n).encode (t.reduce F))).get 0 = suffix := rfl

end PNP.Concrete.ResidualReduction.SourceFamilyReductionRaw
