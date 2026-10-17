import PNP.Concrete.ResidualReduction.SourceReplayParser
import PNP.Concrete.ResidualReduction.SourceFamilyLoader

/-! Exact prefix classification for an arbitrary encoded source family.
A prefix reader must preserve following record fields; it must not require
the family to occupy the entire input. Every fixed-width row bit pattern is
constructively decoded, while missing headers and truncations fail closed. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayFamilyFields
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding

def count (input : BitString) : Nat := (MatrixStrictHeader.scan input).count
def amount (n : Nat) (input : BitString) : Nat := (2 * n + 3) * count input
def payload (n : Nat) (input : BitString) : BitString := (MatrixStrictHeader.scan input).rest.take (amount n input)
def rest (n : Nat) (input : BitString) : BitString := (MatrixStrictHeader.scan input).rest.drop (amount n input)
def valid (n : Nat) (input : BitString) : Bool :=
  if amount n input ≤ (MatrixStrictHeader.scan input).rest.length
  then (MatrixStrictHeader.scan input).terminated else false

theorem encode_bytes {n : Nat} (F : Family n) :
    (SourceEncoding.familyCodec n).encode F = natural F.length ++ familyBits F := by
  change natural F.length ++ encodeSeq (SourceEncoding.rowCodec n).encode F = _
  rw [familyBits_encode]

theorem canonical {n : Nat} (F : Family n) (suffix : BitString) :
    let input := (SourceEncoding.familyCodec n).encode F ++ suffix
    count input = F.length ∧ payload n input = familyBits F ∧ rest n input = suffix ∧ valid n input = true := by
  dsimp only
  rw [encode_bytes,List.append_assoc]
  simp only [count,payload,rest,valid,amount,MatrixStrictHeader.scan_canonical]
  have enough : (2 * n + 3) * F.length ≤ (familyBits F ++ suffix).length := by
    rw [List.length_append,familyBits_length]
    omega
  rw [if_pos enough,← familyBits_length F,List.take_left,List.drop_left]
  simp only [and_self]

theorem valid_parts (n : Nat) (input : BitString) (good : valid n input = true) :
    (MatrixStrictHeader.scan input).terminated = true ∧ amount n input ≤ (MatrixStrictHeader.scan input).rest.length := by
  unfold valid at good
  by_cases enough : amount n input ≤ (MatrixStrictHeader.scan input).rest.length
  · rw [if_pos enough] at good
    exact ⟨good,enough⟩
  · rw [if_neg enough] at good
    cases good

theorem parse_iff {n : Nat} (input : BitString) (F : Family n) (suffix : BitString) :
    (SourceEncoding.familyCodec n).parse input = some (F,suffix) ↔
      valid n input = true ∧ count input = F.length ∧ payload n input = familyBits F ∧ rest n input = suffix := by
  constructor
  · intro parsed
    have bytes := (SourceEncoding.familyCodec n).sound input F suffix parsed
    rw [← bytes]
    have fields := canonical F suffix
    exact ⟨fields.2.2.2,fields.1,fields.2.1,fields.2.2.1⟩
  · rintro ⟨good,rows,body,tail⟩
    have flags := valid_parts n input good
    have header : BitString.decodeLength input = some (count input,(MatrixStrictHeader.scan input).rest) := by
      rw [MatrixStrictHeader.scan_parse,flags.1]
      rfl
    have whole : (SourceEncoding.familyCodec n).encode F ++ suffix = input := by
      rw [encode_bytes,← rows,← body,← tail,List.append_assoc]
      change natural (count input) ++
        ((MatrixStrictHeader.scan input).rest.take (amount n input) ++
          (MatrixStrictHeader.scan input).rest.drop (amount n input)) = input
      rw [List.take_append_drop]
      exact natural_sound input _ _ header
    rw [← whole]
    exact (SourceEncoding.familyCodec n).roundtrip F suffix

theorem valid_parse (n : Nat) (input : BitString) (good : valid n input = true) :
    ∃ F : Family n, (SourceEncoding.familyCodec n).parse input = some (F,rest n input) := by
  have flags := valid_parts n input good
  have size : (payload n input).length = (2 * n + 3) * count input := by
    simp only [payload,List.length_take,Nat.min_eq_left flags.2]
    rfl
  obtain ⟨F,rows,bytes⟩ := SourceFamilyInput.payload_complete n (count input) (payload n input) size
  exact ⟨F,(parse_iff input F (rest n input)).mpr ⟨good,rows.symm,bytes.symm,rfl⟩⟩

theorem invalid_parse (n : Nat) (input : BitString) (bad : valid n input = false) :
    (SourceEncoding.familyCodec n).parse input = none := by
  cases parsed : (SourceEncoding.familyCodec n).parse input with
  | none => rfl
  | some pair =>
    rcases pair with ⟨F,suffix⟩
    have good := ((parse_iff input F suffix).mp parsed).1
    rw [bad] at good
    cases good

theorem count_bound (input : BitString) : count input ≤ input.length := by
  have h := MatrixStrictHeader.scan_size input
  unfold count
  omega
theorem payload_bound (n : Nat) (input : BitString) : (payload n input).length ≤ input.length := by
  have h := MatrixStrictHeader.scan_size input
  have take := Nat.min_le_right (amount n input) (MatrixStrictHeader.scan input).rest.length
  simp only [payload,List.length_take]
  omega
theorem rest_bound (n : Nat) (input : BitString) : (rest n input).length ≤ input.length := by
  have h := MatrixStrictHeader.scan_size input
  simp only [rest,List.length_drop]
  omega

end PNP.Concrete.ResidualReduction.SourceReplayFamilyFields
