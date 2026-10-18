import PNP.Concrete.ResidualReduction.SourceRowReductionInstructions
import PNP.Concrete.ResidualReduction.MatrixStrictHeader
import PNP.Concrete.ResidualReduction.SourceChartFamily

/-! Exact all-row semantics and canonical family encodings for the literal
reduction pass. Failed rows may be consumed without short-circuiting, but their
failure is sticky: no partial family becomes a successful reduction. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (rowWord familyBits familyBits_encode familyBits_length)
open PNP.Concrete.ResidualReduction.SourceRowReductionState (reduceRow)

def emitted {n : Nat} : Option (Row n) → BitString
  | none => []
  | some r => rowWord r
def retained {n : Nat} (t : TailForm n) : Family (n + 1) → Family n
  | [] => []
  | r :: F => match reduceRow t r with
    | none => retained t F
    | some out => out :: retained t F
def valid {n : Nat} (t : TailForm n) : Family (n + 1) → Bool
  | [] => true
  | r :: F => (reduceRow t r).isSome && valid t F
def result {n : Nat} (t : TailForm n) (F : Family (n + 1)) : Option (Family n) :=
  if valid t F then some (retained t F) else none

theorem reduce_nil {n : Nat} (t : TailForm n) : t.reduce [] = some [] := by
  cases t <;> rfl
theorem reduce_cons {n : Nat} (t : TailForm n) (r : Row (n + 1)) (F : Family (n + 1)) :
    t.reduce (r :: F) = (reduceRow t r).bind fun head => (t.reduce F).map fun tail => head :: tail := by
  cases t <;> rfl

theorem result_eq_reduce {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    result t F = t.reduce F := by
  induction F with
  | nil => exact (reduce_nil t).symm
  | cons r F ih =>
    rw [reduce_cons]
    cases hr : reduceRow t r with
    | none =>
      simp only [result,valid,retained,hr,Option.isSome_none,Bool.false_and,
        Bool.false_eq_true,if_false,Option.bind_none]
    | some out =>
      rw [Option.bind_some,← ih]
      cases hv : valid t F <;>
        simp only [result,valid,retained,hr,hv,Option.isSome_some,Bool.true_and,
          Bool.false_eq_true,if_false,if_true,Option.map_none,Option.map_some]

theorem retained_length_le {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    (retained t F).length ≤ F.length := by
  induction F with
  | nil => exact Nat.le_refl _
  | cons r F ih =>
    cases hr : reduceRow t r <;> simp only [retained,hr,List.length_cons] <;> omega

theorem valid_length {n : Nat} (t : TailForm n) (F : Family (n + 1)) (h : valid t F = true) :
    (retained t F).length = F.length := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    cases hr : reduceRow t r with
    | none => simp only [valid,hr,Option.isSome_none,Bool.false_and,Bool.false_eq_true] at h
    | some out =>
      have tail : valid t F = true := by
        simpa only [valid,hr,Option.isSome_some,Bool.true_and] using h
      simpa only [retained,hr,List.length_cons] using congrArg Nat.succ (ih tail)

theorem retained_bits_cons {n : Nat} (t : TailForm n) (r : Row (n + 1)) (F : Family (n + 1)) :
    familyBits (retained t (r :: F)) = emitted (reduceRow t r) ++ familyBits (retained t F) := by
  cases hr : reduceRow t r <;> simp only [retained,hr,emitted,familyBits,List.nil_append]

theorem family_bytes {n : Nat} (F : Family n) :
    (SourceEncoding.familyCodec n).encode F = natural F.length ++ familyBits F := by
  change natural F.length ++ encodeSeq (SourceEncoding.rowCodec n).encode F = _
  rw [familyBits_encode]
theorem family_length {n : Nat} (F : Family n) :
    ((SourceEncoding.familyCodec n).encode F).length = (2 * n + 4) * F.length + 1 := by
  rw [family_bytes,List.length_append,natural_length,familyBits_length]
  simp only [Nat.add_mul]
  omega

def codec (n : Nat) : Codec (Option (Family n)) :=
  MatrixSolutionEncoding.optionCodec (SourceEncoding.familyCodec n)
theorem none_bytes (n : Nat) : (codec n).encode none = [false] := rfl
theorem some_bytes {n : Nat} (F : Family n) :
    (codec n).encode (some F) = true :: (natural F.length ++ familyBits F) := by
  change true :: (SourceEncoding.familyCodec n).encode F = _
  rw [family_bytes]
def output {n : Nat} (t : TailForm n) (F : Family (n + 1)) : BitString :=
  if valid t F then true :: (natural F.length ++ familyBits (retained t F)) else [false]

theorem output_eq {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    output t F = (codec n).encode (t.reduce F) := by
  rw [← result_eq_reduce]
  cases hv : valid t F with
  | false => simp only [output,result,hv,Bool.false_eq_true,if_false,none_bytes]
  | true => simp only [output,result,hv,if_true,some_bytes,valid_length t F hv]
theorem output_decode {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    (codec n).decode (output t F) = some (t.reduce F) := by
  rw [output_eq]
  exact decode_encode _ _
theorem output_length {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    (output t F).length ≤ (2 * n + 4) * F.length + 2 := by
  cases hv : valid t F with
  | false =>
    simp only [output,hv,Bool.false_eq_true,if_false,List.length_cons,List.length_nil]
    omega
  | true =>
    simp only [output,hv,if_true,List.length_cons,List.length_append,natural_length,
      familyBits_length,valid_length t F hv,Nat.add_mul]
    omega

abbrev Problem := (n : Nat) × (TailForm n × Family (n + 1))
def inputCodec : Codec Problem := SourceEncoding.dependentCodec natCodec
  (fun n => pairCodec (SourceComputedTailEncoding.codec n) (SourceEncoding.familyCodec (n + 1)))
def packet {n : Nat} (t : TailForm n) (F : Family (n + 1)) : BitString :=
  inputCodec.encode ⟨n,(t,F)⟩
theorem packet_bytes {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    packet t F = natural n ++ ((SourceComputedTailEncoding.codec n).encode t ++
      (natural F.length ++ familyBits F)) := by
  change natural n ++ ((SourceComputedTailEncoding.codec n).encode t ++
    (SourceEncoding.familyCodec (n + 1)).encode F) = _
  rw [family_bytes]
theorem packet_roundtrip {n : Nat} (t : TailForm n) (F : Family (n + 1)) :
    inputCodec.decode (packet t F) = some ⟨n,(t,F)⟩ := decode_encode _ _

end PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding
