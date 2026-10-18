import PNP.Concrete.ResidualReduction.SourceOriginalSuccessorPolynomial

/-! Exact bytes consumed and emitted by the complete history runner. A record
contains its actual source and selected step; it is not a supplied certificate. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceEncoding

def packet {n : Nat} (F : Family n) : BitString := SourceMatrixEncoding.codec.encode ⟨n,F⟩
def records (history : List StepRecord) : BitString := encodeSeq recordCodec.encode history
def recordPrefix {n : Nat} (F : Family (n + 1)) : BitString :=
  natural n ++ (familyCodec (n + 1)).encode F

theorem packet_bits {n : Nat} (F : Family n) :
    packet F = natural n ++ (familyCodec n).encode F := rfl
theorem positive_packet {n : Nat} (F : Family (n + 1)) :
    packet F = true :: recordPrefix F := by
  rw [packet_bits]
  simp only [recordPrefix,natural,List.replicate_succ,List.cons_append]
theorem record_bits {n : Nat} (F : Family (n + 1)) (s : ConstructedStep n F.length) :
    recordCodec.encode ⟨n,F,s⟩ = recordPrefix F ++ (stepCodec n F.length).encode s := by
  change natural n ++ ((familyCodec (n + 1)).encode F ++ (stepCodec n F.length).encode s) = _
  rw [recordPrefix,List.append_assoc]
theorem records_append (front back : List StepRecord) :
    records (front ++ back) = records front ++ records back := by
  induction front with
  | nil => rfl
  | cons q rest ih =>
    simp only [records,encodeSeq,List.cons_append] at *
    rw [ih,List.append_assoc]
theorem records_singleton (q : StepRecord) : records [q] = recordCodec.encode q := by
  simp only [records,encodeSeq,List.append_nil]
theorem record_accumulator (history : List StepRecord) {n : Nat}
    (F : Family (n + 1)) (s : ConstructedStep n F.length) :
    ((stepCodec n F.length).encode s).reverse ++
      ((recordPrefix F).reverse ++ (records history).reverse) =
        (records (history ++ [⟨n,F,s⟩])).reverse := by
  rw [records_append,records_singleton,record_bits,List.reverse_append,List.reverse_append,List.append_assoc]
theorem data_bits (d : ReductionData) :
    dataCodec.encode d = packet d.core ++ (natural d.history.length ++ records d.history) := by
  change natural d.dimension ++ ((familyCodec d.dimension).encode d.core ++
    (natural d.history.length ++ records d.history)) = _
  rw [packet_bits,List.append_assoc]

theorem step_bits {n m : Nat} (s : ConstructedStep n m) :
    (stepCodec n m).encode s = (pointCodec m).encode s.weights ++
      (natural s.pivot.val ++ ((pointCodec n).encode s.tail ++ (familyCodec n).encode s.output)) := rfl

theorem packet_length {n : Nat} (F : Family n) :
    (packet F).length = (n + 1) + (F.length + 1) + (2 * n + 3) * F.length :=
  SourceMatrixEncoding.codec_length n F

theorem successor_packet_bound {n : Nat} (F : Family (n + 1))
    (s : ConstructedStep n F.length) (selected : globalStep F = some s) :
    (packet s.output).length ≤ (packet F).length := by
  have rows := (globalStep_sound F s selected).1
  rw [packet_length,packet_length,rows]
  simp only [Nat.mul_add,Nat.add_mul]
  omega

end PNP.Concrete.ResidualReduction.SourceHistoryEncoding
