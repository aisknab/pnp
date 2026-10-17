import PNP.Concrete.ResidualReduction.SourceHistoryPolynomial
import PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions
import PNP.Concrete.NativeNormalization.NativeOutputPacket

/-! Exact sparse-to-dense byte specification for the native source adapter.
Repeated sparse labels are XORed, not deduplicated as a set. Input systems store
b/a/e, while the target family must store b/e/a. These are byte and size proofs;
the literal conversion machine remains a separate implementation obligation. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeEncoding
open PNP.Concrete PNP.Concrete.NativeNormalization
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction

def affineWord {n : Nat} (a : Affine n) : BitString := (SourceEncoding.affineCodec n).encode a

theorem constant_word (n : Nat) (b : Bool) :
    affineWord (aConst n b) = List.replicate n false ++ [b] := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons false) ih

theorem add_word {n : Nat} (a b : Affine n) :
    affineWord (aAdd a b) = List.zipWith Bool.xor (affineWord a) (affineWord b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨a0,a⟩
    rcases b with ⟨b0,b⟩
    exact congrArg (List.cons (Bool.xor a0 b0)) (ih a b)

theorem add_zero_left {n : Nat} (a : Affine n) : aAdd (aConst n false) a = a := by
  induction n with
  | zero => exact Bool.false_xor a
  | succ n ih =>
    rcases a with ⟨b,a⟩
    change (Bool.xor false b,aAdd (aConst n false) a) = (b,a)
    rw [Bool.false_xor,ih a]
theorem add_zero_right {n : Nat} (a : Affine n) : aAdd a (aConst n false) = a := by
  induction n with
  | zero => exact Bool.xor_false a
  | succ n ih =>
    rcases a with ⟨b,a⟩
    change (Bool.xor b false,aAdd a (aConst n false)) = (b,a)
    rw [Bool.xor_false,ih a]
theorem add_comm {n : Nat} (a b : Affine n) : aAdd a b = aAdd b a := by
  induction n with
  | zero => exact Bool.xor_comm a b
  | succ n ih =>
    rcases a with ⟨a0,a⟩
    rcases b with ⟨b0,b⟩
    change (Bool.xor a0 b0,aAdd a b) = (Bool.xor b0 a0,aAdd b a)
    rw [Bool.xor_comm a0 b0,ih a b]
theorem add_assoc {n : Nat} (a b c : Affine n) :
    aAdd (aAdd a b) c = aAdd a (aAdd b c) := by
  induction n with
  | zero => exact Bool.xor_assoc a b c
  | succ n ih =>
    rcases a with ⟨a0,a⟩
    rcases b with ⟨b0,b⟩
    rcases c with ⟨c0,c⟩
    change (Bool.xor (Bool.xor a0 b0) c0,aAdd (aAdd a b) c) =
      (Bool.xor a0 (Bool.xor b0 c0),aAdd a (aAdd b c))
    rw [Bool.xor_assoc,ih a b c]

theorem coordinate_word (n : Nat) (i : Fin n) :
    affineWord (NativeSource.coordinateForm n i) =
      (SourceEncoding.pointCodec n).encode (ConstrainedBilinear.unitPoint n i) ++ [false] := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change true :: affineWord (aConst n false) =
        true :: ((SourceEncoding.pointCodec n).encode (BinaryLinear.zeroPoint n) ++ [false])
      rw [constant_word,SourceUnitDirectionInstructions.zero_bytes]
    · change false :: affineWord (NativeSource.coordinateForm n j) =
        false :: ((SourceEncoding.pointCodec n).encode (ConstrainedBilinear.unitPoint n j) ++ [false])
      rw [ih j]

def termsWord {c : Nat} (xs : NativeCoefficients.Coefficients c) (constant : Bool) : BitString :=
  affineWord (aAdd (NativeSource.sparseForm xs) (aConst (2 * c) constant))
def accumulate {c : Nat} : NativeCoefficients.Coefficients c → Affine (2 * c) → Affine (2 * c)
  | [],a => a
  | r :: rest,a => accumulate rest (aAdd (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex r)) a)

theorem accumulate_exact {c : Nat} (xs : NativeCoefficients.Coefficients c) (a : Affine (2 * c)) :
    accumulate xs a = aAdd (NativeSource.sparseForm xs) a := by
  induction xs generalizing a with
  | nil => exact (add_zero_left a).symm
  | cons r rest ih =>
    rw [accumulate,ih,NativeSource.sparseForm,← add_assoc,add_comm (NativeSource.sparseForm rest),add_assoc]

theorem accumulate_word {c : Nat} (xs : NativeCoefficients.Coefficients c) (constant : Bool) :
    affineWord (accumulate xs (aConst (2 * c) constant)) = termsWord xs constant := by
  rw [accumulate_exact]
  rfl
theorem terms_nil (c : Nat) (constant : Bool) :
    termsWord ([] : NativeCoefficients.Coefficients c) constant =
      List.replicate (2 * c) false ++ [constant] := by
  rw [termsWord,NativeSource.sparseForm,add_zero_left,constant_word]
theorem terms_cons {c : Nat} (r : NativeEquations.Row c) (xs : NativeCoefficients.Coefficients c)
    (constant : Bool) :
    termsWord (r :: xs) constant =
      List.zipWith Bool.xor (affineWord (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex r)))
        (termsWord xs constant) := by
  rw [termsWord,NativeSource.sparseForm,add_assoc,add_word]
  rfl
theorem terms_length {c : Nat} (xs : NativeCoefficients.Coefficients c) (constant : Bool) :
    (termsWord xs constant).length = 2 * c + 1 := SourceEncoding.affine_length _
theorem terms_false {c : Nat} (xs : NativeCoefficients.Coefficients c) :
    termsWord xs false = affineWord (NativeSource.sparseForm xs) := by
  rw [termsWord,add_zero_right]

def zeroRow {c : Nat} (xs : NativeCoefficients.Coefficients c) : BitString :=
  false :: (termsWord xs false ++ (List.replicate (2 * c) false ++ [true]))
def oneRow {c : Nat} (xs : NativeCoefficients.Coefficients c) : BitString :=
  false :: (termsWord xs true ++ (List.replicate (2 * c) false ++ [true]))
def productRow {c : Nat} (entry : NativeEquations.Row c × NativeCoefficients.Coefficients c) : BitString :=
  false :: (affineWord (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex entry.1)) ++
    termsWord entry.2 true)

theorem zeroRow_exact {c : Nat} (xs : NativeCoefficients.Coefficients c) :
    (SourceEncoding.rowCodec (2 * c)).encode (NativeSource.requireZero (NativeSource.sparseForm xs)) =
      zeroRow xs := by
  change false :: (affineWord (NativeSource.sparseForm xs) ++ affineWord (aConst (2 * c) true)) = _
  rw [constant_word,zeroRow,terms_false]
theorem oneRow_exact {c : Nat} (xs : NativeCoefficients.Coefficients c) :
    (SourceEncoding.rowCodec (2 * c)).encode (NativeSource.requireOne (NativeSource.sparseForm xs)) =
      oneRow xs := by
  change false :: (termsWord xs true ++ affineWord (aConst (2 * c) true)) = _
  rw [constant_word]
  rfl
theorem productRow_exact {c : Nat} (entry : NativeEquations.Row c × NativeCoefficients.Coefficients c) :
    (SourceEncoding.rowCodec (2 * c)).encode (NativeSource.productRow entry) = productRow entry := rfl

private theorem sequence_append {α : Type} (f : α → BitString) (xs ys : List α) :
    encodeSeq f (xs ++ ys) = encodeSeq f xs ++ encodeSeq f ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,encodeSeq,ih,List.append_assoc]
private theorem sequence_map {α β : Type} (f : β → BitString) (g : α → β) (xs : List α) :
    encodeSeq f (xs.map g) = encodeSeq (fun x => f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,encodeSeq,ih]

def familyBits {c : Nat} (D : NativeSparseSystem.System c) : BitString :=
  oneRow D.b ++ (encodeSeq zeroRow D.e ++ encodeSeq productRow D.a)
def familyPacket {c : Nat} (D : NativeSparseSystem.System c) : BitString :=
  natural (2 * c) ++ (natural (1 + D.e.length + D.a.length) ++ familyBits D)

theorem family_bits {c : Nat} (D : NativeSparseSystem.System c) :
    encodeSeq (SourceEncoding.rowCodec (2 * c)).encode (NativeSource.family D) = familyBits D := by
  simp only [NativeSource.family,encodeSeq,sequence_append,sequence_map,oneRow_exact,
    zeroRow_exact,productRow_exact,familyBits]
theorem family_packet {c : Nat} (D : NativeSparseSystem.System c) :
    SourceHistoryEncoding.packet (NativeSource.family D) = familyPacket D := by
  rw [SourceHistoryEncoding.packet_bits]
  change natural (2 * c) ++ (natural (NativeSource.family D).length ++
    encodeSeq (SourceEncoding.rowCodec (2 * c)).encode (NativeSource.family D)) = _
  rw [NativeSource.family_row_count,family_bits]
  rfl

theorem input_counts {c : Nat} (D : NativeSparseSystem.System c) :
    c + D.a.length + D.e.length + 6 ≤ (NativeOutputPacket.encode (.system c D)).length := by
  simp only [NativeOutputPacket.encode,NativeSystemCodec.systemCodec,mappedCodec,pairCodec,
    NativeSystemCodec.coefficientsCodec,listCodec,List.length_append,natural_length,
    List.length_cons,List.length_nil]
  omega
theorem packet_length {c : Nat} (D : NativeSparseSystem.System c) :
    (familyPacket D).length = (2 * c + 1) + (1 + D.e.length + D.a.length + 1) +
      (4 * c + 3) * (1 + D.e.length + D.a.length) := by
  rw [← family_packet,SourceHistoryEncoding.packet_length,NativeSource.family_row_count]
  rw [show 2 * (2 * c) = 4 * c by omega]
theorem packet_size_bound {c : Nat} (D : NativeSparseSystem.System c) :
    let L := (NativeOutputPacket.encode (.system c D)).length
    (familyPacket D).length ≤ 4 * (L * L) + 6 * L + 2 := by
  dsimp only
  have counts := input_counts D
  have dimensions : c ≤ (NativeOutputPacket.encode (.system c D)).length := by omega
  have rows : 1 + D.e.length + D.a.length ≤ (NativeOutputPacket.encode (.system c D)).length := by omega
  have product := Nat.mul_le_mul
    (show 4 * c + 3 ≤ 4 * (NativeOutputPacket.encode (.system c D)).length + 3 by omega) rows
  rw [packet_length]
  simp only [Nat.add_mul,Nat.mul_assoc] at product ⊢
  omega

end PNP.Concrete.ResidualReduction.SourceNativeEncoding
