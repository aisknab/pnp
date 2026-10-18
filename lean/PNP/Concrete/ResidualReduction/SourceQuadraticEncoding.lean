import PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra

/-! Reversible triangular storage for the existing Boolean quadratic type.
Its width is fixed by the dimension. Addition is bytewise xor, and the zero
polynomial is a fixed-width zero word; no assignment enumeration is involved. -/

namespace PNP.Concrete.ResidualReduction.SourceQuadraticEncoding
open PNP.Concrete PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra

def codec : (n : Nat) → Codec (Quadratic n)
  | 0 => bitCodec
  | n + 1 => pairCodec (SourceEncoding.affineCodec n) (codec n)
def word {n : Nat} (q : Quadratic n) : BitString := (codec n).encode q

theorem word_zero_dimension (b : Bool) : word (n := 0) b = [b] := rfl
theorem word_cons {n : Nat} (a : Affine n) (q : Quadratic n) :
    word (n := n + 1) (a,q) = affineWord a ++ word q := rfl
theorem roundtrip {n : Nat} (q : Quadratic n) : (codec n).decode (word q) = some q :=
  decode_encode (codec n) q
theorem word_length {n : Nat} (q : Quadratic n) : (word q).length = quadraticBits n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases q with ⟨a,q⟩
    simp only [word_cons,List.length_append,affineWord_length,ih,quadraticBits,affineBits]

private theorem zip_append (xs ys rest others : BitString) (h : xs.length = ys.length) :
    List.zipWith Bool.xor (xs ++ rest) (ys ++ others) =
      List.zipWith Bool.xor xs ys ++ List.zipWith Bool.xor rest others := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b ys => simp only [List.length_nil,List.length_cons] at h; omega
  | cons a xs ih =>
    cases ys with
    | nil => simp only [List.length_nil,List.length_cons] at h; omega
    | cons b ys =>
      have ht : xs.length = ys.length := by
        simp only [List.length_cons] at h; omega
      simpa only [List.cons_append,List.zipWith_cons_cons] using
        congrArg (List.cons (Bool.xor a b)) (ih ys ht)

theorem word_add {n : Nat} (p q : Quadratic n) :
    word (qAdd p q) = List.zipWith Bool.xor (word p) (word q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨a,p⟩
    rcases q with ⟨b,q⟩
    change affineWord (aAdd a b) ++ word (qAdd p q) =
      List.zipWith Bool.xor (affineWord a ++ word p) (affineWord b ++ word q)
    rw [MatrixPullbackAlgebra.word_add,ih]
    exact (zip_append (affineWord a) (affineWord b) (word p) (word q)
      (by rw [affineWord_length,affineWord_length])).symm

theorem affine_zero_word (n : Nat) : affineWord (aConst n false) = List.replicate (n + 1) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false :: affineWord (aConst n false) = List.replicate (n + 1 + 1) false
    change false :: affineWord (aConst n false) = false :: List.replicate (n + 1) false
    exact congrArg (List.cons false) ih

private theorem replicate_join (n m : Nat) :
    List.replicate n false ++ List.replicate m false = List.replicate (n + m) false := by
  induction n with
  | zero => simp only [Nat.zero_add,List.replicate_zero,List.nil_append]
  | succ n ih =>
    simpa only [List.replicate_succ,List.cons_append,Nat.succ_add] using
      congrArg (List.cons false) ih

theorem word_zero (n : Nat) :
    word (qOfAffine (aConst n false)) = List.replicate (quadraticBits n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change affineWord (aConst n false) ++ word (qOfAffine (aConst n false)) = _
    rw [affine_zero_word,ih]
    exact replicate_join (n + 1) (quadraticBits n)

theorem word_bound {n : Nat} (q : Quadratic n) :
    (word q).length ≤ (n + 1) * (n + 1) := by
  rw [word_length]
  have size := quadraticBits_exact n
  simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one] at size ⊢
  omega

end PNP.Concrete.ResidualReduction.SourceQuadraticEncoding
