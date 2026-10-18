import PNP.Concrete.ResidualReduction.MatrixInputEncoding
import PNP.Concrete.ResidualReduction.SourceAffinePrelude
import PNP.Concrete.ResidualReduction.SourceSelectedScalar

/-! Exact source bytes for the affine-mask query. Its coefficients are read
from the two affine factors of each original row, not supplied as a matrix.
These encoding identities specify the constructor; they are not runtime
claims. The dimension is explicit even when the source family is empty. -/

namespace PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.MatrixInstructions

def bitAt : BitString → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: rest, k + 1 => bitAt rest k

theorem bitAt_drop (bits : BitString) (k : Nat) :
    bitAt bits k = (bits.drop k).headD false := by
  induction k generalizing bits with
  | zero => cases bits <;> rfl
  | succ k ih => cases bits with
    | nil => rfl
    | cons b rest => exact ih rest

theorem eval_unit_coefficient {n : Nat} (a : Affine n) (i : Fin n) :
    Bool.xor (aEval a (unitPoint n i)) (aConstant a) = bitAt (affineWord a) i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases a with ⟨b, a⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [unitPoint_zero, aEval, Bool.and_true, eval_zero_constant,
        aConstant, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      rfl
    · simpa only [unitPoint_succ, aEval, Bool.and_false, Bool.false_xor,
        aConstant, affineWord_cons, Fin.val_succ, bitAt] using ih a j

theorem linearEval_unit_coefficient {n : Nat} (a : Affine n) (i : Fin n) :
    linearEval a (unitPoint n i) = bitAt (affineWord a) i.val := by
  rw [linearEval, homogeneousRow_eval, eval_unit_coefficient]

def polarBit {n : Nat} (r : Row n) (i j : Nat) : Bool :=
  Bool.xor (bitAt (affineWord r.left) i && bitAt (affineWord r.right) j)
    (bitAt (affineWord r.right) i && bitAt (affineWord r.left) j)

theorem polar_units {n : Nat} (r : Row n) (i j : Fin n) :
    polar r (unitPoint n i) (unitPoint n j) = polarBit r i.val j.val := by
  simp only [polar, linearEval_unit_coefficient, polarBit]

def polarCoefficients {n : Nat} : (F : Family n) → Point n → Point n → Affine F.length
  | [], _, _ => false
  | r :: F, x, y => (polar r x y, polarCoefficients F x y)

theorem polarCoefficients_eval {n : Nat} (F : Family n) (x y : Point n)
    (w : Point F.length) : aEval (polarCoefficients F x y) w = weightedPolar F w x y := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [polarCoefficients, aEval, weightedPolar, ih, Bool.and_comm]

theorem polarCoefficients_word {n : Nat} (F : Family n) (x y : Point n) :
    affineWord (polarCoefficients F x y) = F.map (fun r => polar r x y) ++ [false] := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    simp only [polarCoefficients, affineWord_cons, List.map_cons, List.cons_append, ih]

theorem zero_planeConstraint {n : Nat} (F : Family n) (x y : Point n) :
    planeConstraint F (aConst n false) (aConst n false) x y = polarCoefficients F x y := by
  apply SourceBalance.affine_eval_ext
  intro w
  simp only [planeConstraint_eval, planeDifference, fixedWedge, SourceClosure.linearEval_const,
    Bool.false_and, Bool.xor_false, polarCoefficients_eval]

theorem planeConstraint_word {n : Nat} (F : Family n) (i j : Fin n) :
    affineWord (planeConstraint F (aConst n false) (aConst n false)
      (unitPoint n i) (unitPoint n j)) = F.map (fun r => polarBit r i.val j.val) ++ [false] := by
  rw [zero_planeConstraint, polarCoefficients_word]
  simp only [polar_units]

theorem matrixBits_map {A : Type} {m : Nat} (f : A → Affine m) (xs : List A) :
    matrixBits (xs.map f) = xs.flatMap (fun x => affineWord (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, matrixBits, List.flatMap_cons, ih]

theorem matrixBits_flatMap {A : Type} {m : Nat} (f : A → System m) (xs : List A) :
    matrixBits (xs.flatMap f) = xs.flatMap (fun x => matrixBits (f x)) := by
  have append (as bs : System m) : matrixBits (as ++ bs) = matrixBits as ++ matrixBits bs := by
    induction as with
    | nil => rfl
    | cons a as ih => simp only [List.cons_append, matrixBits, ih, List.append_assoc]
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, append, ih]

/-- Exact row and coefficient order of the existing query, including diagonal
rows and zero constants. No reassociation of the solver's input is hidden. -/
theorem affineMask_bytes {n : Nat} (F : Family n) :
    matrixBits (affineMaskRows F) = (List.finRange n).flatMap (fun i =>
      (List.finRange n).flatMap (fun j => F.map (fun r => polarBit r i.val j.val) ++ [false])) := by
  unfold affineMaskRows SourcePlane.planeRows
  rw [matrixBits_flatMap]
  congr 1
  funext i
  rw [matrixBits_map]
  congr 1
  funext j
  exact planeConstraint_word F i j

abbrev Problem := (n : Nat) × Family n
def codec : Codec Problem := SourceEncoding.dependentCodec natCodec SourceEncoding.familyCodec

def rowWord {n : Nat} (r : Row n) : BitString :=
  r.selected :: (affineWord r.left ++ affineWord r.right)
def familyBits {n : Nat} : Family n → BitString
  | [] => []
  | r :: F => rowWord r ++ familyBits F

theorem rowWord_encode {n : Nat} (r : Row n) :
    rowWord r = (SourceEncoding.rowCodec n).encode r := rfl
theorem rowWord_length {n : Nat} (r : Row n) : (rowWord r).length = 2 * n + 3 :=
  SourceEncoding.row_length r

theorem familyBits_encode {n : Nat} (F : Family n) :
    encodeSeq (SourceEncoding.rowCodec n).encode F = familyBits F := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    change rowWord r ++ encodeSeq (SourceEncoding.rowCodec n).encode F = _
    rw [ih]; rfl

theorem familyBits_length {n : Nat} (F : Family n) :
    (familyBits F).length = (2 * n + 3) * F.length := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    simp only [familyBits, List.length_append, rowWord_length, ih, List.length_cons,
      Nat.mul_add, Nat.mul_one]
    omega

theorem codec_bits (n : Nat) (F : Family n) :
    codec.encode ⟨n, F⟩ = natural n ++ (natural F.length ++ familyBits F) := by
  change natural n ++ (natural F.length ++ encodeSeq (SourceEncoding.rowCodec n).encode F) = _
  rw [familyBits_encode]

theorem codec_length (n : Nat) (F : Family n) :
    (codec.encode ⟨n, F⟩).length = (n + 1) + (F.length + 1) + (2 * n + 3) * F.length := by
  rw [codec_bits]
  simp only [List.length_append, natural_length, familyBits_length, Nat.add_assoc]

theorem dimension_bound (n : Nat) (F : Family n) : n ≤ (codec.encode ⟨n, F⟩).length := by
  rw [codec_length]; omega
theorem rowCount_bound (n : Nat) (F : Family n) : F.length ≤ (codec.encode ⟨n, F⟩).length := by
  rw [codec_length]; omega
theorem roundtrip (n : Nat) (F : Family n) : codec.decode (codec.encode ⟨n, F⟩) = some ⟨n, F⟩ :=
  decode_encode codec _
theorem canonical (bits : BitString) (problem : Problem) :
    codec.decode bits = some problem ↔ codec.encode problem = bits := decode_eq_some_iff codec bits problem

def affineMatrixPacket {n : Nat} (F : Family n) : BitString :=
  MatrixInputEncoding.codec.encode ⟨F.length, affineMaskRows F⟩

theorem affineMatrixPacket_bound (n : Nat) (F : Family n) :
    let L := (codec.encode ⟨n, F⟩).length
    (affineMatrixPacket F).length ≤ (L + 1) + (L * L + 1) + (L + 1) * (L * L) := by
  dsimp only
  rw [affineMatrixPacket, MatrixInputEncoding.codec_length, affineMaskRows, planeRows_length]
  have hn := dimension_bound n F
  have hm := rowCount_bound n F
  have square := Nat.mul_le_mul hn hn
  have payload := Nat.mul_le_mul (Nat.add_le_add_right hm 1) square
  omega

end PNP.Concrete.ResidualReduction.SourceMatrixEncoding
