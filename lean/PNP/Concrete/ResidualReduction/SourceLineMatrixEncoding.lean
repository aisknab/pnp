import PNP.Concrete.ResidualReduction.SourcePlaneMatrixAugmentation
import PNP.Concrete.ResidualReduction.SourceBilinearFamily
import PNP.Concrete.ResidualReduction.SourceUnitDirectionInstructions
import PNP.Concrete.ResidualReduction.SourceComputedContract

/-! Exact rank-one equations from an augmented source family. The original
weight coefficients come first, followed by the covector coefficients in the
existing coordinate order. Every extra row is derived from alpha and a unit
coordinate; no equation, matrix or semantic certificate is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceLineMatrix
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions

def vectorForm : {n : Nat} → Point n → Affine n
  | 0, _ => false
  | _ + 1, (b, x) => (b, vectorForm x)
theorem vectorForm_eval {n : Nat} (a x : Point n) :
    aEval (vectorForm a) x = pointDot a x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    rcases x with ⟨c, x⟩
    simp only [vectorForm, aEval, pointDot, ih]
theorem betaNormal_eq {n : Nat} (a : Point n) : betaNormal a = vectorForm a := by
  apply SourceBalance.affine_eval_ext
  intro x
  rw [betaNormal, linearForm_eval _ (pointDot_zero_right a) (pointDot_additive_right a)]
  exact (vectorForm_eval a x).symm
theorem vectorForm_word {n : Nat} (a : Point n) :
    affineWord (vectorForm a) = (SourceEncoding.pointCodec n).encode a ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    change b :: affineWord (vectorForm a) = b :: ((SourceEncoding.pointCodec n).encode a ++ [false])
    rw [ih]
theorem betaNormal_word {n : Nat} (a : Point n) :
    affineWord (betaNormal a) = (SourceEncoding.pointCodec n).encode a ++ [false] := by
  rw [betaNormal_eq, vectorForm_word]

def coefficients {n : Nat} : (F : Family n) → Point n → Point n → Affine n → Affine (n + F.length)
  | [], _, _, suffix => suffix
  | r :: F, x, y, suffix => (polar r x y, coefficients F x y suffix)
theorem coefficients_eval {n : Nat} (F : Family n) (x y : Point n) (suffix : Affine n)
    (w : Point (n + F.length)) :
    aEval (coefficients F x y suffix) w =
      Bool.xor (weightedPolar F (splitPoint F.length w).1 x y) (aEval suffix (splitPoint F.length w).2) := by
  induction F with
  | nil => simp only [coefficients, List.length_nil, splitPoint, weightedPolar, Bool.false_xor]
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [coefficients, List.length_cons, aEval, splitPoint, weightedPolar,
      ih, Bool.and_comm, Bool.xor_assoc]
theorem coefficients_word {n : Nat} (F : Family n) (x y : Point n) (suffix : Affine n) :
    affineWord (coefficients F x y suffix) = F.map (fun r => polar r x y) ++ affineWord suffix := by
  induction F with
  | nil => rfl
  | cons r F ih => simp only [coefficients, affineWord_cons, List.map_cons, List.cons_append, ih]

def covectorCoefficients {n : Nat} (alpha : Affine n) (x y : Point n) : Affine n :=
  linearForm (fun beta => wedge alpha beta x y)
theorem covectorCoefficients_eval {n : Nat} (alpha : Affine n) (x y beta : Point n) :
    aEval (covectorCoefficients alpha x y) beta = wedge alpha beta x y :=
  linearForm_eval _ (wedge_zero_beta alpha x y) (fun a b => wedge_additive_beta alpha a b x y) beta
theorem constraint_coefficients {n : Nat} (F : Family n) (alpha : Affine n) (x y : Point n) :
    polarConstraint F alpha x y = coefficients F x y (covectorCoefficients alpha x y) := by
  apply SourceBalance.affine_eval_ext
  intro w
  rw [polarConstraint, linearForm_eval _ (polarDifference_zero_weights F alpha x y)
    (fun a b => polarDifference_additive_weights F alpha a b x y), coefficients_eval, covectorCoefficients_eval]
  rfl
theorem constraint_word {n : Nat} (F : Family n) (alpha : Affine n) (x y : Point n) :
    affineWord (polarConstraint F alpha x y) = F.map (fun r => polar r x y) ++
      ((List.finRange n).map (fun j => wedge alpha (unitPoint n j) x y) ++ [false]) := by
  rw [constraint_coefficients, coefficients_word]
  exact congrArg (List.append (F.map (fun r => polar r x y)))
    (SourceBilinearFamily.coefficient_word (fun j => wedge alpha (unitPoint n j) x y))

def synthetic {n : Nat} (alpha : Affine n) (j : Fin n) : Row n :=
  ⟨false, alpha, betaNormal (unitPoint n j)⟩
def syntheticFamily {n : Nat} (alpha : Affine n) : Family n := (List.finRange n).map (synthetic alpha)
def augmented {n : Nat} (F : Family n) (alpha : Affine n) : Family n := F ++ syntheticFamily alpha
theorem synthetic_polar {n : Nat} (alpha : Affine n) (j : Fin n) (x y : Point n) :
    polar (synthetic alpha j) x y = wedge alpha (unitPoint n j) x y := by
  simp only [polar, synthetic, betaNormal_linearEval, wedge]
theorem synthetic_polar_units {n : Nat} (alpha : Affine n) (k i j : Fin n) :
    polarBit (synthetic alpha k) i.val j.val = wedge alpha (unitPoint n k) (unitPoint n i) (unitPoint n j) := by
  rw [← polar_units, synthetic_polar]
theorem augmented_length {n : Nat} (F : Family n) (alpha : Affine n) :
    (augmented F alpha).length = F.length + n := by
  simp only [augmented, syntheticFamily, List.length_append, List.length_map, List.length_finRange]

def rowBytes {n : Nat} (alpha : Affine n) (j : Nat) : BitString :=
  false :: (affineWord alpha ++ (SourceUnitDirectionInstructions.word n j ++ [false]))
def rowsBytes {n : Nat} (alpha : Affine n) (start count : Nat) : BitString :=
  (List.range' start count).flatMap (rowBytes alpha)
theorem rowBytes_exact {n : Nat} (alpha : Affine n) (j : Fin n) :
    rowBytes alpha j.val = rowWord (synthetic alpha j) := by
  simp only [rowBytes, rowWord, synthetic, betaNormal_word, SourceUnitDirectionInstructions.unit_bytes]
theorem rowsBytes_zero {n : Nat} (alpha : Affine n) (start : Nat) : rowsBytes alpha start 0 = [] := rfl
theorem rowsBytes_succ {n : Nat} (alpha : Affine n) (start count : Nat) :
    rowsBytes alpha start (count + 1) = rowBytes alpha start ++ rowsBytes alpha (start + 1) count := by
  simp only [rowsBytes, List.range'_succ, List.flatMap_cons]
theorem familyBits_map {A : Type} {n : Nat} (f : A → Row n) (xs : List A) :
    familyBits (xs.map f) = xs.flatMap (fun x => rowWord (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, familyBits, List.flatMap_cons, ih]
theorem synthetic_bytes {n : Nat} (alpha : Affine n) :
    familyBits (syntheticFamily alpha) = rowsBytes alpha 0 n := by
  rw [syntheticFamily, familyBits_map]
  unfold rowsBytes
  rw [← SourceMatrixSchedule.finite_range_values]
  simp only [List.flatMap_map]
  congr 1
  funext j
  exact (rowBytes_exact alpha j).symm
theorem augmented_bits {n : Nat} (F : Family n) (alpha : Affine n) :
    familyBits (augmented F alpha) = familyBits F ++ rowsBytes alpha 0 n := by
  rw [augmented, SourcePlaneMatrix.familyBits_append, synthetic_bytes]

/-- Exact complete matrix bytes, including the covector suffix, zero constants,
diagonal equations, and original solver order. This is not an execution claim. -/
theorem augmented_matrix {n : Nat} (F : Family n) (alpha : Affine n) :
    matrixBits (SourceClosure.affineMaskRows (augmented F alpha)) = matrixBits (rankOneRows F alpha) := by
  rw [affineMask_bytes]
  unfold rankOneRows
  rw [matrixBits_flatMap]
  congr 1
  funext i
  rw [matrixBits_map]
  congr 1
  funext j
  rw [constraint_word]
  simp only [augmented, syntheticFamily, List.map_append, List.map_map, Function.comp_def,
    synthetic_polar_units, polar_units, List.append_assoc]

end PNP.Concrete.ResidualReduction.SourceLineMatrix
