import PNP.Concrete.ResidualReduction.SourceMatrixLoop
import PNP.Concrete.ResidualReduction.SourceDirectionEncoding

/-! The complete plane-constraint matrix is obtained from the original family
and its two input factors. One source-derived row supplies the affine right-hand
side. The old complete matrix constructor then emits the desired row followed
by one padding bit; the next literal pass must remove that bit, not the actual
affine constant. These are exact byte identities, not execution claims. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneMatrix
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions

def coefficients {n : Nat} : (F : Family n) → Point n → Point n → Bool → Affine F.length
  | [], _, _, c => c
  | r :: F, x, y, c => (polar r x y, coefficients F x y c)
theorem coefficients_eval {n : Nat} (F : Family n) (x y : Point n) (c : Bool)
    (w : Point F.length) :
    aEval (coefficients F x y c) w = Bool.xor (weightedPolar F w x y) c := by
  induction F with
  | nil => simp only [coefficients, aEval, weightedPolar, Bool.false_xor]
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [coefficients, aEval, weightedPolar, ih, Bool.and_comm, Bool.xor_assoc]
theorem coefficients_word {n : Nat} (F : Family n) (x y : Point n) (c : Bool) :
    affineWord (coefficients F x y c) = F.map (fun r => polar r x y) ++ [c] := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    simp only [coefficients, affineWord_cons, List.map_cons, List.cons_append, ih]
theorem plane_coefficients {n : Nat} (F : Family n) (alpha beta : Affine n) (x y : Point n) :
    planeConstraint F alpha beta x y = coefficients F x y (fixedWedge alpha beta x y) := by
  apply SourceBalance.affine_eval_ext
  intro w
  rw [planeConstraint_eval, coefficients_eval]
  rfl
theorem plane_word {n : Nat} (F : Family n) (alpha beta : Affine n) (i j : Fin n) :
    affineWord (planeConstraint F alpha beta (unitPoint n i) (unitPoint n j)) =
      F.map (fun r => polarBit r i.val j.val) ++ [fixedWedge alpha beta (unitPoint n i) (unitPoint n j)] := by
  rw [plane_coefficients, coefficients_word]
  simp only [polar_units]

def synthetic {n : Nat} (alpha beta : Affine n) : Row n := ⟨false, alpha, beta⟩
def augmented {n : Nat} (F : Family n) (alpha beta : Affine n) : Family n :=
  F ++ [synthetic alpha beta]
theorem synthetic_polar {n : Nat} (alpha beta : Affine n) (i j : Fin n) :
    polarBit (synthetic alpha beta) i.val j.val = fixedWedge alpha beta (unitPoint n i) (unitPoint n j) := by
  simp only [fixedWedge, linearEval_unit_coefficient, polarBit, synthetic]
theorem augmented_length {n : Nat} (F : Family n) (alpha beta : Affine n) :
    (augmented F alpha beta).length = F.length + 1 := by
  simp only [augmented, List.length_append, List.length_cons, List.length_nil]
theorem familyBits_append {n : Nat} (F G : Family n) :
    familyBits (F ++ G) = familyBits F ++ familyBits G := by
  induction F with
  | nil => rfl
  | cons r F ih => simp only [List.cons_append, familyBits, ih, List.append_assoc]
theorem augmented_bits {n : Nat} (F : Family n) (alpha beta : Affine n) :
    familyBits (augmented F alpha beta) = familyBits F ++ false :: matrixBits [alpha, beta] := by
  simp only [augmented, familyBits_append, familyBits, rowWord, synthetic, matrixBits,
    List.append_nil]

def paddedRows {m : Nat} : System m → BitString
  | [] => []
  | a :: rows => (affineWord a ++ [false]) ++ paddedRows rows
theorem paddedRows_append {m : Nat} (as bs : System m) :
    paddedRows (as ++ bs) = paddedRows as ++ paddedRows bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, paddedRows, ih, List.append_assoc]
theorem paddedRows_map {A : Type} {m : Nat} (f : A → Affine m) (xs : List A) :
    paddedRows (xs.map f) = xs.flatMap (fun x => affineWord (f x) ++ [false]) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, paddedRows, List.flatMap_cons, ih]
theorem paddedRows_flatMap {A : Type} {m : Nat} (f : A → System m) (xs : List A) :
    paddedRows (xs.flatMap f) = xs.flatMap (fun x => paddedRows (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, paddedRows_append, ih]
theorem paddedRows_length {m : Nat} (rows : System m) :
    (paddedRows rows).length = (m + 2) * rows.length := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    simp only [paddedRows, List.length_append, affineWord_length, List.length_cons,
      List.length_nil, ih, Nat.mul_succ]
    omega

/-- The complete existing all-coordinate builder supplies exactly the desired
plane equations plus one removable padding bit per row. No equation or source
coefficient is supplied independently of F, alpha and beta. -/
theorem augmented_matrix {n : Nat} (F : Family n) (alpha beta : Affine n) :
    matrixBits (SourceClosure.affineMaskRows (augmented F alpha beta)) =
      paddedRows (SourcePlane.planeRows F alpha beta) := by
  rw [affineMask_bytes]
  unfold SourcePlane.planeRows
  rw [paddedRows_flatMap]
  congr 1
  funext i
  rw [paddedRows_map]
  congr 1
  funext j
  rw [plane_word]
  simp only [augmented, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc, List.cons_append, List.nil_append, synthetic_polar]

end PNP.Concrete.ResidualReduction.SourcePlaneMatrix
