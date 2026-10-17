import PNP.Concrete.ResidualReduction.SourceLineSolver
import PNP.Concrete.ResidualReduction.SourceActivityConstruction

/-! Exact byte decompositions of both rank-one query matrices. Weight rows
precede covector rows. Normal coefficients ignore affine origins, while
activity coefficients retain the original source constants. These identities
specify the constructors; they are not execution or runtime claims. -/

namespace PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra

theorem constant_bits {A : Type} (xs : List A) :
    xs.map (fun _ => false) = List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]
theorem matrixBits_cons {m k : Nat} (M : Matrix (m + 1) k) :
    coefficientMatrixBits M = (List.finRange k).map (M 0) ++
      coefficientMatrixBits (fun i => M i.succ) := by
  simp only [coefficientMatrixBits, List.finRange_succ, List.flatMap_cons,
    List.flatMap_map]
theorem replicate_join (a b : Nat) :
    List.replicate a false ++ List.replicate b false = List.replicate (a + b) false := by
  induction a with
  | zero => simp only [List.replicate_zero, List.nil_append, Nat.zero_add]
  | succ a ih => simp only [List.replicate_succ, List.cons_append, Nat.succ_add, ih]

theorem zero_matrix_bits (m k : Nat) :
    coefficientMatrixBits (fun (_ : Fin m) (_ : Fin k) => false) = List.replicate (m * k) false := by
  induction m with
  | zero => simp only [coefficientMatrixBits, List.finRange_zero, List.flatMap_nil, Nat.zero_mul, List.replicate_zero]
  | succ m ih =>
    rw [matrixBits_cons, constant_bits, List.length_finRange, ih, replicate_join]
    congr 1
    simp only [Nat.add_mul, Nat.one_mul]
    omega
theorem coefficientMatrixBits_length {m k : Nat} (M : Matrix m k) :
    (coefficientMatrixBits M).length = m * k := by
  induction m with
  | zero => simp only [coefficientMatrixBits, List.finRange_zero, List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | succ m ih =>
    rw [matrixBits_cons, List.length_append, List.length_map, List.length_finRange, ih]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

def linearBits : {n k : Nat} → AffineMap n k → BitString
  | 0, _, _ => []
  | _ + 1, _, (f, fs) => normalWord f ++ linearBits fs
theorem linearBits_length {n k : Nat} (fs : AffineMap n k) :
    (linearBits fs).length = n * k := by
  induction n with
  | zero => simp only [linearBits, List.length_nil, Nat.zero_mul]
  | succ n ih =>
    rcases fs with ⟨f, fs⟩
    rw [linearBits, List.length_append, normalWord_length, ih]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
theorem normalWord_units {k : Nat} (f : Affine k) :
    normalWord f = (List.finRange k).map (fun j => linearEval f (unitPoint k j)) := by
  simp only [linearEval_unit_coefficient]
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases f with ⟨b, f⟩
    simp only [normalWord, List.finRange_succ, List.map_cons, List.map_map,
      Function.comp_def, Fin.val_zero, Fin.val_succ, affineWord_cons, bitAt, ih]
theorem linearMapEval_cons {n k : Nat} (f : Affine k) (fs : AffineMap n k) (z : Point k) :
    linearMapEval (n := n + 1) (f, fs) z = (linearEval f z, linearMapEval fs z) := by
  simp only [linearMapEval, mapEval, pXor, linearEval, homogeneousRow_eval, eval_zero_constant]
theorem normal_matrix_bits {n k : Nat} (fs : AffineMap n k) :
    coefficientMatrixBits (bilinearCoefficients (fun w z => pointDot w (linearMapEval fs z))) =
      linearBits fs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases fs with ⟨f, fs⟩
    have head : (bilinearCoefficients (fun w z => pointDot w (linearMapEval (n := n + 1) (f, fs) z))) 0 =
        (fun j => linearEval f (unitPoint k j)) := by
      funext j
      simp only [bilinearCoefficients, unitPoint_zero, linearMapEval_cons, pointDot,
        pointDot_zero_left, Bool.true_and, Bool.xor_false]
    have tail : (fun i => (bilinearCoefficients (fun w z => pointDot w (linearMapEval (n := n + 1) (f, fs) z))) i.succ) =
        bilinearCoefficients (fun w z => pointDot w (linearMapEval fs z)) := by
      funext i j
      simp only [bilinearCoefficients, unitPoint_succ, linearMapEval_cons, pointDot,
        Bool.false_and, Bool.false_xor]
    rw [matrixBits_cons, head, tail, ← normalWord_units, ih]
    rfl

def suffixMatrix {n k : Nat} (m : Nat) (fs : AffineMap n k) : Matrix (n + m) k :=
  bilinearCoefficients (fun w z => pointDot (splitPoint m w).2 (linearMapEval fs z))
theorem suffixMatrix_first {n k : Nat} (m : Nat) (fs : AffineMap n k) (j : Fin k) :
    suffixMatrix (m + 1) fs 0 j = false := by
  simp only [suffixMatrix, bilinearCoefficients, Nat.add_succ, unitPoint_zero, splitPoint, split_zero, pointDot_zero_left]
theorem suffixMatrix_next {n k : Nat} (m : Nat) (fs : AffineMap n k) (i : Fin (n + m)) (j : Fin k) :
    suffixMatrix (m + 1) fs i.succ j = suffixMatrix m fs i j := by
  simp only [suffixMatrix, bilinearCoefficients, Nat.add_succ, unitPoint_succ, splitPoint]
theorem suffixMatrix_bits {n k : Nat} (m : Nat) (fs : AffineMap n k) :
    coefficientMatrixBits (m := n + m) (k := k) (suffixMatrix (n := n) (k := k) m fs) =
      List.replicate (m * k) false ++ linearBits fs := by
  induction m with
  | zero =>
    simpa only [suffixMatrix, splitPoint, Nat.add_zero, Nat.zero_mul, List.replicate_zero, List.nil_append] using normal_matrix_bits (n := n) (k := k) fs
  | succ m ih =>
    have head : suffixMatrix (n := n) (k := k) (m + 1) fs 0 = (fun _ => false) :=
      funext (suffixMatrix_first (n := n) (k := k) m fs)
    have tail : (fun (i : Fin (n + m)) => suffixMatrix (n := n) (k := k) (m + 1) fs i.succ) =
        suffixMatrix (n := n) (k := k) m fs := by
      funext i j
      exact suffixMatrix_next (n := n) (k := k) m fs i j
    erw [matrixBits_cons, head, tail, constant_bits, List.length_finRange, ih, ← List.append_assoc, replicate_join]
    have count : k + m * k = (m + 1) * k := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    rw [count]

def prefixMatrix {n : Nat} (F : Family n) (s : Space n) : Matrix (n + F.length) s.parameters :=
  bilinearCoefficients (fun w z => weightedActivity F (splitPoint F.length w).1 (s.direction z))
theorem prefixMatrix_first {n : Nat} (r : Row n) (F : Family n) (s : Space n) (j : Fin s.parameters) :
    prefixMatrix (r :: F) s 0 j = activityCoefficients r s j := by
  simp only [prefixMatrix, bilinearCoefficients, List.length_cons, Nat.add_succ, unitPoint_zero,
    splitPoint, split_zero, weightedActivity, SourceClosure.weightedActivity_zero_weights,
    Bool.true_and, Bool.xor_false, activityCoefficients]
theorem prefixMatrix_next {n : Nat} (r : Row n) (F : Family n) (s : Space n)
    (i : Fin (n + F.length)) (j : Fin s.parameters) :
    prefixMatrix (r :: F) s i.succ j = prefixMatrix F s i j := by
  simp only [prefixMatrix, bilinearCoefficients, List.length_cons, Nat.add_succ, unitPoint_succ,
    splitPoint, weightedActivity, Bool.false_and, Bool.false_xor]
theorem prefixMatrix_bits {n : Nat} (F : Family n) (s : Space n) :
    coefficientMatrixBits (m := n + F.length) (k := s.parameters) (prefixMatrix (n := n) F s) =
      coefficientMatrixBits (activityMatrix s F) ++ List.replicate (n * s.parameters) false := by
  induction F with
  | nil => exact zero_matrix_bits n s.parameters
  | cons r F ih =>
    have head : prefixMatrix (r :: F) s 0 = activityCoefficients r s := funext (prefixMatrix_first r F s)
    have tail : (fun (i : Fin (n + F.length)) => prefixMatrix (n := n) (r :: F) s i.succ) =
        prefixMatrix (n := n) F s := by
      funext i j
      exact prefixMatrix_next r F s i j
    erw [matrixBits_cons, head, tail, ih, matrixBits_cons]
    simp only [activityMatrix, Fin.cases_zero, Fin.cases_succ, List.append_assoc]

theorem normal_query_bytes {n : Nat} (F : Family n) (alpha : Affine n) :
    coefficientMatrixBits (normalQueryMatrix F alpha) =
      List.replicate (F.length * (directionSpace F [alpha]).parameters) false ++
        linearBits (directionSpace F [alpha]).forms :=
  suffixMatrix_bits F.length (directionSpace F [alpha]).forms
theorem activity_query_bytes {n : Nat} (F : Family n) (alpha : Affine n) :
    coefficientMatrixBits (activityQueryMatrix F alpha) =
      sourceBits F (directionSpace F [alpha]) ++
        List.replicate (n * (directionSpace F [alpha]).parameters) false := by
  rw [sourceBits_matrix]
  exact prefixMatrix_bits F (directionSpace F [alpha])

end PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra
