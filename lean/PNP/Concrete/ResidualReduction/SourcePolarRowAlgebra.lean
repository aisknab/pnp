import PNP.Concrete.ResidualReduction.SourceMatrixEncoding
import PNP.Concrete.ResidualReduction.SourceDirectionSpace
import PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra

/-! Exact coefficients for constructing the direction constraints. Pulling
the two factors back through an affine map gives the coefficients of their
linear evaluations on its basis directions, even when the map has a nonzero
origin. The resulting rows retain the existing source and basis order. These
identities specify the literal constructor; they do not assert its runtime. -/

namespace PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra
open PNP.Concrete
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra

theorem linearEval_pullback {n k : Nat} (f : Affine n) (m : AffineMap n k)
    (z : Point k) :
    linearEval f (linearMapEval m z) = linearEval (pullback f m) z := by
  unfold linearEval
  rw [homogeneousRow_eval, homogeneousRow_eval, linearMapEval, aEval_xor]
  rw [← pullback_eval f m z, ← pullback_eval f m (zeroPoint k), eval_zero_constant]
  simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem linearEval_pullback_unit {n k : Nat} (f : Affine n) (m : AffineMap n k)
    (j : Fin k) :
    linearEval f (linearMapEval m (unitPoint k j)) =
      bitAt (affineWord (pullback f m)) j.val := by
  rw [linearEval_pullback, linearEval_unit_coefficient]

/-- The constant slot is deliberately false, independently of both input
constants. Only the two variable-coefficient words are combined. -/
def combine (a b : Bool) : {n : Nat} → Affine n → Affine n → Affine n
  | 0, _, _ => false
  | _ + 1, (x, f), (y, g) => (Bool.xor (a && x) (b && y), combine a b f g)

theorem combine_eq {n : Nat} (a b : Bool) (f g : Affine n) :
    combine a b f g = aAdd (aScale a (homogeneousRow f)) (aScale b (homogeneousRow g)) := by
  induction n with
  | zero => cases f <;> cases g <;> cases a <;> cases b <;> rfl
  | succ n ih =>
    rcases f with ⟨x, f⟩; rcases g with ⟨y, g⟩
    change (Bool.xor (a && x) (b && y), combine a b f g) =
      (Bool.xor (a && Bool.xor x false) (b && Bool.xor y false),
        aAdd (aScale a (homogeneousRow f)) (aScale b (homogeneousRow g)))
    rw [Bool.xor_false, Bool.xor_false, ih]

theorem combine_constant {n : Nat} (a b : Bool) (f g : Affine n) :
    aConstant (combine a b f g) = false := by
  induction n with
  | zero => rfl
  | succ n ih => rcases f with ⟨x, f⟩; rcases g with ⟨y, g⟩; exact ih f g

theorem combine_word {n : Nat} (a b : Bool) (f g : Affine n) :
    affineWord (combine a b f g) = normalWord (combine a b f g) ++ [false] := by
  rw [word_split, combine_constant]

/-- Walk the two computed pullbacks together, excluding their constants. -/
def pairRows {n : Nat} (r : Row n) : {k : Nat} → Affine k → Affine k → System n
  | 0, _, _ => []
  | _ + 1, (a, f), (b, g) => combine b a r.left r.right :: pairRows r f g

theorem pairRows_length {n k : Nat} (r : Row n) (f g : Affine k) :
    (pairRows r f g).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases f with ⟨a, f⟩; rcases g with ⟨b, g⟩
    exact congrArg Nat.succ (ih f g)

theorem pairRows_finRange {n k : Nat} (r : Row n) (f g : Affine k) :
    pairRows r f g = (List.finRange k).map fun j =>
      combine (bitAt (affineWord g) j.val) (bitAt (affineWord f) j.val) r.left r.right := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases f with ⟨a, f⟩; rcases g with ⟨b, g⟩
    simp only [pairRows, List.finRange_succ, List.map_cons, List.map_map,
      Function.comp_def, Fin.val_zero, Fin.val_succ, affineWord_cons, bitAt, ih]

theorem combine_pullback_coefficient {n : Nat} (r : Row n) (s : Space n)
    (j : Fin s.parameters) :
    combine (bitAt (affineWord (pullback r.right s.forms)) j.val)
      (bitAt (affineWord (pullback r.left s.forms)) j.val) r.left r.right =
        polarForm r (s.direction (unitPoint s.parameters j)) := by
  simp only [combine_eq, polarForm, Space.direction, linearEval_pullback_unit]

theorem pairRows_pullback {n : Nat} (r : Row n) (s : Space n) :
    pairRows r (pullback r.left s.forms) (pullback r.right s.forms) =
      (List.finRange s.parameters).map fun j => polarForm r (s.direction (unitPoint _ j)) := by
  rw [pairRows_finRange]
  apply List.map_congr_left
  intro j _
  exact combine_pullback_coefficient r s j

def sourceRows {n : Nat} (F : Family n) (s : Space n) : System n :=
  F.flatMap fun r => pairRows r (pullback r.left s.forms) (pullback r.right s.forms)

theorem sourceRows_eq {n : Nat} (F : Family n) (s : Space n) :
    sourceRows F s = polarRows F s := by
  unfold sourceRows polarRows
  congr 1
  funext r
  exact pairRows_pullback r s

theorem sourceRows_bytes {n : Nat} (F : Family n) (s : Space n) :
    matrixBits (sourceRows F s) = matrixBits (polarRows F s) := by rw [sourceRows_eq]

end PNP.Concrete.ResidualReduction.SourcePolarRowAlgebra
