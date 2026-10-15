import PNP.Concrete.ResidualReduction.PointSupport
import PNP.Concrete.ResidualReduction.BilinearSelection

namespace PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
abbrev Matrix (m n : Nat) := BilinearSelection.Matrix m n

def rowDot : {n : Nat} → (Fin n → Bool) → Point n → Bool
  | 0, _, _ => false
  | _ + 1, f, (b, x) => Bool.xor (f 0 && b) (rowDot (fun i => f i.succ) x)

def bilinearEval : {m n : Nat} → Matrix m n → Point m → Point n → Bool
  | 0, _, _, _, _ => false
  | _ + 1, _, M, (b, x), y =>
    Bool.xor (b && rowDot (M 0) y) (bilinearEval (fun i => M i.succ) x y)

private theorem xor_split :
    ∀ a b c d : Bool,
      Bool.xor (Bool.xor a b) (Bool.xor c d) =
        Bool.xor (Bool.xor a c) (Bool.xor b d) := by decide

private theorem and_xor :
    ∀ a b c : Bool, (a && Bool.xor b c) = Bool.xor (a && b) (a && c) := by decide

private theorem xor_and :
    ∀ a b c : Bool, (Bool.xor a b && c) = Bool.xor (a && c) (b && c) := by decide

theorem rowDot_zero {n : Nat} (f : Fin n → Bool) :
    rowDot f (zeroPoint n) = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zeroPoint, rowDot, Bool.and_false, Bool.false_xor, ih]

theorem rowDot_additive {n : Nat} (f : Fin n → Bool) (x y : Point n) :
    rowDot f (pXor x y) = Bool.xor (rowDot f x) (rowDot f y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨a, x⟩
    rcases y with ⟨b, y⟩
    simp only [pXor, rowDot, ih, and_xor]
    exact xor_split _ _ _ _

theorem bilinear_zero_left {m n : Nat} (M : Matrix m n) (y : Point n) :
    bilinearEval M (zeroPoint m) y = false := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [zeroPoint, bilinearEval, Bool.false_and, Bool.false_xor, ih]

theorem bilinear_zero_right {m n : Nat} (M : Matrix m n) (x : Point m) :
    bilinearEval M x (zeroPoint n) = false := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨b, x⟩
    simp only [bilinearEval, rowDot_zero, Bool.and_false, Bool.false_xor, ih]

theorem bilinear_additive_left {m n : Nat} (M : Matrix m n)
    (x z : Point m) (y : Point n) :
    bilinearEval M (pXor x z) y =
      Bool.xor (bilinearEval M x y) (bilinearEval M z y) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨a, x⟩
    rcases z with ⟨b, z⟩
    simp only [pXor, bilinearEval, ih, xor_and]
    exact xor_split _ _ _ _

theorem bilinear_additive_right {m n : Nat} (M : Matrix m n)
    (x : Point m) (y z : Point n) :
    bilinearEval M x (pXor y z) =
      Bool.xor (bilinearEval M x y) (bilinearEval M x z) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rcases x with ⟨a, x⟩
    simp only [bilinearEval, rowDot_additive, ih, and_xor]
    exact xor_split _ _ _ _

/-- Every coefficient is computed from the two explicit solution maps. -/
def pullMatrix {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n) :
    Matrix s.parameters t.parameters :=
  fun i j => bilinearEval M
    (s.direction (unitPoint s.parameters i)) (t.direction (unitPoint t.parameters j))

theorem pull_row {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (i : Fin s.parameters) (js : List (Fin t.parameters)) :
    BilinearSelection.rowEval (pullMatrix M s t) i js =
      bilinearEval M (s.direction (unitPoint s.parameters i)) (t.direction (sumUnits js)) := by
  induction js with
  | nil => simp only [BilinearSelection.rowEval, sumUnits, direction_zero, bilinear_zero_right]
  | cons j js ih =>
    simp only [BilinearSelection.rowEval, sumUnits, Space.direction_additive,
      bilinear_additive_right, ih, pullMatrix]

theorem pull_eval {m n : Nat} (M : Matrix m n) (s : Space m) (t : Space n)
    (is : List (Fin s.parameters)) (js : List (Fin t.parameters)) :
    BilinearSelection.eval (pullMatrix M s t) is js =
      bilinearEval M (s.direction (sumUnits is)) (t.direction (sumUnits js)) := by
  induction is with
  | nil => simp only [BilinearSelection.eval, sumUnits, direction_zero, bilinear_zero_left]
  | cons i is ih =>
    simp only [BilinearSelection.eval, sumUnits, Space.direction_additive,
      bilinear_additive_left, ih, pull_row]

end PNP.Concrete.ResidualReduction.ConstrainedBilinear
