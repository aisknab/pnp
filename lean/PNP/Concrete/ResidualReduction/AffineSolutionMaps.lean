import PNP.Concrete.ResidualReduction.BooleanCoefficients

namespace PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.FactoredContraction

/-- Explicit affine coefficient rows, not a supplied semantic map. -/
def AffineMap : Nat → Nat → Type
  | 0, _ => Unit
  | n + 1, k => Affine k × AffineMap n k

def mapEval : {n k : Nat} → AffineMap n k → Point k → Point n
  | 0, _, _, _ => ()
  | _ + 1, _, (f, fs), z => (aEval f z, mapEval fs z)

def pullback : {n k : Nat} → Affine n → AffineMap n k → Affine k
  | 0, k, c, _ => aConst k c
  | _ + 1, _, (b, f), (g, gs) => aAdd (aScale b g) (pullback f gs)

theorem pullback_eval {n k : Nat} (f : Affine n) (m : AffineMap n k)
    (z : Point k) :
    aEval (pullback f m) z = aEval f (mapEval m z) := by
  induction n with
  | zero => exact aConst_eval k f z
  | succ n ih =>
    rcases f with ⟨b, f⟩
    rcases m with ⟨g, gs⟩
    simp only [pullback, mapEval, aEval, aAdd_eval, aScale_eval, ih]

def raiseMap : {n k : Nat} → AffineMap n k → AffineMap n (k + 1)
  | 0, _, _ => ()
  | _ + 1, _, (f, fs) => ((false, f), raiseMap fs)

theorem raiseMap_eval {n k : Nat} (m : AffineMap n k) (b : Bool)
    (z : Point k) : mapEval (raiseMap m) (b, z) = mapEval m z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases m with ⟨f, fs⟩
    simp only [raiseMap, mapEval, aEval, Bool.false_and, Bool.false_xor, ih]

def freeMap {n k : Nat} (m : AffineMap n k) : AffineMap (n + 1) (k + 1) :=
  ((true, aConst k false), raiseMap m)

theorem freeMap_eval {n k : Nat} (m : AffineMap n k) (b : Bool)
    (z : Point k) : mapEval (freeMap m) (b, z) = (b, mapEval m z) := by
  simp only [freeMap, mapEval, aEval, aConst_eval, Bool.true_and,
    Bool.xor_false, raiseMap_eval]

def pivotMap {n k : Nat} (p : Affine n) (m : AffineMap n k) :
    AffineMap (n + 1) k :=
  (pullback p m, m)

theorem pivotMap_eval {n k : Nat} (p : Affine n) (m : AffineMap n k)
    (z : Point k) :
    mapEval (pivotMap p m) z = (aEval p (mapEval m z), mapEval m z) := by
  simp only [pivotMap, mapEval, pullback_eval]

def zeroPoint : (n : Nat) → Point n
  | 0 => ()
  | n + 1 => (false, zeroPoint n)

theorem eval_zero_constant {n : Nat} (f : Affine n) :
    aEval f (zeroPoint n) = aConstant f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases f with ⟨b, f⟩
    simp only [zeroPoint, aEval, Bool.and_false, Bool.false_xor, aConstant, ih]

def linearMapEval {n k : Nat} (m : AffineMap n k) (z : Point k) : Point n :=
  pXor (mapEval m z) (mapEval m (zeroPoint k))

theorem mapEval_affine_xor {n k : Nat} (m : AffineMap n k) (x y : Point k) :
    mapEval m (pXor x y) =
      pXor (pXor (mapEval m x) (mapEval m y)) (mapEval m (zeroPoint k)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases m with ⟨f, fs⟩
    simp only [mapEval, pXor, aEval_xor, eval_zero_constant, ih]

theorem mapEval_from_linear {n k : Nat} (m : AffineMap n k) (z : Point k) :
    pXor (linearMapEval m z) (mapEval m (zeroPoint k)) = mapEval m z :=
  pXor_twice (mapEval m z) (mapEval m (zeroPoint k))

private theorem xor_cancel_constant :
    ∀ a b c : Bool,
      Bool.xor (Bool.xor (Bool.xor a b) c) c =
        Bool.xor (Bool.xor a c) (Bool.xor b c) := by
  decide

theorem linearMapEval_xor {n k : Nat} (m : AffineMap n k) (x y : Point k) :
    linearMapEval m (pXor x y) =
      pXor (linearMapEval m x) (linearMapEval m y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases m with ⟨f, fs⟩
    have head := xor_cancel_constant (aEval f x) (aEval f y)
      (aEval f (zeroPoint k))
    simp only [linearMapEval, mapEval, pXor, aEval_xor, eval_zero_constant] at *
    exact Prod.ext head (ih fs)

def coefficientBits (n k : Nat) : Nat := n * (k + 1)

theorem coefficientBits_bound {n k : Nat} (h : k ≤ n) :
    coefficientBits n k ≤ n * (n + 1) := by
  exact Nat.mul_le_mul_left n (Nat.add_le_add_right h 1)

end PNP.Concrete.ResidualReduction.BinaryLinear
