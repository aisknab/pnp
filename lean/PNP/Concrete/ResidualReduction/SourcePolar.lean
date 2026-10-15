import PNP.Concrete.ResidualReduction.FactoredContraction
import PNP.Concrete.ResidualReduction.ConstrainedBilinear

namespace PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear PNP.Concrete.ResidualReduction.ConstrainedBilinear

def linearEval {n : Nat} (f : Affine n) (x : Point n) : Bool :=
  aEval (homogeneousRow f) x

theorem linearEval_zero {n : Nat} (f : Affine n) :
    linearEval f (zeroPoint n) = false := by
  rw [linearEval, homogeneousRow_eval, eval_zero_constant, Bool.xor_self]

theorem linearEval_additive {n : Nat} (f : Affine n) (x y : Point n) :
    linearEval f (pXor x y) = Bool.xor (linearEval f x) (linearEval f y) := by
  simp only [linearEval, aEval_xor, homogeneousRow_constant, Bool.xor_false]

def polar {n : Nat} (r : Row n) (x y : Point n) : Bool :=
  Bool.xor (linearEval r.left x && linearEval r.right y)
    (linearEval r.right x && linearEval r.left y)

def activity {n : Nat} (r : Row n) (x : Point n) : Bool :=
  Bool.xor (r.eval x) (r.eval (zeroPoint n))

private theorem polarization_identity : ∀ a b c d e f : Bool,
    Bool.xor ((Bool.xor (Bool.xor a b) e) && (Bool.xor (Bool.xor c d) f)) (e && f) =
      Bool.xor (Bool.xor (Bool.xor (a && c) (e && f)) (Bool.xor (b && d) (e && f)))
        (Bool.xor ((Bool.xor a e) && (Bool.xor d f))
          ((Bool.xor c f) && (Bool.xor b e))) := by decide

theorem activity_polarization {n : Nat} (r : Row n) (x y : Point n) :
    activity r (pXor x y) =
      Bool.xor (Bool.xor (activity r x) (activity r y)) (polar r x y) := by
  simp only [activity, Row.eval, aEval_xor, eval_zero_constant, polar,
    linearEval, homogeneousRow_eval]
  exact polarization_identity _ _ _ _ _ _

theorem activity_zero {n : Nat} (r : Row n) :
    activity r (zeroPoint n) = false := by
  simp only [activity, Bool.xor_self]

theorem polar_zero_left {n : Nat} (r : Row n) (y : Point n) :
    polar r (zeroPoint n) y = false := by
  simp only [polar, linearEval_zero, Bool.false_and, Bool.false_xor]

theorem polar_zero_right {n : Nat} (r : Row n) (x : Point n) :
    polar r x (zeroPoint n) = false := by
  simp only [polar, linearEval_zero, Bool.and_false, Bool.false_xor]

private theorem polar_swap : ∀ a b c d : Bool,
    Bool.xor (a && d) (c && b) = Bool.xor (b && c) (d && a) := by decide

theorem polar_comm {n : Nat} (r : Row n) (x y : Point n) :
    polar r x y = polar r y x :=
  polar_swap _ _ _ _

private theorem polar_add : ∀ a b c d e f : Bool,
    Bool.xor (a && Bool.xor b c) (d && Bool.xor e f) =
      Bool.xor (Bool.xor (a && b) (d && e)) (Bool.xor (a && c) (d && f)) := by decide

theorem polar_additive_right {n : Nat} (r : Row n) (x y z : Point n) :
    polar r x (pXor y z) = Bool.xor (polar r x y) (polar r x z) := by
  simp only [polar, linearEval_additive]
  exact polar_add _ _ _ _ _ _

theorem polar_additive_left {n : Nat} (r : Row n) (x y z : Point n) :
    polar r (pXor x y) z = Bool.xor (polar r x z) (polar r y z) := by
  rw [polar_comm r (pXor x y) z, polar_additive_right,
    polar_comm r z x, polar_comm r z y]

/-- Coefficients of the source polar, with the second argument fixed. -/
def polarForm {n : Nat} (r : Row n) (z : Point n) : Affine n :=
  aAdd (aScale (linearEval r.right z) (homogeneousRow r.left))
    (aScale (linearEval r.left z) (homogeneousRow r.right))

theorem polarForm_eval {n : Nat} (r : Row n) (z x : Point n) :
    aEval (polarForm r z) x = polar r x z := by
  simp only [polarForm, aAdd_eval, aScale_eval, polar, linearEval, Bool.and_comm]

theorem polarForm_constant {n : Nat} (r : Row n) (z : Point n) :
    aConstant (polarForm r z) = false := by
  rw [← eval_zero_constant, polarForm_eval, polar_zero_left]

theorem homogeneous_polarForm_eval {n : Nat} (r : Row n) (z x : Point n) :
    aEval (homogeneousRow (polarForm r z)) x = polar r x z := by
  rw [homogeneousRow_eval, polarForm_eval, polarForm_constant, Bool.xor_false]

end PNP.Concrete.ResidualReduction.SourceDirections
