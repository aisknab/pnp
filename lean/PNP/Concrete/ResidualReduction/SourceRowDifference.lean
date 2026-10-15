import PNP.Concrete.ResidualReduction.SourceScalarTail

namespace PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane PNP.Concrete.ResidualReduction.SourceBalance

def rowDifference {n : Nat} (r : Row (n + 1)) : Affine n :=
  match r.left.1, r.right.1 with
  | false, false => aConst n false
  | false, true => r.left.2
  | true, false => r.right.2
  | true, true => aAdd (aAdd r.left.2 r.right.2) (aConst n true)

theorem rowDifference_eval {n : Nat} (r : Row (n + 1)) (z : Point n) :
    aEval (rowDifference r) z = Bool.xor (r.eval (true,z)) (r.eval (false,z)) := by
  rcases r with ⟨s, ⟨dl,f⟩, ⟨dr,g⟩⟩
  cases dl <;> cases dr <;>
    simp only [rowDifference, Row.eval, aEval, aAdd_eval, aConst_eval,
      Bool.and_true, Bool.and_false, Bool.false_xor] <;>
    cases h1 : aEval f z <;> cases h2 : aEval g z <;> decide

theorem chart_row_difference {n : Nat} (r : Row (n + 1)) (v : Point (n + 1))
    (c : Fin (n + 1) × Point n) (hc : chooseChart v = some c) (z : Point n) :
    aEval (rowDifference ((r.cut c.1).shear c.2)) z =
      Bool.xor (activity r v) (polar r (basePoint c.1 z) v) := by
  rw [rowDifference_eval, Row.shear_eval, Row.cut_eval, Row.shear_eval, Row.cut_eval]
  change Bool.xor (r.eval (unchart c.1 c.2 (true,z)))
    (r.eval (unchart c.1 c.2 (false,z))) = _
  rw [unchart_flip, chooseChart_sound v c hc]
  exact row_derivative r (basePoint c.1 z) v

theorem polar_self {n : Nat} (r : Row n) (v : Point n) : polar r v v = false := by
  simp only [polar, Bool.and_comm, Bool.xor_self]

theorem chart_row_one_derivative {n : Nat} (r : Row (n + 1)) (v : Point (n + 1))
    (c : Fin (n + 1) × Point n) (hc : chooseChart v = some c)
    (hd : rowDifference ((r.cut c.1).shear c.2) = aConst n true) (x : Point (n+1)) :
    Bool.xor (r.eval (pXor x v)) (r.eval x) = true := by
  have hall : ∀ z, Bool.xor (activity r v) (polar r (basePoint c.1 z) v) = true := by
    intro z
    rw [← chart_row_difference r v c hc z, hd, aConst_eval]
  rw [row_derivative]
  have hx : x = unchart c.1 c.2 (chart c.1 c.2 x) :=
    (unchart_chart c.1 c.2 x).symm
  generalize hy : chart c.1 c.2 x = y at hx
  rcases y with ⟨b,z⟩
  cases b with
  | false =>
    rw [hx]
    exact hall z
  | true =>
    rw [hx, unchart_flip, chooseChart_sound v c hc, polar_additive_left, polar_self,
      Bool.xor_false]
    exact hall z

theorem affine_translation {n : Nat} (f : Affine n) (x v : Point n) :
    aEval f (pXor x v) = Bool.xor (aEval f x) (linearEval f v) := by
  rw [aEval_xor, linearEval, homogeneousRow_eval, Bool.xor_assoc]

private theorem product_difference : ∀ a b l r : Bool,
    Bool.xor ((Bool.xor l a) && (Bool.xor r b)) (l && r) =
      Bool.xor (Bool.xor (a && r) (b && l)) (a && b) := by decide

theorem row_derivative_expansion {n : Nat} (r : Row n) (v x : Point n) :
    Bool.xor (r.eval (pXor x v)) (r.eval x) =
      Bool.xor (Bool.xor (linearEval r.left v && aEval r.right x)
        (linearEval r.right v && aEval r.left x))
        (linearEval r.left v && linearEval r.right v) := by
  simp only [Row.eval, affine_translation]
  exact product_difference _ _ _ _

private theorem constant_difference_polar : ∀ a b l r s t u v : Bool,
    Bool.xor (Bool.xor (a && r) (b && l)) (a && b) = true →
    Bool.xor (Bool.xor (a && t) (b && s)) (a && b) = true →
    Bool.xor (Bool.xor (a && v) (b && u)) (a && b) = true →
    Bool.xor ((Bool.xor l u) && (Bool.xor t v))
      ((Bool.xor r v) && (Bool.xor s u)) = false := by decide

theorem product_unit_derivative_affine {n : Nat} (r : Row n) (v : Point n)
    (h : ∀ x, Bool.xor (r.eval (pXor x v)) (r.eval x) = true) :
    ∀ x y, polar r x y = false := by
  intro x y
  have hx := h x
  have hy := h y
  have hz := h (zeroPoint n)
  rw [row_derivative_expansion] at hx hy hz
  simp only [polar, linearEval, homogeneousRow_eval, ← eval_zero_constant]
  exact constant_difference_polar _ _ _ _ _ _ _ _ hx hy hz

theorem source_chart_difference_ne_one {n : Nat} (F : Family (n+1))
    (hn : sourceAffineQuery F = none) (r : Row (n+1)) (hr : r ∈ F)
    (v : Point (n+1)) (c : Fin (n+1) × Point n) (hc : chooseChart v = some c) :
    rowDifference ((r.cut c.1).shear c.2) ≠ aConst n true := by
  intro hd
  have hall := chart_row_one_derivative r v c hc hd
  have hp := product_unit_derivative_affine r v hall
  have hf := sourceAffineQuery_none_row_activity F hn r hr hp v
  have ht := hall (zeroPoint (n+1))
  rw [point_zero_xor] at ht
  change activity r v = true at ht
  rw [hf] at ht
  cases ht

theorem source_two_normal_span {n : Nat} (r : Row n) (v : Point n) (a b : Affine n)
    (h : ∀ x, linearEval a x = false → linearEval b x = false → polar r v x = false) :
    ∃ c d : Bool, ∀ x, polar r v x =
      Bool.xor (c && linearEval a x) (d && linearEval b x) :=
  two_annihilator_span (linearEval a) (linearEval b) (polar r v)
    (linearEval_zero a) (linearEval_zero b) (linearEval_additive a)
    (linearEval_additive b) (polar_additive_right r v) h

theorem chart_difference_span {n : Nat} (r : Row (n+1)) (v : Point (n+1))
    (a b : Affine (n+1)) (c : Fin (n+1) × Point n) (hc : chooseChart v = some c)
    (h : ∀ x, linearEval a x = false → linearEval b x = false → polar r v x = false) :
    ∃ l m : Bool, ∀ z, aEval (rowDifference ((r.cut c.1).shear c.2)) z =
      Bool.xor (Bool.xor (l && aEval (tailNormal c.1 a) z)
        (m && aEval (tailNormal c.1 b) z)) (activity r v) := by
  obtain ⟨l,m,hm⟩ := source_two_normal_span r v a b h
  refine ⟨l,m,fun z => ?_⟩
  rw [chart_row_difference r v c hc, polar_comm, hm, tailNormal_eval, tailNormal_eval,
    Bool.xor_comm (activity r v)]

end PNP.Concrete.ResidualReduction.SourceClosure
