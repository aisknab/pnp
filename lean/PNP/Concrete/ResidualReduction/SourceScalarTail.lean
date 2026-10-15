import PNP.Concrete.ResidualReduction.SourceDualSpan

namespace PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine PNP.Concrete.ResidualReduction.SourcePlane PNP.Concrete.ResidualReduction.SourceBalance

def qPolar {n : Nat} (q : Quadratic n) (x y : Point n) : Bool :=
  Bool.xor (Bool.xor (qEval q (pXor x y)) (qEval q x))
    (Bool.xor (qEval q y) (qEval q (zeroPoint n)))

private theorem derivative_polar : ∀ a b c d p : Bool,
    Bool.xor a b = Bool.xor (Bool.xor c d) p →
      Bool.xor (Bool.xor a b) (Bool.xor c d) = p := by decide

theorem weightedActivity_value {n : Nat} (F : Family n) (w : Point F.length) (x : Point n) :
    weightedActivity F w x =
      Bool.xor (weightedValue F w x) (weightedValue F w (zeroPoint n)) := by
  have h := weightedValue_derivative F w (zeroPoint n) x
  rw [point_zero_xor, weightedPolar_zero_left, Bool.xor_false] at h
  exact h.symm

theorem weightedValue_polar {n : Nat} (F : Family n) (w : Point F.length) (x y : Point n) :
    Bool.xor (Bool.xor (weightedValue F w (pXor x y)) (weightedValue F w x))
      (Bool.xor (weightedValue F w y) (weightedValue F w (zeroPoint n))) =
        weightedPolar F w x y :=
  derivative_polar _ _ _ _ _ (by
    rw [weightedValue_derivative, weightedActivity_value])

theorem qProduct_polar {n : Nat} (a b : Affine n) (x y : Point n) :
    qPolar (qProduct a b) x y = fixedWedge a b x y := by
  have h := row_derivative (⟨false, a, b⟩ : Row n) x y
  simp only [Row.eval, activity, polar] at h
  simp only [qPolar, qProduct_eval, fixedWedge]
  exact derivative_polar _ _ _ _ _ h

private theorem xor_four_add : ∀ a b c d e f g h : Bool,
    Bool.xor (Bool.xor (Bool.xor a b) (Bool.xor c d))
      (Bool.xor (Bool.xor e f) (Bool.xor g h)) =
    Bool.xor (Bool.xor (Bool.xor a c) (Bool.xor e g))
      (Bool.xor (Bool.xor b d) (Bool.xor f h)) := by decide

theorem qAdd_polar {n : Nat} (q r : Quadratic n) (x y : Point n) :
    qPolar (qAdd q r) x y = Bool.xor (qPolar q x y) (qPolar r x y) := by
  simp only [qPolar, qAdd_eval]
  exact xor_four_add _ _ _ _ _ _ _ _

theorem quadratic_eval_ext {n : Nat} (q r : Quadratic n)
    (h : ∀ x, qEval q x = qEval r x) : q = r := by
  induction n with
  | zero => exact h ()
  | succ n ih =>
    rcases q with ⟨a, q⟩
    rcases r with ⟨b, r⟩
    have ht : q = r := ih q r (fun x => by
      simpa only [qEval, Bool.and_false, Bool.false_xor] using h (false, x))
    have hh : a = b := by
      apply affine_eval_ext
      intro x
      rw [← qHead_derivative (a, q), ← qHead_derivative (b, r)]
      rw [h (true, x), h (false, x)]
    exact Prod.ext hh ht

def affinePart {n : Nat} (q : Quadratic n) : Affine n :=
  aAdd (linearForm (fun x => Bool.xor (qEval q x) (qEval q (zeroPoint n))))
    (aConst n (qEval q (zeroPoint n)))

private theorem zero_polar_add : ∀ a b c d : Bool,
    Bool.xor (Bool.xor a b) (Bool.xor c d) = false →
      Bool.xor a d = Bool.xor (Bool.xor b d) (Bool.xor c d) := by decide

theorem affinePart_eval_of_zero_polar {n : Nat} (q : Quadratic n)
    (h : ∀ x y, qPolar q x y = false) (x : Point n) :
    aEval (affinePart q) x = qEval q x := by
  have hz : Bool.xor (qEval q (zeroPoint n)) (qEval q (zeroPoint n)) = false :=
    Bool.xor_self _
  have ha : ∀ x y, Bool.xor (qEval q (pXor x y)) (qEval q (zeroPoint n)) =
      Bool.xor (Bool.xor (qEval q x) (qEval q (zeroPoint n)))
        (Bool.xor (qEval q y) (qEval q (zeroPoint n))) :=
    fun x y => zero_polar_add _ _ _ _ (h x y)
  rw [affinePart, aAdd_eval, aConst_eval, linearForm_eval _ hz ha,
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem zero_polar_affine_coefficients {n : Nat} (q : Quadratic n)
    (h : ∀ x y, qPolar q x y = false) : q = qOfAffine (affinePart q) := by
  apply quadratic_eval_ext
  intro x
  rw [qOfAffine_eval, affinePart_eval_of_zero_polar q h]

def planeRemainder {n : Nat} (q : Quadratic n) (a b : Affine n) : Affine n :=
  affinePart (qAdd q (qProduct a b))

theorem plane_decomposition {n : Nat} (q : Quadratic n) (a b : Affine n)
    (h : ∀ x y, qPolar q x y = fixedWedge a b x y) :
    q = qAdd (qProduct a b) (qOfAffine (planeRemainder q a b)) := by
  have hz : ∀ x y, qPolar (qAdd q (qProduct a b)) x y = false := by
    intro x y
    rw [qAdd_polar, qProduct_polar, h x y, Bool.xor_self]
  apply quadratic_eval_ext
  intro x
  rw [qAdd_eval, qOfAffine_eval, planeRemainder, affinePart_eval_of_zero_polar _ hz,
    qAdd_eval, Bool.xor_comm (qEval q x), ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

def basePoint {n : Nat} (k : Fin (n + 1)) (z : Point n) : Point (n + 1) :=
  insert n k (false, z)

theorem insert_zero {n : Nat} (k : Fin (n + 1)) :
    insert n k (zeroPoint (n + 1)) = zeroPoint (n + 1) := by
  have h := insert_xor n k (zeroPoint (n+1)) (zeroPoint (n+1))
  rw [point_xor_self, point_xor_self] at h
  exact h

theorem basePoint_zero {n : Nat} (k : Fin (n + 1)) :
    basePoint k (zeroPoint n) = zeroPoint (n + 1) := insert_zero k

theorem basePoint_additive {n : Nat} (k : Fin (n + 1)) (x y : Point n) :
    basePoint k (pXor x y) = pXor (basePoint k x) (basePoint k y) :=
  insert_xor n k (false, x) (false, y)

def tailNormal {n : Nat} (k : Fin (n + 1)) (f : Affine (n + 1)) : Affine n :=
  (cut n k (homogeneousRow f)).2

theorem tailNormal_eval {n : Nat} (k : Fin (n + 1)) (f : Affine (n + 1))
    (z : Point n) : aEval (tailNormal k f) z = linearEval f (basePoint k z) := by
  have h := aEval_cut n k (homogeneousRow f) (basePoint k z)
  unfold basePoint at h
  rw [cut_insert] at h
  simpa only [affine_eval_cons, Bool.and_false, Bool.false_xor, tailNormal, linearEval,
    basePoint] using h

theorem tailNormal_constant {n : Nat} (k : Fin (n + 1)) (f : Affine (n + 1)) :
    aConstant (tailNormal k f) = false := by
  rw [← eval_zero_constant, tailNormal_eval, basePoint_zero, linearEval_zero]

theorem tailNormal_linearEval {n : Nat} (k : Fin (n + 1))
    (f : Affine (n + 1)) (z : Point n) :
    linearEval (tailNormal k f) z = linearEval f (basePoint k z) := by
  rw [linearEval, homogeneousRow_eval, tailNormal_constant, Bool.xor_false, tailNormal_eval]

theorem qEval_tail {n : Nat} (q : Quadratic (n + 1)) (z : Point n) :
    qEval q (false, z) = qEval q.2 z := by
  rcases q with ⟨a, q⟩
  simp only [qEval, Bool.and_false, Bool.false_xor]

theorem source_tail_eval {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (t z : Point n) :
    qEval (scalar (chartRows (markSource F w) k t)).2 z =
      weightedValue F w (basePoint k z) := by
  have h := scalar_chart_eval (markSource F w) k t (false, z)
  rw [markSource_scalar_eval, qEval_tail] at h
  simpa only [unchart, shear, Bool.false_eq_true, ↓reduceIte, basePoint] using h

theorem source_tail_polar {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (t x y : Point n) :
    qPolar (scalar (chartRows (markSource F w) k t)).2 x y =
      weightedPolar F w (basePoint k x) (basePoint k y) := by
  simp only [qPolar, source_tail_eval, basePoint_zero, basePoint_additive]
  exact weightedValue_polar F w (basePoint k x) (basePoint k y)

theorem source_tail_plane {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (alpha beta : Affine (n + 1)) (k : Fin (n + 1)) (t : Point n)
    (h : ∀ x y, weightedPolar F w x y = fixedWedge alpha beta x y) :
    let q := (scalar (chartRows (markSource F w) k t)).2
    q = qAdd (qProduct (tailNormal k alpha) (tailNormal k beta))
      (qOfAffine (planeRemainder q (tailNormal k alpha) (tailNormal k beta))) := by
  apply plane_decomposition
  intro x y
  rw [source_tail_polar, h]
  simp only [fixedWedge, tailNormal_linearEval]

end PNP.Concrete.ResidualReduction.SourceClosure
