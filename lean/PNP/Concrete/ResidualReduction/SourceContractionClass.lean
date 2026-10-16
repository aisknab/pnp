import PNP.Concrete.ResidualReduction.SourceGlobalSelector

set_option autoImplicit false

namespace PNP.Concrete.ResidualReduction.SourceClass
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain

/-- The scalar is the actual XOR of selected source equations. -/
def sourceRetraction {n : Nat} (F : Family n) (w : Point F.length)
    (v x : Point n) : Point n :=
  if weightedValue F w x then pXor x v else x

/-- Translation by the chosen direction toggles the selected source scalar. -/
def Balanced {n : Nat} (F : Family n) (w : Point F.length) (v : Point n) : Prop :=
  weightedActivity F w v = true ∧
    ∀ x, weightedPolar F w x v = false

/-- Full semantic closure: each complete pulled-back source row is quadratic.
    This is not a supplied line, plane, or finite-menu membership certificate. -/
def SemanticContraction {n : Nat} (F : Family n) (w : Point F.length)
    (v : Point n) : Prop :=
  Balanced F w v ∧
    ∀ r ∈ F, ∃ q : Quadratic n, ∀ x,
      qEval q x = r.eval (sourceRetraction F w v x)

/-- The alternating cubic obstruction of a two-form and a one-form. -/
def ExteriorZero {α : Type} (B : α → α → Bool) (a : α → Bool) : Prop :=
  ∀ x y z, Bool.xor (B x y && a z)
    (Bool.xor (B x z && a y) (B y z && a x)) = false

/-- The complete coefficient criterion. Its equivalence with semantic closure
    is a separate proof obligation, not a definitional assumption. -/
def CoefficientContraction {n : Nat} (F : Family n) (w : Point F.length)
    (v : Point n) : Prop :=
  Balanced F w v ∧
    ∀ r ∈ F, ExteriorZero (weightedPolar F w) (polar r v)

theorem polar_diagonal {n : Nat} (r : Row n) (x : Point n) :
    polar r x x = false := by
  simp only [polar, Bool.and_comm, Bool.xor_self]

theorem weightedPolar_comm {n : Nat} (F : Family n) (w : Point F.length)
    (x y : Point n) : weightedPolar F w x y = weightedPolar F w y x := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b,w⟩
    simp only [weightedPolar, polar_comm r x y, ih]

theorem weightedPolar_diagonal {n : Nat} (F : Family n) (w : Point F.length)
    (x : Point n) : weightedPolar F w x x = false := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b,w⟩
    simp only [weightedPolar, polar_diagonal, Bool.and_false, Bool.false_xor, ih]

private theorem exterior_factor_bool : ∀ value bp cp ay ax : Bool,
    Bool.xor value (Bool.xor (bp && ay) (cp && ax)) = false →
      value = Bool.xor (ax && cp) (bp && ay) := by decide

/-- A single nonzero annihilating one-form forces a decomposable two-form.
    The chosen point is a witness to that one-form, not a source model. -/
theorem exterior_factor {α : Type} (B : α → α → Bool) (a : α → Bool)
    (h : ExteriorZero B a) (p : α) (hp : a p = true) (x y : α) :
    B x y = Bool.xor (a x && B y p) (B x p && a y) := by
  have he := h x y p
  simp only [hp, Bool.and_true] at he
  exact exterior_factor_bool _ _ _ _ _ he

private theorem exterior_span_bool : ∀ ax ay az bx byv bz c d : Bool,
    Bool.xor
      (Bool.xor (ax && byv) (bx && ay) && Bool.xor (c && az) (d && bz))
      (Bool.xor
        (Bool.xor (ax && bz) (bx && az) && Bool.xor (c && ay) (d && byv))
        (Bool.xor (ay && bz) (byv && az) && Bool.xor (c && ax) (d && bx))) = false := by
  decide

theorem exterior_of_span {α : Type} (a b h : α → Bool) (c d : Bool)
    (hh : ∀ x, h x = Bool.xor (c && a x) (d && b x)) :
    ExteriorZero (fun x y => Bool.xor (a x && b y) (b x && a y)) h := by
  intro x y z
  rw [hh x, hh y, hh z]
  exact exterior_span_bool _ _ _ _ _ _ _ _

theorem polarForm_homogeneous {n : Nat} (r : Row n) (v : Point n) :
    homogeneousRow (polarForm r v) = polarForm r v := by
  apply affine_eval_ext
  intro x
  rw [homogeneousRow_eval, polarForm_constant, Bool.xor_false]

theorem polarForm_linearEval {n : Nat} (r : Row n) (v x : Point n) :
    linearEval (polarForm r v) x = polar r v x := by
  rw [linearEval, polarForm_homogeneous, polarForm_eval, polar_comm]

private theorem polarForm_zero_left {n : Nat} (r : Row n) (v : Point n)
    (h : homogeneousRow r.left = aConst n false) :
    polarForm r v = aConst n false := by
  apply affine_eval_ext
  intro x
  simp only [polarForm_eval, polar, linearEval, h, aConst_eval,
    Bool.false_and, Bool.and_false, Bool.false_xor]

private theorem polarForm_zero_right {n : Nat} (r : Row n) (v : Point n)
    (h : homogeneousRow r.right = aConst n false) :
    polarForm r v = aConst n false := by
  apply affine_eval_ext
  intro x
  simp only [polarForm_eval, polar, linearEval, h, aConst_eval,
    Bool.false_and, Bool.and_false, Bool.false_xor]

private theorem polarForm_zero_equal {n : Nat} (r : Row n) (v : Point n)
    (h : homogeneousRow r.left = homogeneousRow r.right) :
    polarForm r v = aConst n false := by
  apply affine_eval_ext
  intro x
  simp only [polarForm_eval, polar, linearEval, h, Bool.xor_self, aConst_eval]

/-- Every nonzero source derivative is one of that row's three exact normals.
    Zero or affine products cannot supply such a derivative. -/
theorem polarForm_mem_rowNormals {n : Nat} (r : Row n) (v : Point n)
    (hn : polarForm r v ≠ aConst n false) :
    polarForm r v ∈ rowNormals r := by
  by_cases ha : aEq (homogeneousRow r.left) (aConst n false) = true
  · exact False.elim (hn (polarForm_zero_left r v ((aEq_true_iff _ _).mp ha)))
  by_cases hb : aEq (homogeneousRow r.right) (aConst n false) = true
  · exact False.elim (hn (polarForm_zero_right r v ((aEq_true_iff _ _).mp hb)))
  by_cases hab : aEq (homogeneousRow r.left) (homogeneousRow r.right) = true
  · exact False.elim (hn (polarForm_zero_equal r v ((aEq_true_iff _ _).mp hab)))
  simp only [rowNormals, ha, hb, hab]
  cases hl : linearEval r.left v with
  | false =>
    cases hr : linearEval r.right v with
    | false =>
      have hz : polarForm r v = aConst n false := by
        apply affine_eval_ext
        intro x
        simp only [polarForm_eval, polar, hl, hr, Bool.and_false,
          Bool.false_xor, aConst_eval]
      exact False.elim (hn hz)
    | true =>
      have he : polarForm r v = homogeneousRow r.left := by
        apply affine_eval_ext
        intro x
        rw [polarForm_eval]
        change polar r x v = linearEval r.left x
        simp only [polar, hl, hr, Bool.and_true,
          Bool.and_false, Bool.xor_false]
      rw [he]
      exact List.mem_cons_self
  | true =>
    cases hr : linearEval r.right v with
    | false =>
      have he : polarForm r v = homogeneousRow r.right := by
        apply affine_eval_ext
        intro x
        rw [polarForm_eval]
        change polar r x v = linearEval r.right x
        simp only [polar, hl, hr, Bool.and_true,
          Bool.and_false, Bool.false_xor]
      rw [he]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    | true =>
      have he : polarForm r v =
          aAdd (homogeneousRow r.left) (homogeneousRow r.right) := by
        apply affine_eval_ext
        intro x
        rw [polarForm_eval, aAdd_eval]
        change polar r x v =
          Bool.xor (linearEval r.left x) (linearEval r.right x)
        simp only [polar, hl, hr, Bool.and_true]
      rw [he]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem polarForm_mem_sourceMenu {n : Nat} (F : Family n) (r : Row n)
    (hr : r ∈ F) (v : Point n) (hn : polarForm r v ≠ aConst n false) :
    polarForm r v ∈ sourceMenu F :=
  (sourceMenu_mem F _).mpr ⟨r,hr,polarForm_mem_rowNormals r v hn⟩


private theorem polar_succ_bool : ∀ ax ay ac qxy qx qy qz b c : Bool,
    Bool.xor
      (Bool.xor
        (Bool.xor (Bool.xor (Bool.xor ax ay) ac && Bool.xor b c) qxy)
        (Bool.xor (ax && b) qx))
      (Bool.xor (Bool.xor (ay && c) qy) qz) =
    Bool.xor (Bool.xor ax ac && c)
      (Bool.xor (Bool.xor ay ac && b)
        (Bool.xor (Bool.xor qxy qx) (Bool.xor qy qz))) := by decide

theorem qPolar_succ {n : Nat} (a : Affine n) (q : Quadratic n)
    (b c : Bool) (x y : Point n) :
    qPolar (n := n+1) (a,q) (b,x) (c,y) =
      Bool.xor (linearEval a x && c)
        (Bool.xor (linearEval a y && b) (qPolar q x y)) := by
  simp only [qPolar, qEval, pXor, zeroPoint, Bool.and_false, Bool.false_xor,
    aEval_xor, linearEval, homogeneousRow_eval, eval_zero_constant]
  exact polar_succ_bool _ _ _ _ _ _ _ _ _

theorem qPolar_additive_left {n : Nat} (q : Quadratic n) (x y z : Point n) :
    qPolar q (pXor x y) z = Bool.xor (qPolar q x z) (qPolar q y z) := by
  induction n with
  | zero =>
    cases x; cases y; cases z
    simp only [qPolar, qEval, Bool.xor_self]
  | succ n ih =>
    rcases q with ⟨a,q⟩
    rcases x with ⟨b,x⟩
    rcases y with ⟨c,y⟩
    rcases z with ⟨d,z⟩
    simp only [pXor, qPolar_succ, linearEval_additive, xor_and, and_xor, ih,
      Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

def functionPolar {n : Nat} (f : Point n → Bool) (x y : Point n) : Bool :=
  Bool.xor (Bool.xor (f (pXor x y)) (f x))
    (Bool.xor (f y) (f (zeroPoint n)))

/-- The third difference at zero, grouped as a failure of polar additivity. -/
def thirdDifference {n : Nat} (f : Point n → Bool) (x y z : Point n) : Bool :=
  Bool.xor (functionPolar f (pXor x y) z)
    (Bool.xor (functionPolar f x z) (functionPolar f y z))

theorem thirdDifference_qEval {n : Nat} (q : Quadratic n) (x y z : Point n) :
    thirdDifference (qEval q) x y z = false := by
  change Bool.xor (qPolar q (pXor x y) z)
    (Bool.xor (qPolar q x z) (qPolar q y z)) = false
  rw [qPolar_additive_left, Bool.xor_self]

theorem weightedValue_activity {n : Nat} (F : Family n)
    (w : Point F.length) (x : Point n) :
    weightedValue F w x =
      Bool.xor (weightedActivity F w x) (weightedValue F w (zeroPoint n)) := by
  rw [weightedActivity_value, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

private theorem product_polar_bool : ∀ ax ay pz b c gx gy : Bool,
    Bool.xor
      (Bool.xor
        (Bool.xor (Bool.xor (Bool.xor ax ay) b) pz &&
          Bool.xor c (Bool.xor gx gy))
        (Bool.xor ax pz && Bool.xor c gx))
      (Bool.xor (Bool.xor ay pz && Bool.xor c gy) (pz && c)) =
    Bool.xor (b && Bool.xor c (Bool.xor gx gy))
      (Bool.xor (ax && gy) (ay && gx)) := by decide

theorem functionPolar_weighted_product {n : Nat} (F : Family n)
    (w : Point F.length) (c : Bool) (g : Point n → Bool)
    (gz : g (zeroPoint n) = false)
    (ga : ∀ x y, g (pXor x y) = Bool.xor (g x) (g y))
    (x y : Point n) :
    functionPolar (fun t => weightedValue F w t && Bool.xor c (g t)) x y =
      Bool.xor (weightedPolar F w x y && Bool.xor c (Bool.xor (g x) (g y)))
        (Bool.xor (weightedActivity F w x && g y)
          (weightedActivity F w y && g x)) := by
  simp only [functionPolar]
  rw [weightedValue_activity F w (pXor x y), weightedValue_activity F w x,
    weightedValue_activity F w y]
  rw [weightedActivity_polarization, ga, gz, Bool.xor_false]
  exact product_polar_bool _ _ _ _ _ _ _

private theorem product_third_bool : ∀ ax ay az bxy bxz byz c gx gy gz : Bool,
    Bool.xor
      (Bool.xor
        (Bool.xor bxz byz && Bool.xor c (Bool.xor (Bool.xor gx gy) gz))
        (Bool.xor (Bool.xor (Bool.xor ax ay) bxy && gz)
          (az && Bool.xor gx gy)))
      (Bool.xor
        (Bool.xor (bxz && Bool.xor c (Bool.xor gx gz))
          (Bool.xor (ax && gz) (az && gx)))
        (Bool.xor (byz && Bool.xor c (Bool.xor gy gz))
          (Bool.xor (ay && gz) (az && gy)))) =
      Bool.xor (bxy && gz) (Bool.xor (bxz && gy) (byz && gx)) := by
  decide

theorem thirdDifference_weighted_product {n : Nat} (F : Family n)
    (w : Point F.length) (c : Bool) (g : Point n → Bool)
    (gz : g (zeroPoint n) = false)
    (ga : ∀ x y, g (pXor x y) = Bool.xor (g x) (g y))
    (x y z : Point n) :
    thirdDifference (fun t => weightedValue F w t && Bool.xor c (g t)) x y z =
      Bool.xor (weightedPolar F w x y && g z)
        (Bool.xor (weightedPolar F w x z && g y)
          (weightedPolar F w y z && g x)) := by
  simp only [thirdDifference, functionPolar_weighted_product F w c g gz ga,
    weightedPolar_additive_left, weightedActivity_polarization, ga]
  exact product_third_bool _ _ _ _ _ _ _ _ _ _

private theorem derivative_recover : ∀ a b c : Bool,
    Bool.xor a b = c → a = Bool.xor b c := by decide

private theorem xor_remove_middle : ∀ a b : Bool,
    Bool.xor (Bool.xor a b) a = b := by decide

theorem sourceRetraction_eval {n : Nat} (F : Family n) (w : Point F.length)
    (v : Point n) (r : Row n) (x : Point n) :
    r.eval (sourceRetraction F w v x) =
      Bool.xor (r.eval x)
        (weightedValue F w x && Bool.xor (activity r v) (polar r v x)) := by
  cases hp : weightedValue F w x with
  | false =>
    simp only [sourceRetraction, hp, Bool.false_eq_true, ↓reduceIte,
      Bool.false_and, Bool.xor_false]
  | true =>
    simp only [sourceRetraction, hp, ↓reduceIte, Bool.true_and]
    exact derivative_recover _ _ _ (by
      rw [row_derivative, polar_comm])

/-- Semantic degree preservation implies the complete cubic obstruction vanishes.
    This direction does not assume a menu witness, supplied coverage, or a bound
    on the ambient dimension. All affine constants are retained. -/
theorem semantic_implies_coefficient {n : Nat} (F : Family n)
    (w : Point F.length) (v : Point n) (h : SemanticContraction F w v) :
    CoefficientContraction F w v := by
  refine ⟨h.1, ?_⟩
  intro r hr
  obtain ⟨q,hq⟩ := h.2 r hr
  let residual := qAdd q (qProduct r.left r.right)
  have he : qEval residual =
      (fun x => weightedValue F w x && Bool.xor (activity r v) (polar r v x)) := by
    funext x
    simp only [residual, qAdd_eval, qProduct_eval, hq]
    change Bool.xor (r.eval (sourceRetraction F w v x)) (r.eval x) =
      (weightedValue F w x && Bool.xor (activity r v) (polar r v x))
    rw [sourceRetraction_eval, xor_remove_middle]
  intro x y z
  have hz := thirdDifference_qEval residual x y z
  rw [he, thirdDifference_weighted_product F w (activity r v) (polar r v)
    (polar_zero_right r v) (polar_additive_right r v)] at hz
  exact hz

end PNP.Concrete.ResidualReduction.SourceClass
