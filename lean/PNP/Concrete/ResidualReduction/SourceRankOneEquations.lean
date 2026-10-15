import PNP.Concrete.ResidualReduction.SourceLinearCoordinates

namespace PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections

def weightedPolar {n : Nat} :
    (F : Family n) → Point F.length → Point n → Point n → Bool
  | [], _, _, _ => false
  | r :: F, (b, bs), x, y => Bool.xor (b && polar r x y) (weightedPolar F bs x y)

theorem weightedPolar_zero_weights {n : Nat} (F : Family n) (x y : Point n) :
    weightedPolar F (zeroPoint F.length) x y = false := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    simp only [List.length_cons, zeroPoint, weightedPolar, Bool.false_and, Bool.false_xor, ih]

theorem weightedPolar_additive_weights {n : Nat} (F : Family n)
    (u v : Point F.length) (x y : Point n) :
    weightedPolar F (pXor u v) x y =
      Bool.xor (weightedPolar F u x y) (weightedPolar F v x y) := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases u with ⟨a, u⟩
    rcases v with ⟨b, v⟩
    simp only [weightedPolar, pXor, xor_and, ih]
    exact xor_interchange _ _ _ _

theorem weightedPolar_zero_left {n : Nat} (F : Family n)
    (w : Point F.length) (y : Point n) :
    weightedPolar F w (zeroPoint n) y = false := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [weightedPolar, polar_zero_left, Bool.and_false, Bool.false_xor, ih]

theorem weightedPolar_zero_right {n : Nat} (F : Family n)
    (w : Point F.length) (x : Point n) :
    weightedPolar F w x (zeroPoint n) = false := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [weightedPolar, polar_zero_right, Bool.and_false, Bool.false_xor, ih]

theorem weightedPolar_additive_left {n : Nat} (F : Family n)
    (w : Point F.length) (x y z : Point n) :
    weightedPolar F w (pXor x y) z =
      Bool.xor (weightedPolar F w x z) (weightedPolar F w y z) := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [weightedPolar, polar_additive_left, and_xor, ih]
    exact xor_interchange _ _ _ _

theorem weightedPolar_additive_right {n : Nat} (F : Family n)
    (w : Point F.length) (x y z : Point n) :
    weightedPolar F w x (pXor y z) =
      Bool.xor (weightedPolar F w x y) (weightedPolar F w x z) := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    simp only [weightedPolar, polar_additive_right, and_xor, ih]
    exact xor_interchange _ _ _ _

def wedge {n : Nat} (alpha : Affine n) (beta x y : Point n) : Bool :=
  Bool.xor (linearEval alpha x && pointDot beta y)
    (pointDot beta x && linearEval alpha y)

theorem wedge_zero_beta {n : Nat} (alpha : Affine n) (x y : Point n) :
    wedge alpha (zeroPoint n) x y = false := by
  simp only [wedge, pointDot_zero_left, Bool.and_false, Bool.false_and, Bool.false_xor]

theorem wedge_additive_beta {n : Nat} (alpha : Affine n) (a b x y : Point n) :
    wedge alpha (pXor a b) x y =
      Bool.xor (wedge alpha a x y) (wedge alpha b x y) := by
  simp only [wedge, pointDot_additive_left, and_xor, xor_and]
  exact xor_interchange _ _ _ _

theorem wedge_zero_left {n : Nat} (alpha : Affine n) (beta y : Point n) :
    wedge alpha beta (zeroPoint n) y = false := by
  simp only [wedge, linearEval_zero, pointDot_zero_right,
    Bool.false_and, Bool.false_xor]

theorem wedge_zero_right {n : Nat} (alpha : Affine n) (beta x : Point n) :
    wedge alpha beta x (zeroPoint n) = false := by
  simp only [wedge, linearEval_zero, pointDot_zero_right,
    Bool.and_false, Bool.false_xor]

theorem wedge_additive_left {n : Nat} (alpha : Affine n) (beta x y z : Point n) :
    wedge alpha beta (pXor x y) z =
      Bool.xor (wedge alpha beta x z) (wedge alpha beta y z) := by
  simp only [wedge, linearEval_additive, pointDot_additive_right, xor_and]
  exact xor_interchange _ _ _ _

theorem wedge_additive_right {n : Nat} (alpha : Affine n) (beta x y z : Point n) :
    wedge alpha beta x (pXor y z) =
      Bool.xor (wedge alpha beta x y) (wedge alpha beta x z) := by
  simp only [wedge, linearEval_additive, pointDot_additive_right, and_xor]
  exact xor_interchange _ _ _ _

def polarDifference {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (x y : Point n) : Bool :=
  Bool.xor (weightedPolar F (splitPoint F.length w).1 x y)
    (wedge alpha (splitPoint F.length w).2 x y)

theorem polarDifference_zero_weights {n : Nat} (F : Family n) (alpha : Affine n)
    (x y : Point n) : polarDifference F alpha (zeroPoint (n + F.length)) x y = false := by
  simp only [polarDifference, split_zero, weightedPolar_zero_weights,
    wedge_zero_beta, Bool.false_xor]

theorem polarDifference_additive_weights {n : Nat} (F : Family n) (alpha : Affine n)
    (a b : Point (n + F.length)) (x y : Point n) :
    polarDifference F alpha (pXor a b) x y =
      Bool.xor (polarDifference F alpha a x y) (polarDifference F alpha b x y) := by
  simp only [polarDifference, split_xor, weightedPolar_additive_weights, wedge_additive_beta]
  exact xor_interchange _ _ _ _

theorem polarDifference_zero_left {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (y : Point n) :
    polarDifference F alpha w (zeroPoint n) y = false := by
  simp only [polarDifference, weightedPolar_zero_left, wedge_zero_left, Bool.false_xor]

theorem polarDifference_zero_right {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (x : Point n) :
    polarDifference F alpha w x (zeroPoint n) = false := by
  simp only [polarDifference, weightedPolar_zero_right, wedge_zero_right, Bool.false_xor]

theorem polarDifference_additive_left {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (x y z : Point n) :
    polarDifference F alpha w (pXor x y) z =
      Bool.xor (polarDifference F alpha w x z) (polarDifference F alpha w y z) := by
  simp only [polarDifference, weightedPolar_additive_left, wedge_additive_left]
  exact xor_interchange _ _ _ _

theorem polarDifference_additive_right {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (x y z : Point n) :
    polarDifference F alpha w x (pXor y z) =
      Bool.xor (polarDifference F alpha w x y) (polarDifference F alpha w x z) := by
  simp only [polarDifference, weightedPolar_additive_right, wedge_additive_right]
  exact xor_interchange _ _ _ _

def polarConstraint {n : Nat} (F : Family n) (alpha : Affine n)
    (x y : Point n) : Affine (n + F.length) :=
  linearForm (fun w => polarDifference F alpha w x y)

theorem polarConstraint_eval {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (x y : Point n) :
    aEval (homogeneousRow (polarConstraint F alpha x y)) w =
      polarDifference F alpha w x y := by
  rw [polarConstraint, homogeneousRow_eval, linearForm_constant, Bool.xor_false]
  exact linearForm_eval _ (polarDifference_zero_weights F alpha x y)
    (fun a b => polarDifference_additive_weights F alpha a b x y) w

/-- All source-derived unit-pair equations; no supplied equation table. -/
def rankOneRows {n : Nat} (F : Family n) (alpha : Affine n) : System (n + F.length) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => polarConstraint F alpha (unitPoint n i) (unitPoint n j)

theorem rankOneRows_units {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) :
    satisfies (homogeneous (rankOneRows F alpha)) w = true ↔
      ∀ i j, polarDifference F alpha w (unitPoint n i) (unitPoint n j) = false := by
  constructor
  · intro h i j
    have hm : homogeneousRow (polarConstraint F alpha (unitPoint n i) (unitPoint n j)) ∈
        homogeneous (rankOneRows F alpha) :=
      List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
        ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩, rfl⟩
    have hh := (satisfies_iff _ _).mp h _ hm
    rw [polarConstraint_eval] at hh
    exact hh
  · intro h
    apply (satisfies_iff _ _).mpr
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    obtain ⟨i, _, hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
    rw [polarConstraint_eval]
    exact h i j

/-- The finite coefficient equations represent the full original-source
    bilinear identity, not just its values on fixed sample inputs. -/
theorem rankOneRows_iff {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) :
    satisfies (homogeneous (rankOneRows F alpha)) w = true ↔
      ∀ x y, weightedPolar F (splitPoint F.length w).1 x y =
        wedge alpha (splitPoint F.length w).2 x y := by
  rw [rankOneRows_units]
  constructor
  · intro h x y
    apply (xor_false_iff _ _).mp
    change polarDifference F alpha w x y = false
    apply additive_units_zero (fun z => polarDifference F alpha w z y)
      (polarDifference_zero_left F alpha w y)
      (fun a b => polarDifference_additive_left F alpha w a b y) _ x
    intro i
    exact additive_units_zero (polarDifference F alpha w (unitPoint n i))
      (polarDifference_zero_right F alpha w _)
      (polarDifference_additive_right F alpha w _) (h i) y
  · intro h i j
    exact (xor_false_iff _ _).mpr (h (unitPoint n i) (unitPoint n j))

theorem rankOneRows_length {n : Nat} (F : Family n) (alpha : Affine n) :
    (rankOneRows F alpha).length = n * n := by
  have aux : ∀ is : List (Fin n),
      (is.flatMap (fun i => (List.finRange n).map (fun j =>
        polarConstraint F alpha (unitPoint n i) (unitPoint n j)))).length = is.length * n := by
    intro is
    induction is with
    | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
    | cons i is ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_finRange, List.length_cons]
      rw [ih, Nat.succ_mul, Nat.add_comm]
  simpa only [rankOneRows, List.length_finRange] using aux (List.finRange n)

end PNP.Concrete.ResidualReduction.SourceLine
