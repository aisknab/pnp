import PNP.Concrete.ResidualReduction.SourceRankOneEquations

namespace PNP.Concrete.ResidualReduction.SourcePlane
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections PNP.Concrete.ResidualReduction.SourceLine

def fixedWedge {n : Nat} (alpha beta : Affine n) (x y : Point n) : Bool :=
  Bool.xor (linearEval alpha x && linearEval beta y)
    (linearEval beta x && linearEval alpha y)

theorem fixedWedge_zero_left {n : Nat} (alpha beta : Affine n) (y : Point n) :
    fixedWedge alpha beta (zeroPoint n) y = false := by
  simp only [fixedWedge, linearEval_zero, Bool.false_and, Bool.false_xor]

theorem fixedWedge_zero_right {n : Nat} (alpha beta : Affine n) (x : Point n) :
    fixedWedge alpha beta x (zeroPoint n) = false := by
  simp only [fixedWedge, linearEval_zero, Bool.and_false, Bool.false_xor]

theorem fixedWedge_additive_left {n : Nat} (alpha beta : Affine n) (x y z : Point n) :
    fixedWedge alpha beta (pXor x y) z =
      Bool.xor (fixedWedge alpha beta x z) (fixedWedge alpha beta y z) := by
  simp only [fixedWedge, linearEval_additive, xor_and]
  exact xor_interchange _ _ _ _

theorem fixedWedge_additive_right {n : Nat} (alpha beta : Affine n) (x y z : Point n) :
    fixedWedge alpha beta x (pXor y z) =
      Bool.xor (fixedWedge alpha beta x y) (fixedWedge alpha beta x z) := by
  simp only [fixedWedge, linearEval_additive, and_xor]
  exact xor_interchange _ _ _ _

def planeDifference {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length) (x y : Point n) : Bool :=
  Bool.xor (weightedPolar F w x y) (fixedWedge alpha beta x y)

theorem planeDifference_zero_left {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length) (y : Point n) :
    planeDifference F alpha beta w (zeroPoint n) y = false := by
  simp only [planeDifference, weightedPolar_zero_left, fixedWedge_zero_left, Bool.false_xor]

theorem planeDifference_zero_right {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length) (x : Point n) :
    planeDifference F alpha beta w x (zeroPoint n) = false := by
  simp only [planeDifference, weightedPolar_zero_right, fixedWedge_zero_right, Bool.false_xor]

theorem planeDifference_additive_left {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length) (x y z : Point n) :
    planeDifference F alpha beta w (pXor x y) z =
      Bool.xor (planeDifference F alpha beta w x z) (planeDifference F alpha beta w y z) := by
  simp only [planeDifference, weightedPolar_additive_left, fixedWedge_additive_left]
  exact xor_interchange _ _ _ _

theorem planeDifference_additive_right {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length) (x y z : Point n) :
    planeDifference F alpha beta w x (pXor y z) =
      Bool.xor (planeDifference F alpha beta w x y) (planeDifference F alpha beta w x z) := by
  simp only [planeDifference, weightedPolar_additive_right, fixedWedge_additive_right]
  exact xor_interchange _ _ _ _

/-- This is affine in the weights: the fixed wedge is the equation's right side. -/
def planeConstraint {n : Nat} (F : Family n) (alpha beta : Affine n)
    (x y : Point n) : Affine F.length :=
  aAdd (linearForm (fun w => weightedPolar F w x y))
    (aConst F.length (fixedWedge alpha beta x y))

theorem planeConstraint_eval {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length) (x y : Point n) :
    aEval (planeConstraint F alpha beta x y) w = planeDifference F alpha beta w x y := by
  rw [planeConstraint, aAdd_eval, aConst_eval]
  rw [linearForm_eval _ (weightedPolar_zero_weights F x y)
    (fun a b => weightedPolar_additive_weights F a b x y)]
  rfl

def planeRows {n : Nat} (F : Family n) (alpha beta : Affine n) : System F.length :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => planeConstraint F alpha beta (unitPoint n i) (unitPoint n j)

theorem planeRows_units {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length) :
    satisfies (planeRows F alpha beta) w = true ↔
      ∀ i j, planeDifference F alpha beta w (unitPoint n i) (unitPoint n j) = false := by
  constructor
  · intro h i j
    have hm : planeConstraint F alpha beta (unitPoint n i) (unitPoint n j) ∈
        planeRows F alpha beta :=
      List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
        List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩
    have hh := (satisfies_iff _ _).mp h _ hm
    rw [planeConstraint_eval] at hh
    exact hh
  · intro h
    apply (satisfies_iff _ _).mpr
    intro f hf
    obtain ⟨i, _, hg⟩ := List.mem_flatMap.mp hf
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
    rw [planeConstraint_eval]
    exact h i j

/-- Exact original-source polar identity for every x,y, not finite sampling. -/
theorem planeRows_iff {n : Nat} (F : Family n) (alpha beta : Affine n)
    (w : Point F.length) :
    satisfies (planeRows F alpha beta) w = true ↔
      ∀ x y, weightedPolar F w x y = fixedWedge alpha beta x y := by
  rw [planeRows_units]
  constructor
  · intro h x y
    apply (xor_false_iff _ _).mp
    change planeDifference F alpha beta w x y = false
    apply additive_units_zero (fun z => planeDifference F alpha beta w z y)
      (planeDifference_zero_left F alpha beta w y)
      (fun a b => planeDifference_additive_left F alpha beta w a b y) _ x
    intro i
    exact additive_units_zero (planeDifference F alpha beta w (unitPoint n i))
      (planeDifference_zero_right F alpha beta w _)
      (planeDifference_additive_right F alpha beta w _) (h i) y
  · intro h i j
    exact (xor_false_iff _ _).mpr (h (unitPoint n i) (unitPoint n j))

theorem planeRows_length {n : Nat} (F : Family n) (alpha beta : Affine n) :
    (planeRows F alpha beta).length = n * n := by
  have aux : ∀ is : List (Fin n),
      (is.flatMap (fun i => (List.finRange n).map (fun j =>
        planeConstraint F alpha beta (unitPoint n i) (unitPoint n j)))).length = is.length * n := by
    intro is
    induction is with
    | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
    | cons i is ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_finRange, List.length_cons]
      rw [ih, Nat.succ_mul, Nat.add_comm]
  simpa only [planeRows, List.length_finRange] using aux (List.finRange n)

end PNP.Concrete.ResidualReduction.SourcePlane
