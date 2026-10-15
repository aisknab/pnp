import PNP.Concrete.ResidualReduction.SourceRankOneEquations

namespace PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear PNP.Concrete.ResidualReduction.SourceDirections

def queryNormal {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (z : Point (directionSpace F [alpha]).parameters) : Bool :=
  pointDot (splitPoint F.length w).2 ((directionSpace F [alpha]).direction z)

theorem queryNormal_zero_left {n : Nat} (F : Family n) (alpha : Affine n)
    (z : Point (directionSpace F [alpha]).parameters) :
    queryNormal F alpha (zeroPoint (n + F.length)) z = false := by
  simp only [queryNormal, split_zero, pointDot_zero_left]

theorem queryNormal_zero_right {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) :
    queryNormal F alpha w (zeroPoint (directionSpace F [alpha]).parameters) = false := by
  simp only [queryNormal, direction_zero, pointDot_zero_right]

theorem queryNormal_additive_left {n : Nat} (F : Family n) (alpha : Affine n)
    (a b : Point (n + F.length)) (z : Point (directionSpace F [alpha]).parameters) :
    queryNormal F alpha (pXor a b) z =
      Bool.xor (queryNormal F alpha a z) (queryNormal F alpha b z) := by
  simp only [queryNormal, split_xor, pointDot_additive_left]

theorem queryNormal_additive_right {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (a b : Point (directionSpace F [alpha]).parameters) :
    queryNormal F alpha w (pXor a b) =
      Bool.xor (queryNormal F alpha w a) (queryNormal F alpha w b) := by
  simp only [queryNormal, Space.direction_additive, pointDot_additive_right]

def queryActivity {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (z : Point (directionSpace F [alpha]).parameters) : Bool :=
  weightedActivity F (splitPoint F.length w).1 ((directionSpace F [alpha]).direction z)

theorem queryActivity_eq {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (z : Point (directionSpace F [alpha]).parameters) :
    queryActivity F alpha w z =
      bilinearEval (activityMatrix (directionSpace F [alpha]) F) (splitPoint F.length w).1 z :=
  (computed_activity_matrix_eval F [alpha] (splitPoint F.length w).1 z).symm

theorem queryActivity_zero_left {n : Nat} (F : Family n) (alpha : Affine n)
    (z : Point (directionSpace F [alpha]).parameters) :
    queryActivity F alpha (zeroPoint (n + F.length)) z = false := by
  rw [queryActivity_eq, split_zero, bilinear_zero_left]

theorem queryActivity_zero_right {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) :
    queryActivity F alpha w (zeroPoint (directionSpace F [alpha]).parameters) = false := by
  rw [queryActivity_eq, bilinear_zero_right]

theorem queryActivity_additive_left {n : Nat} (F : Family n) (alpha : Affine n)
    (a b : Point (n + F.length)) (z : Point (directionSpace F [alpha]).parameters) :
    queryActivity F alpha (pXor a b) z =
      Bool.xor (queryActivity F alpha a z) (queryActivity F alpha b z) := by
  simp only [queryActivity_eq, split_xor, bilinear_additive_left]

theorem queryActivity_additive_right {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (a b : Point (directionSpace F [alpha]).parameters) :
    queryActivity F alpha w (pXor a b) =
      Bool.xor (queryActivity F alpha w a) (queryActivity F alpha w b) := by
  simp only [queryActivity_eq, bilinear_additive_right]

def normalQueryMatrix {n : Nat} (F : Family n) (alpha : Affine n) :
    Matrix (n + F.length) (directionSpace F [alpha]).parameters :=
  let d := directionSpace F [alpha]
  bilinearCoefficients (fun w z => pointDot (splitPoint F.length w).2 (d.direction z))

def activityQueryMatrix {n : Nat} (F : Family n) (alpha : Affine n) :
    Matrix (n + F.length) (directionSpace F [alpha]).parameters :=
  let d := directionSpace F [alpha]
  bilinearCoefficients (fun w z => weightedActivity F (splitPoint F.length w).1 (d.direction z))

theorem normalQueryMatrix_eval {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (z : Point (directionSpace F [alpha]).parameters) :
    bilinearEval (normalQueryMatrix F alpha) w z =
      pointDot (splitPoint F.length w).2 ((directionSpace F [alpha]).direction z) :=
  bilinearCoefficients_eval _ (queryNormal_zero_left F alpha)
    (queryNormal_zero_right F alpha) (queryNormal_additive_left F alpha)
    (queryNormal_additive_right F alpha) w z

theorem activityQueryMatrix_eval {n : Nat} (F : Family n) (alpha : Affine n)
    (w : Point (n + F.length)) (z : Point (directionSpace F [alpha]).parameters) :
    bilinearEval (activityQueryMatrix F alpha) w z =
      weightedActivity F (splitPoint F.length w).1 ((directionSpace F [alpha]).direction z) :=
  bilinearCoefficients_eval _ (queryActivity_zero_left F alpha)
    (queryActivity_zero_right F alpha) (queryActivity_additive_left F alpha)
    (queryActivity_additive_right F alpha) w z

/-- Coefficient storage bound only, not a full encoded runtime theorem. -/
theorem queryMatrix_size_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    2 * ((n + F.length) * (directionSpace F [alpha]).parameters) ≤
      2 * ((n + F.length) * n) :=
  Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (n + F.length)
    (kernelSpace_parameter_bound (directionSystem F [alpha])))

end PNP.Concrete.ResidualReduction.SourceLine
