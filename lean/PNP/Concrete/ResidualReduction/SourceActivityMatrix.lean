import PNP.Concrete.ResidualReduction.SourceDirectionSpace

namespace PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear PNP.Concrete.ResidualReduction.ConstrainedBilinear

theorem source_activity_additive {n : Nat} (F : Family n) (U : System n)
    (r : Row n) (hr : r ∈ F)
    (x y : Point (directionSpace F U).parameters) :
    activity r ((directionSpace F U).direction (pXor x y)) =
      Bool.xor (activity r ((directionSpace F U).direction x))
        (activity r ((directionSpace F U).direction y)) := by
  rw [Space.direction_additive, activity_polarization,
    (directionSpace_sound F U x).2 r hr _ (directionSpace_sound F U y).1,
    Bool.xor_false]

def activityCoefficients {n : Nat} (r : Row n) (s : Space n) :
    Fin s.parameters → Bool :=
  fun j => activity r (s.direction (unitPoint _ j))

theorem source_activity_coefficients {n : Nat} (F : Family n) (U : System n)
    (r : Row n) (hr : r ∈ F) (z : Point (directionSpace F U).parameters) :
    rowDot (activityCoefficients r (directionSpace F U)) z =
      activity r ((directionSpace F U).direction z) :=
  additive_coefficient_exact (fun x => activity r ((directionSpace F U).direction x))
    (by rw [direction_zero, activity_zero]) (source_activity_additive F U r hr) z

def weightedActivity {n : Nat} :
    (F : Family n) → Point F.length → Point n → Bool
  | [], _, _ => false
  | r :: F, (b, bs), x =>
    Bool.xor (b && activity r x) (weightedActivity F bs x)

def activityMatrix {n : Nat} (s : Space n) :
    (F : Family n) → Matrix F.length s.parameters
  | [], i => Fin.elim0 i
  | r :: F, i => Fin.cases (activityCoefficients r s) (activityMatrix s F) i

theorem activityMatrix_eval {n : Nat} (F : Family n) (s : Space n)
    (w : Point F.length) (z : Point s.parameters)
    (h : ∀ r ∈ F, rowDot (activityCoefficients r s) z = activity r (s.direction z)) :
    bilinearEval (activityMatrix s F) w z = weightedActivity F w (s.direction z) := by
  induction F with
  | nil => rfl
  | cons r F ih =>
    rcases w with ⟨b, w⟩
    change Bool.xor (b && rowDot (activityCoefficients r s) z)
      (bilinearEval (activityMatrix s F) w z) =
        Bool.xor (b && activity r (s.direction z)) (weightedActivity F w (s.direction z))
    rw [h r List.mem_cons_self, ih w (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- The activity matrix is exactly the weighted original-source activity on
    every computed direction, not merely on basis points or finite examples. -/
theorem computed_activity_matrix_eval {n : Nat} (F : Family n) (U : System n)
    (w : Point F.length) (z : Point (directionSpace F U).parameters) :
    bilinearEval (activityMatrix (directionSpace F U) F) w z =
      weightedActivity F w ((directionSpace F U).direction z) :=
  activityMatrix_eval F (directionSpace F U) w z
    (fun r hr => source_activity_coefficients F U r hr z)

theorem activity_matrix_size_bound {n : Nat} (F : Family n) (U : System n) :
    F.length * (directionSpace F U).parameters ≤ F.length * n :=
  Nat.mul_le_mul_left F.length (kernelSpace_parameter_bound (directionSystem F U))

end PNP.Concrete.ResidualReduction.SourceDirections
