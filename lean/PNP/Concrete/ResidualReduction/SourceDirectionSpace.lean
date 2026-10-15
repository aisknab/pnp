import PNP.Concrete.ResidualReduction.KernelCoefficientMaps

namespace PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear PNP.Concrete.ResidualReduction.ConstrainedBilinear

def polarRows {n : Nat} (F : Family n) (s : Space n) : System n :=
  F.flatMap fun r =>
    (List.finRange s.parameters).map fun j => polarForm r (s.direction (unitPoint _ j))

theorem polarRows_iff {n : Nat} (F : Family n) (s : Space n) (v : Point n) :
    satisfies (homogeneous (polarRows F s)) v = true ↔
      ∀ r ∈ F, ∀ j, polar r v (s.direction (unitPoint _ j)) = false := by
  constructor
  · intro h r hr j
    have hm : homogeneousRow (polarForm r (s.direction (unitPoint _ j))) ∈
        homogeneous (polarRows F s) :=
      List.mem_map.mpr ⟨_, List.mem_flatMap.mpr
        ⟨r, hr, List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩⟩, rfl⟩
    have hh := (satisfies_iff _ _).mp h _ hm
    rw [homogeneous_polarForm_eval] at hh
    exact hh
  · intro h
    apply (satisfies_iff _ _).mpr
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    obtain ⟨r, hr, hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
    rw [homogeneous_polarForm_eval]
    exact h r hr j

theorem satisfies_append {n : Nat} (rs ts : System n) (x : Point n) :
    satisfies (rs ++ ts) x = (satisfies rs x && satisfies ts x) := by
  induction rs with
  | nil => simp only [List.nil_append, satisfies, Bool.true_and]
  | cons r rs ih =>
    simp only [List.cons_append, satisfies, ih, Bool.and_assoc]

def directionSystem {n : Nat} (F : Family n) (U : System n) : System n :=
  U ++ polarRows F (kernelSpace U)

def DirectionSpec {n : Nat} (F : Family n) (U : System n) (v : Point n) : Prop :=
  satisfies (homogeneous U) v = true ∧
    ∀ r ∈ F, ∀ z, satisfies (homogeneous U) z = true → polar r v z = false

theorem directionSystem_iff {n : Nat} (F : Family n) (U : System n) (v : Point n) :
    satisfies (homogeneous (directionSystem F U)) v = true ↔ DirectionSpec F U v := by
  simp only [directionSystem, homogeneous, List.map_append, satisfies_append,
    Bool.and_eq_true]
  change (satisfies (homogeneous U) v = true ∧
    satisfies (homogeneous (polarRows F (kernelSpace U))) v = true) ↔ _
  rw [polarRows_iff]
  constructor
  · rintro ⟨hu, hp⟩
    refine ⟨hu, fun r hr => ?_⟩
    exact (additive_vanish_on_kernel U (polar r v) (polar_zero_right r v)
      (polar_additive_right r v)).mp (hp r hr)
  · rintro ⟨hu, hp⟩
    refine ⟨hu, fun r hr => ?_⟩
    exact (additive_vanish_on_kernel U (polar r v) (polar_zero_right r v)
      (polar_additive_right r v)).mpr (hp r hr)

/-- Both the perpendicular and the admissible direction space are computed
    from the source coefficients. -/
def directionSpace {n : Nat} (F : Family n) (U : System n) : Space n :=
  kernelSpace (directionSystem F U)

theorem directionSpace_iff {n : Nat} (F : Family n) (U : System n) (v : Point n) :
    DirectionSpec F U v ↔ ∃ z, (directionSpace F U).direction z = v :=
  (directionSystem_iff F U v).symm.trans (kernelSpace_iff (directionSystem F U) v)

theorem directionSpace_sound {n : Nat} (F : Family n) (U : System n)
    (z : Point (directionSpace F U).parameters) :
    DirectionSpec F U ((directionSpace F U).direction z) :=
  (directionSpace_iff F U _).mpr ⟨z, rfl⟩

theorem directionSpace_complete {n : Nat} (F : Family n) (U : System n)
    (v : Point n) (h : DirectionSpec F U v) :
    ∃ z, (directionSpace F U).direction z = v :=
  (directionSpace_iff F U v).mp h

theorem polarRows_length {n : Nat} (F : Family n) (s : Space n) :
    (polarRows F s).length = F.length * s.parameters := by
  induction F with
  | nil => simp only [polarRows, List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons r F ih =>
    simp only [polarRows, List.flatMap_cons, List.length_append, List.length_map,
      List.length_finRange, List.length_cons] at *
    rw [ih, Nat.succ_mul, Nat.add_comm]

theorem directionSystem_size_bound {n : Nat} (F : Family n) (U : System n) :
    (directionSystem F U).length ≤ U.length + F.length * n := by
  rw [directionSystem, List.length_append, polarRows_length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left F.length (kernelSpace_parameter_bound U)) U.length

end PNP.Concrete.ResidualReduction.SourceDirections
