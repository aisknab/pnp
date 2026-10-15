import PNP.Concrete.ResidualReduction.SourcePolar

namespace PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear PNP.Concrete.ResidualReduction.ConstrainedBilinear

/-- A total computed kernel. The inconsistent branch is impossible for a
    homogeneous system by the checked solver, not by an input certificate. -/
def kernelSpace {n : Nat} (rs : System n) : Space n :=
  match h : solve n (homogeneous rs) with
  | some s => s
  | none => False.elim ((solve_none_iff (homogeneous rs)).mp h
      ⟨zeroPoint n, homogeneous_zero rs⟩)

theorem kernelSpace_spec {n : Nat} (rs : System n) :
    solve n (homogeneous rs) = some (kernelSpace rs) := by
  unfold kernelSpace
  split
  next s h => exact h
  next h =>
    exact False.elim ((solve_none_iff (homogeneous rs)).mp h
      ⟨zeroPoint n, homogeneous_zero rs⟩)

theorem kernelSpace_sound {n : Nat} (rs : System n)
    (z : Point (kernelSpace rs).parameters) :
    satisfies (homogeneous rs) ((kernelSpace rs).direction z) = true :=
  kernel_sound rs (kernelSpace rs) (kernelSpace_spec rs) z

theorem kernelSpace_iff {n : Nat} (rs : System n) (x : Point n) :
    satisfies (homogeneous rs) x = true ↔ ∃ z, (kernelSpace rs).direction z = x :=
  ⟨kernel_complete rs (kernelSpace rs) (kernelSpace_spec rs) x,
    fun ⟨z, h⟩ => h ▸ kernelSpace_sound rs z⟩

theorem kernelSpace_parameter_bound {n : Nat} (rs : System n) :
    (kernelSpace rs).parameters ≤ n :=
  solve_some_parameter_bound _ _ (kernelSpace_spec rs)

theorem additive_vanish_on_kernel {n : Nat} (U : System n) (f : Point n → Bool)
    (hzero : f (zeroPoint n) = false)
    (hadd : ∀ x y, f (pXor x y) = Bool.xor (f x) (f y)) :
    (∀ j, f ((kernelSpace U).direction (unitPoint _ j)) = false) ↔
      ∀ x, satisfies (homogeneous U) x = true → f x = false := by
  constructor
  · intro hj x hx
    obtain ⟨z, rfl⟩ := (kernelSpace_iff U x).mp hx
    have hs : ∀ is : List (Fin (kernelSpace U).parameters),
        f ((kernelSpace U).direction (sumUnits is)) = false := by
      intro is
      induction is with
      | nil => simpa only [sumUnits, direction_zero] using hzero
      | cons i is ih =>
        rw [sumUnits, Space.direction_additive, hadd, hj, ih, Bool.false_xor]
    simpa only [sumUnits_support] using hs (support z)
  · intro h j
    exact h _ (kernelSpace_sound U _)

theorem rowDot_unit {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    rowDot f (unitPoint n i) = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [unitPoint_zero, rowDot, Bool.and_true, rowDot_zero, Bool.xor_false]
    · simpa only [unitPoint_succ, rowDot, Bool.and_false, Bool.false_xor] using
        ih (fun k => f k.succ) j

theorem additive_coefficient_exact {n : Nat} (f : Point n → Bool)
    (hzero : f (zeroPoint n) = false)
    (hadd : ∀ x y, f (pXor x y) = Bool.xor (f x) (f y)) (z : Point n) :
    rowDot (fun j => f (unitPoint n j)) z = f z := by
  have hs : ∀ is : List (Fin n),
      rowDot (fun j => f (unitPoint n j)) (sumUnits is) = f (sumUnits is) := by
    intro is
    induction is with
    | nil => simp only [sumUnits, rowDot_zero, hzero]
    | cons i is ih =>
      rw [sumUnits, rowDot_additive, hadd, rowDot_unit, ih]
  simpa only [sumUnits_support] using hs (support z)

end PNP.Concrete.ResidualReduction.SourceDirections
