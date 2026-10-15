import PNP.Concrete.ResidualReduction.BilinearPullback

namespace PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.FactoredContraction PNP.Concrete.ResidualReduction.BinaryLinear

theorem homogeneous_zero {n : Nat} (rs : System n) :
    satisfies (homogeneous rs) (zeroPoint n) = true := by
  apply (satisfies_iff _ _).mpr
  intro f hf
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hf
  rw [homogeneousRow_eval, eval_zero_constant, Bool.xor_self]

theorem homogeneousRow_constant {n : Nat} (f : Affine n) :
    aConstant (homogeneousRow f) = false := by
  rw [← eval_zero_constant, homogeneousRow_eval, eval_zero_constant, Bool.xor_self]

theorem homogeneous_twice {n : Nat} (rs : System n) (x : Point n) :
    satisfies (homogeneous (homogeneous rs)) x = satisfies (homogeneous rs) x := by
  induction rs with
  | nil => rfl
  | cons f rs ih =>
    simp only [homogeneous, List.map_cons, satisfies, homogeneousRow_eval,
      homogeneousRow_constant, Bool.xor_false] at *
    rw [ih]

theorem homogeneous_solved {n : Nat} (rs : System n) :
    ∃ s, solve n (homogeneous rs) = some s := by
  cases h : solve n (homogeneous rs) with
  | none =>
    exact False.elim ((solve_none_iff (homogeneous rs)).mp h
      ⟨zeroPoint n, homogeneous_zero rs⟩)
  | some s => exact ⟨s, rfl⟩

theorem kernel_sound {n : Nat} (rs : System n) (s : Space n)
    (h : solve n (homogeneous rs) = some s) (z : Point s.parameters) :
    satisfies (homogeneous rs) (s.direction z) = true := by
  have hz := solve_direction_sound (homogeneous rs) s h z
  rw [homogeneous_twice] at hz
  exact hz

theorem kernel_complete {n : Nat} (rs : System n) (s : Space n)
    (h : solve n (homogeneous rs) = some s) (x : Point n)
    (hx : satisfies (homogeneous rs) x = true) :
    ∃ z, s.direction z = x :=
  solve_direction_complete (homogeneous rs) s h x
    ((homogeneous_twice rs x).trans hx)

/-- The rows are interpreted homogeneously: only their linear coefficients
    constrain the two inputs. Affine constrained queries are a separate problem. -/
def Good {m n : Nat} (rs : System m) (ts : System n)
    (A C : Matrix m n) (w : Point m × Point n) : Prop :=
  satisfies (homogeneous rs) w.1 = true ∧
  satisfies (homogeneous ts) w.2 = true ∧
  bilinearEval A w.1 w.2 = false ∧ bilinearEval C w.1 w.2 = true

/-- Compute both parameter spaces internally, then solve and lift the exact
    pulled-back bilinear query. There is no supplied basis or proof certificate. -/
def query {m n : Nat} (rs : System m) (ts : System n)
    (A C : Matrix m n) : Option (Point m × Point n) :=
  match solve m (homogeneous rs), solve n (homogeneous ts) with
  | some s, some t =>
    match (BilinearSelection.select (pullMatrix A s t) (pullMatrix C s t)).witness with
    | none => none
    | some w => some (s.direction (sumUnits w.1), t.direction (sumUnits w.2))
  | _, _ => none

theorem query_sound {m n : Nat} (rs : System m) (ts : System n)
    (A C : Matrix m n) (w : Point m × Point n)
    (h : query rs ts A C = some w) : Good rs ts A C w := by
  cases hs : solve m (homogeneous rs) with
  | none => simp only [query, hs, reduceCtorEq] at h
  | some s =>
    cases ht : solve n (homogeneous ts) with
    | none => simp only [query, hs, ht, reduceCtorEq] at h
    | some t =>
      cases hw : (BilinearSelection.select (pullMatrix A s t) (pullMatrix C s t)).witness with
      | none => simp only [query, hs, ht, hw, reduceCtorEq] at h
      | some v =>
        have he : (s.direction (sumUnits v.1), t.direction (sumUnits v.2)) = w := by
          simpa only [query, hs, ht, hw, Option.some.injEq] using h
        subst w
        obtain ⟨_, _, ha, hc⟩ := BilinearSelection.select_sound _ _ hw
        rw [pull_eval] at ha hc
        exact ⟨kernel_sound rs s hs _, kernel_sound ts t ht _, ha, hc⟩

theorem query_complete {m n : Nat} (rs : System m) (ts : System n)
    (A C : Matrix m n) (h : ∃ w, Good rs ts A C w) :
    ∃ w, query rs ts A C = some w := by
  obtain ⟨s, hs⟩ := homogeneous_solved rs
  obtain ⟨t, ht⟩ := homogeneous_solved ts
  obtain ⟨⟨x, y⟩, hx, hy, ha, hc⟩ := h
  obtain ⟨z, hz⟩ := kernel_complete rs s hs x hx
  obtain ⟨v, hv⟩ := kernel_complete ts t ht y hy
  have pa : BilinearSelection.eval (pullMatrix A s t) (support z) (support v) = false := by
    rw [pull_eval, sumUnits_support, sumUnits_support, hz, hv]
    exact ha
  have pc : BilinearSelection.eval (pullMatrix C s t) (support z) (support v) = true := by
    rw [pull_eval, sumUnits_support, sumUnits_support, hz, hv]
    exact hc
  obtain ⟨w, hw⟩ := BilinearSelection.select_complete_for_any_witness
    (pullMatrix A s t) (pullMatrix C s t) ⟨support z, support v, pa, pc⟩
  exact ⟨(s.direction (sumUnits w.1), t.direction (sumUnits w.2)),
    by simp only [query, hs, ht, hw]⟩

theorem query_none_iff {m n : Nat} (rs : System m) (ts : System n)
    (A C : Matrix m n) :
    query rs ts A C = none ↔ ¬ ∃ w, Good rs ts A C w := by
  constructor
  · intro hn hg
    obtain ⟨w, hw⟩ := query_complete rs ts A C hg
    simp only [hn, reduceCtorEq] at hw
  · intro hg
    cases h : query rs ts A C with
    | none => rfl
    | some w => exact False.elim (hg ⟨w, query_sound rs ts A C w h⟩)

theorem query_exists_iff {m n : Nat} (rs : System m) (ts : System n)
    (A C : Matrix m n) :
    (∃ w, query rs ts A C = some w) ↔ ∃ w, Good rs ts A C w :=
  ⟨fun ⟨w, h⟩ => ⟨w, query_sound rs ts A C w h⟩, query_complete rs ts A C⟩

/-- This is a coefficient-query charge bound, not a full encoded runtime bound. -/
theorem pulled_query_charge {m n : Nat} (rs : System m) (ts : System n)
    (A C : Matrix m n) (s : Space m) (t : Space n)
    (hs : solve m (homogeneous rs) = some s)
    (ht : solve n (homogeneous ts) = some t) :
    (BilinearSelection.select (pullMatrix A s t) (pullMatrix C s t)).matrixReadCharge ≤
      3 * (m * n) + 72 := by
  apply Nat.le_trans (BilinearSelection.matrix_read_charge_bound _ _)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.mul_le_mul
    (solve_some_parameter_bound _ _ hs) (solve_some_parameter_bound _ _ ht))) 72

end PNP.Concrete.ResidualReduction.ConstrainedBilinear
