import PNP.Concrete.ResidualReduction.BinaryLinearSolver

namespace PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.FactoredContraction

/-- Clear only the affine constant, retaining every source coefficient. -/
def homogeneousRow {n : Nat} (f : Affine n) : Affine n :=
  aAdd f (aConst n (aConstant f))

def homogeneous {n : Nat} (rs : System n) : System n :=
  rs.map homogeneousRow

theorem homogeneousRow_eval {n : Nat} (f : Affine n) (x : Point n) :
    aEval (homogeneousRow f) x = Bool.xor (aEval f x) (aConstant f) := by
  simp only [homogeneousRow, aAdd_eval, aConst_eval]

theorem homogeneous_difference {n : Nat} (rs : System n) (x y : Point n)
    (hx : satisfies rs x = true) (hy : satisfies rs y = true) :
    satisfies (homogeneous rs) (pXor x y) = true := by
  apply (satisfies_iff _ _).mpr
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  rw [homogeneousRow_eval, aEval_xor,
    (satisfies_iff rs x).mp hx g hg, (satisfies_iff rs y).mp hy g hg]
  cases aConstant g <;> rfl

theorem homogeneous_translate {n : Nat} (rs : System n) (x d : Point n)
    (hx : satisfies rs x = true) (hd : satisfies (homogeneous rs) d = true) :
    satisfies rs (pXor d x) = true := by
  apply (satisfies_iff _ _).mpr
  intro f hf
  have hdir := (satisfies_iff (homogeneous rs) d).mp hd (homogeneousRow f)
    (List.mem_map.mpr ⟨f, hf, rfl⟩)
  rw [homogeneousRow_eval] at hdir
  rw [aEval_xor, (satisfies_iff rs x).mp hx f hf, Bool.xor_false]
  exact hdir

def Space.particular {n : Nat} (s : Space n) : Point n :=
  mapEval s.forms (zeroPoint s.parameters)

def Space.direction {n : Nat} (s : Space n) (z : Point s.parameters) : Point n :=
  linearMapEval s.forms z

theorem solve_particular {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) : satisfies rs s.particular = true :=
  solve_some_sound rs s h (zeroPoint s.parameters)

theorem solve_direction_sound {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) (z : Point s.parameters) :
    satisfies (homogeneous rs) (s.direction z) = true :=
  homogeneous_difference rs (mapEval s.forms z) s.particular
    (solve_some_sound rs s h z) (solve_particular rs s h)

theorem solve_direction_complete {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) (d : Point n)
    (hd : satisfies (homogeneous rs) d = true) :
    ∃ z, s.direction z = d := by
  have hx := homogeneous_translate rs s.particular d (solve_particular rs s h) hd
  obtain ⟨z, hz⟩ := solve_some_complete rs s h (pXor d s.particular) hx
  refine ⟨z, ?_⟩
  unfold Space.direction linearMapEval
  rw [hz]
  exact pXor_twice d s.particular

theorem solve_direction_iff {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) (d : Point n) :
    satisfies (homogeneous rs) d = true ↔ ∃ z, s.direction z = d := by
  constructor
  · exact solve_direction_complete rs s h d
  · rintro ⟨z, rfl⟩
    exact solve_direction_sound rs s h z

theorem Space.direction_additive {n : Nat} (s : Space n)
    (x y : Point s.parameters) :
    s.direction (pXor x y) = pXor (s.direction x) (s.direction y) :=
  linearMapEval_xor s.forms x y

theorem solve_direction_injective {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) (x y : Point s.parameters)
    (he : s.direction x = s.direction y) : x = y := by
  apply solve_some_injective rs s h x y
  have ht := congrArg (fun d => pXor d s.particular) he
  simpa only [Space.direction, Space.particular, linearMapEval, pXor_twice] using ht

theorem solve_affine_fiber {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) (x : Point n) :
    satisfies rs x = true ↔
      ∃ z, pXor (s.direction z) s.particular = x := by
  simpa only [Space.direction, Space.particular, mapEval_from_linear] using
    solve_some_iff_parameter rs s h x

/-- The particular point and the complete independent homogeneous direction
    family are computed by the solver, not supplied as premises. -/
theorem solve_complete_space {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) :
    satisfies rs s.particular = true ∧
    (∀ d, satisfies (homogeneous rs) d = true ↔ ∃ z, s.direction z = d) ∧
    (∀ x y, s.direction (pXor x y) = pXor (s.direction x) (s.direction y)) ∧
    (∀ x y, s.direction x = s.direction y → x = y) ∧
    (∀ x, satisfies rs x = true ↔
      ∃ z, pXor (s.direction z) s.particular = x) ∧
    coefficientBits n s.parameters ≤ n * (n + 1) :=
  ⟨solve_particular rs s h, solve_direction_iff rs s h,
    s.direction_additive, solve_direction_injective rs s h,
    solve_affine_fiber rs s h, solve_output_coefficient_bound rs s h⟩

end PNP.Concrete.ResidualReduction.BinaryLinear
