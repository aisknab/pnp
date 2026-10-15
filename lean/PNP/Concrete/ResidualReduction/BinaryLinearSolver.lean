import PNP.Concrete.ResidualReduction.LinearEquations
import PNP.Concrete.ResidualReduction.AffineSolutionMaps

namespace PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.FactoredContraction

structure Space (n : Nat) where
  parameters : Nat
  forms : AffineMap n parameters

def freeSpace {n : Nat} (s : Space n) : Space (n + 1) :=
  ⟨s.parameters + 1, freeMap s.forms⟩

def pivotSpace {n : Nat} (p : Affine n) (s : Space n) : Space (n + 1) :=
  ⟨s.parameters, pivotMap p s.forms⟩

/-- Eliminate one source coordinate per recursion; no assignment enumeration. -/
def solve : (n : Nat) → System n → Option (Space n)
  | 0, rs =>
    if satisfies rs () = true then some ⟨0, ()⟩ else none
  | n + 1, rs =>
    match choosePivot rs with
    | none => (solve n (tails rs)).map freeSpace
    | some p => (solve n (substituteRows p rs)).map (pivotSpace p)

def Correct {n : Nat} (rs : System n) : Option (Space n) → Prop
  | none => ∀ x, satisfies rs x = false
  | some s =>
    s.parameters ≤ n ∧
    (∀ z, satisfies rs (mapEval s.forms z) = true) ∧
    (∀ x, satisfies rs x = true → ∃ z, mapEval s.forms z = x) ∧
    (∀ z w, mapEval s.forms z = mapEval s.forms w → z = w)

/-- Exact all-solutions result for arbitrary source rows and dimensions. -/
theorem solve_correct (n : Nat) (rs : System n) : Correct rs (solve n rs) := by
  induction n with
  | zero =>
    by_cases h : satisfies rs () = true
    · simp only [solve, h, if_pos, Correct]
      refine ⟨Nat.le_refl 0, ?_, ?_, ?_⟩
      · intro z
        exact h
      · intro x _
        cases x
        exact ⟨(), rfl⟩
      · intro z w _
        cases z
        cases w
        rfl
    · simp only [solve, h, Correct]
      intro x
      cases x
      cases hx : satisfies rs () with
      | false => rfl
      | true => exact (h hx).elim
  | succ n ih =>
    cases hp : choosePivot rs with
    | none =>
      have heads := choosePivot_none rs hp
      have recur := ih (tails rs)
      cases hs : solve n (tails rs) with
      | none =>
        rw [hs] at recur
        simp only [solve, hp, hs, Option.map, Correct]
        intro x
        rcases x with ⟨b, x⟩
        rw [← tails_eval rs heads b x]
        exact recur x
      | some s =>
        rw [hs] at recur
        obtain ⟨hdim, hsound, hcomplete, hinjective⟩ := recur
        simp only [solve, hp, hs, Option.map, Correct, freeSpace]
        refine ⟨Nat.succ_le_succ hdim, ?_, ?_, ?_⟩
        · intro z
          rcases z with ⟨b, z⟩
          rw [freeMap_eval, ← tails_eval rs heads b (mapEval s.forms z)]
          exact hsound z
        · intro x hx
          rcases x with ⟨b, x⟩
          have ht : satisfies (tails rs) x = true :=
            (tails_eval rs heads b x).trans hx
          obtain ⟨z, hz⟩ := hcomplete x ht
          refine ⟨(b, z), ?_⟩
          rw [freeMap_eval, hz]
        · intro z w he
          rcases z with ⟨b, z⟩
          rcases w with ⟨c, w⟩
          rw [freeMap_eval, freeMap_eval] at he
          have hb := congrArg Prod.fst he
          have ht := congrArg Prod.snd he
          exact Prod.ext hb (hinjective z w ht)
    | some p =>
      have recur := ih (substituteRows p rs)
      cases hs : solve n (substituteRows p rs) with
      | none =>
        rw [hs] at recur
        simp only [solve, hp, hs, Option.map, Correct]
        intro x
        rcases x with ⟨b, x⟩
        cases hx : satisfies rs (b, x) with
        | false => rfl
        | true =>
          have hbad := (pivot_equivalence rs p hp b x).mp hx
          exact Bool.noConfusion ((recur x).symm.trans hbad.2)
      | some s =>
        rw [hs] at recur
        obtain ⟨hdim, hsound, hcomplete, hinjective⟩ := recur
        simp only [solve, hp, hs, Option.map, Correct, pivotSpace]
        refine ⟨Nat.le_trans hdim (Nat.le_succ n), ?_, ?_, ?_⟩
        · intro z
          rw [pivotMap_eval]
          exact (pivot_equivalence rs p hp _ _).mpr ⟨rfl, hsound z⟩
        · intro x hx
          rcases x with ⟨b, x⟩
          obtain ⟨hb, ht⟩ := (pivot_equivalence rs p hp b x).mp hx
          obtain ⟨z, hz⟩ := hcomplete x ht
          refine ⟨z, ?_⟩
          rw [pivotMap_eval, hz, ← hb]
        · intro z w he
          rw [pivotMap_eval, pivotMap_eval] at he
          exact hinjective z w (congrArg Prod.snd he)

theorem solve_some_parameter_bound {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) : s.parameters ≤ n := by
  have hc := solve_correct n rs
  rw [h] at hc
  exact hc.1

theorem solve_some_sound {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) (z : Point s.parameters) :
    satisfies rs (mapEval s.forms z) = true := by
  have hc := solve_correct n rs
  rw [h] at hc
  exact hc.2.1 z

theorem solve_some_complete {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) (x : Point n) (hx : satisfies rs x = true) :
    ∃ z, mapEval s.forms z = x := by
  have hc := solve_correct n rs
  rw [h] at hc
  exact hc.2.2.1 x hx

theorem solve_some_injective {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) (z w : Point s.parameters)
    (he : mapEval s.forms z = mapEval s.forms w) : z = w := by
  have hc := solve_correct n rs
  rw [h] at hc
  exact hc.2.2.2 z w he

theorem solve_none_iff {n : Nat} (rs : System n) :
    solve n rs = none ↔ ¬ ∃ x, satisfies rs x = true := by
  constructor
  · intro h
    have hc := solve_correct n rs
    rw [h] at hc
    rintro ⟨x, hx⟩
    exact Bool.noConfusion ((hc x).symm.trans hx)
  · intro h
    cases hs : solve n rs with
    | none => rfl
    | some s =>
      exact (h ⟨mapEval s.forms (zeroPoint s.parameters),
        solve_some_sound rs s hs (zeroPoint s.parameters)⟩).elim

theorem solve_some_iff_parameter {n : Nat} (rs : System n) (s : Space n)
    (h : solve n rs = some s) (x : Point n) :
    satisfies rs x = true ↔ ∃ z, mapEval s.forms z = x := by
  constructor
  · exact solve_some_complete rs s h x
  · rintro ⟨z, rfl⟩
    exact solve_some_sound rs s h z

theorem solve_output_coefficient_bound {n : Nat} (rs : System n)
    (s : Space n) (h : solve n rs = some s) :
    coefficientBits n s.parameters ≤ n * (n + 1) :=
  coefficientBits_bound (solve_some_parameter_bound rs s h)

end PNP.Concrete.ResidualReduction.BinaryLinear
