import PNP.Concrete.ResidualReduction.SourceMenuSortStep

/-! The actual candidate-sorting loop. It consumes every encoded record and
computes the reference insertion fold, with an explicit instruction bound
for arbitrary dimensions and list lengths. Compiler costs are a separate
boundary; this block neither selects a contraction nor solves a stopped core. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuSort
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuOrder
open PNP.Concrete.ResidualReduction.SourceMenuSortStep

def fold {n : Nat} (xs us : List (Affine n)) : List (Affine n) :=
  xs.foldl (fun menu a => insertNormal a menu) us
def block : Block 14 := .loop 0 SourceMenuSortStep.block
def bound (n total remaining : Nat) : Nat :=
  (SourceMenuSortStep.bound n total + 1) * remaining + 1

theorem fold_length {n : Nat} (xs : List (Affine n)) :
    ∀ us, (fold xs us).length ≤ xs.length + us.length := by
  induction xs with
  | nil =>
    intro us
    simpa only [fold, List.foldl_nil, List.length_nil, Nat.zero_add] using Nat.le_refl us.length
  | cons a xs ih =>
    intro us
    have tail := ih (insertNormal a us)
    have inserted := insertNormal_length_le a us
    change (fold xs (insertNormal a us)).length ≤ (a :: xs).length + us.length
    simp only [List.length_cons]
    omega

theorem fold_homogeneous {n : Nat} (xs : List (Affine n)) :
    ∀ us, (∀ a ∈ xs, Homogeneous a) → (∀ a ∈ us, Homogeneous a) →
      ∀ a ∈ fold xs us, Homogeneous a := by
  induction xs with
  | nil => intro us _ hu; exact hu
  | cons a xs ih =>
    intro us hx hu
    exact ih (insertNormal a us) (fun b hb => hx b (List.mem_cons_of_mem a hb))
      (insert_homogeneous a us (hx a List.mem_cons_self) hu)

theorem input_present {n : Nat} (a : Affine n) (xs us : List (Affine n))
    (s : SourceMenuCompare.Saved) (t : Held) :
    ∃ bit rest, (full (initial (a :: xs) us) s t).get 0 = bit :: rest := by
  cases h : affineWord a with
  | nil =>
    have length := affineWord_length a
    rw [h] at length
    exact False.elim (by simp only [List.length_nil] at length; omega)
  | cons bit rest =>
    refine ⟨bit, rest ++ matrixBits xs, ?_⟩
    change affineWord a ++ matrixBits xs = _
    rw [h]
    rfl

theorem advance_budget (n total m rowCost restCost : Nat)
    (row : rowCost ≤ SourceMenuSortStep.bound n total)
    (rest : restCost ≤ bound n total m) :
    1 + (rowCost + restCost) ≤ bound n total (m + 1) := by
  simp only [bound, Nat.mul_add, Nat.mul_one] at rest ⊢
  omega

theorem block_exec {n : Nat} (xs : List (Affine n)) :
    ∀ (us : List (Affine n)) (s : SourceMenuCompare.Saved) (t : Held) (total : Nat),
      (∀ a ∈ xs, Homogeneous a) → (∀ a ∈ us, Homogeneous a) →
      xs.length + us.length ≤ total →
      ∃ used last held, Exec block (full (initial xs us) s t) used
        (full (initial [] (fold xs us)) last held) ∧ used ≤ bound n total xs.length := by
  induction xs with
  | nil =>
    intro us s t total _ _ _
    refine ⟨1, s, t, ?_, ?_⟩
    · exact Exec.loopStop rfl
    · simp only [bound, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.le_refl]
  | cons a xs ih =>
    intro us s t total hx hu limit
    have ha := hx a List.mem_cons_self
    have remaining : ∀ b ∈ xs, Homogeneous b :=
      fun b hb => hx b (List.mem_cons_of_mem a hb)
    have menu := insert_homogeneous a us ha hu
    have size := insertNormal_length_le a us
    have nextLimit : xs.length + (insertNormal a us).length ≤ total := by
      simp only [List.length_cons] at limit
      omega
    have menuLimit : us.length ≤ total := by
      simp only [List.length_cons] at limit
      omega
    obtain ⟨rowUsed, middle, saved, first, rowBudget⟩ :=
      SourceMenuSortStep.block_exec a xs us ha hu s t
    obtain ⟨used, last, held, rest, restBudget⟩ :=
      ih (insertNormal a us) middle saved total remaining menu nextLimit
    obtain ⟨bit, tail, present⟩ := input_present a xs us s t
    have checked := Exec.loopStep (source := (0 : Fin 14)) present first rest
    refine ⟨1 + (rowUsed + used), last, held, checked, ?_⟩
    have uniform := Nat.le_trans rowBudget (SourceMenuSortStep.bound_mono n us.length total menuLimit)
    exact advance_budget n total xs.length rowUsed used uniform restBudget

theorem output_bound {n : Nat} (xs us : List (Affine n)) :
    (matrixBits (fold xs us)).length ≤ (n + 1) * (xs.length + us.length) := by
  rw [matrixBits_length]
  exact Nat.mul_le_mul_left (n + 1) (fold_length xs us)

def program : Program 14 := block.program 0 7

theorem program_run {n : Nat} (xs us : List (Affine n))
    (hx : ∀ a ∈ xs, Homogeneous a) (hu : ∀ a ∈ us, Homogeneous a)
    (s : SourceMenuCompare.Saved) (t : Held) :
    ∃ used last held,
      BitRegister.run program (used + 1) ⟨.running 0, full (initial xs us) s t⟩ =
        ⟨.accepted, full (initial [] (fold xs us)) last held⟩ ∧
      (full (initial [] (fold xs us)) last held).get 7 = matrixBits (fold xs us) ∧
      used + 1 ≤ bound n (xs.length + us.length) xs.length + 1 := by
  obtain ⟨used, last, held, checked, budget⟩ :=
    block_exec xs us s t (xs.length + us.length) hx hu (Nat.le_refl _)
  exact ⟨used, last, held, checked.program_run 0 7, rfl, by omega⟩

end PNP.Concrete.ResidualReduction.SourceMenuSort
