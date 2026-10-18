import PNP.Concrete.ResidualReduction.SourceMenuSort

/-! Construct and sort the entire source-derived normal menu. Source rows
alone determine candidates, homogeneity, ordering and duplicate handling.
The finite program returns exactly sourceMenu for every family and dimension.
This is not the raw parser/compiler theorem or a complete contraction. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuFromFamily
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuOrder
open PNP.Concrete.ResidualReduction.SourceMenuSortStep

def rowSaved (s : SourceMenuCompare.Saved) : SourceMenuRow.Saved :=
  ⟨s.tail, s.width, s.firstFlag⟩
def compareSaved (s : SourceMenuRow.Saved) : SourceMenuCompare.Saved :=
  ⟨s.stream, s.width, s.accumulator⟩
def candidates {n : Nat} (F : Family n) : List (Affine n) := (F.flatMap rowNormals).reverse

theorem candidates_homogeneous {n : Nat} (F : Family n) :
    ∀ a ∈ candidates F, Homogeneous a := by
  intro a ha
  exact family_homogeneous F a (List.mem_reverse.mp ha)

theorem candidates_length {n : Nat} (F : Family n) : (candidates F).length ≤ 3 * F.length := by
  simpa only [candidates, List.length_reverse] using SourceMenuFamily.candidate_count F

theorem fold_exact {n : Nat} (F : Family n) :
    SourceMenuSort.fold (candidates F) [] = sourceMenu F :=
  SourceMenuFamily.source_menu_link F

def prepare : Block 9 := .seq (.action (.copy 0 7)) <|
  .seq (.action (.push 1 true)) (.action (.clear 7))

theorem prepare_exec {n : Nat} (xs : List (Affine n)) :
    Exec prepare (SourceMenuRowInput.initial n [] (matrixBits xs)).store 3
      (SourceMenuSortStep.initial xs []).store := by
  simp only [SourceMenuRowInput.initial, SourceMenuSortStep.initial, List.replicate_succ, matrixBits]
  exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def initial {n : Nat} (F : Family n) (s : SourceMenuCompare.Saved) (t : Held) : Store 14 :=
  Frame.join (SourceMenuFamily.initial F [] (rowSaved s)) t.store
def terminal {n : Nat} (F : Family n) (s : SourceMenuCompare.Saved) (t : Held) : Store 14 :=
  full (SourceMenuSortStep.initial [] (sourceMenu F)) s t

def block : Block 14 := .seq (Frame.block 2 SourceMenuFamily.block) <|
  .seq (Frame.block 5 prepare) SourceMenuSort.block
def bound (n m : Nat) : Nat :=
  (43 * n + 53) * m + 7 + (3 + SourceMenuSort.bound n (3 * m) (3 * m))

theorem block_exec {n : Nat} (F : Family n) (s : SourceMenuCompare.Saved) (t : Held) :
    ∃ used last held, Exec block (initial F s t) used (terminal F last held) ∧
      used ≤ bound n F.length := by
  obtain ⟨familyUsed, rowLast, built, familyBudget⟩ := SourceMenuFamily.block_exec F [] (rowSaved s)
  have first := Frame.execution built t.store
  simp only [List.append_nil] at first
  have second := Frame.execution (prepare_exec (candidates F)) (frame (compareSaved rowLast) t)
  have count := candidates_length F
  have limit : (candidates F).length + ([] : List (Affine n)).length ≤ 3 * F.length := by
    simpa only [List.length_nil, Nat.add_zero] using count
  have empty : ∀ a ∈ ([] : List (Affine n)), Homogeneous a := by
    intro a ha
    exact False.elim (List.not_mem_nil ha)
  obtain ⟨sortUsed, last, held, sorted, sortBudget⟩ := SourceMenuSort.block_exec (candidates F) []
    (compareSaved rowLast) t (3 * F.length) (candidates_homogeneous F) empty limit
  rw [fold_exact] at sorted
  have sortLimit : sortUsed ≤ SourceMenuSort.bound n (3 * F.length) (3 * F.length) := by
    have scaled := Nat.mul_le_mul_left (SourceMenuSortStep.bound n (3 * F.length) + 1) count
    simp only [SourceMenuSort.bound] at sortBudget ⊢
    omega
  refine ⟨familyUsed + (3 + sortUsed), last, held, Exec.seq first (Exec.seq second sorted), ?_⟩
  unfold bound
  omega

/-- The empty-family path executes no candidate iteration. -/
theorem empty_exec (n : Nat) (s : SourceMenuCompare.Saved) (t : Held) :
    Exec block (initial ([] : Family n) s t) 11 (terminal (n := n) [] s t) := by
  have header := Frame.execution (SourceMenuFamily.header_exec n 0 [] []) (rowSaved s).store
  have rows : Exec SourceMenuFamily.rowLoop (SourceMenuFamily.rowInitial ([] : Family n) [] (rowSaved s))
      1 (SourceMenuFamily.terminal n [] (rowSaved s)) := Exec.loopStop rfl
  have generated : Exec SourceMenuFamily.block (SourceMenuFamily.initial ([] : Family n) [] (rowSaved s))
      7 (SourceMenuFamily.terminal n [] (rowSaved s)) := Exec.seq header rows
  have first := Frame.execution generated t.store
  have second := Frame.execution (prepare_exec ([] : List (Affine n))) (frame s t)
  have stopped : Exec SourceMenuSort.block (full (SourceMenuSortStep.initial ([] : List (Affine n)) []) s t)
      1 (terminal (n := n) [] s t) := Exec.loopStop rfl
  exact Exec.seq first (Exec.seq second stopped)

theorem output_bound {n : Nat} (F : Family n) :
    (matrixBits (sourceMenu F)).length ≤ (n + 1) * (3 * F.length) := by
  have general := SourceMenuSort.output_bound (candidates F) []
  rw [fold_exact] at general
  have scaled := Nat.mul_le_mul_left (n + 1) (candidates_length F)
  simp only [List.length_nil, Nat.add_zero] at general
  exact Nat.le_trans general scaled

def program : Program 14 := block.program 0 7

theorem program_run {n : Nat} (F : Family n) (s : SourceMenuCompare.Saved) (t : Held) :
    ∃ used last held,
      BitRegister.run program (used + 1) ⟨.running 0, initial F s t⟩ =
        ⟨.accepted, terminal F last held⟩ ∧
      (terminal F last held).get 7 = matrixBits (sourceMenu F) ∧
      used + 1 ≤ bound n F.length + 1 := by
  obtain ⟨used, last, held, checked, budget⟩ := block_exec F s t
  exact ⟨used, last, held, checked.program_run 0 7, rfl, by omega⟩

end PNP.Concrete.ResidualReduction.SourceMenuFromFamily
