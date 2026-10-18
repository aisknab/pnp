import PNP.Concrete.ResidualReduction.SourceMenuInsertStep

/-! Exact finite-machine insertion for every homogeneous candidate and finite
homogeneous menu, including unsorted menus. The equality/order behavior is
the reference insertNormal, not a supplied sorting certificate. This is the
general insertion component; the outer source-derived sorting loop and raw
parser/compiler integration are separate obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuInsertion
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceMenuOrder
open PNP.Concrete.ResidualReduction.SourceMenuCompare
open PNP.Concrete.ResidualReduction.SourceMenuInsertStep

def body : Block 12 := .branch 0 (Frame.block 3 SourceMenuInsertOutput.atEnd) step step
def block : Block 12 := .loop 6 body
def bound (n m priorBytes : Nat) : Nat := (80 * (n + 1) + 80) * (m + 1) + 4 * priorBytes

theorem body_exec {n : Nat} (a b : Affine n) (us : List (Affine n)) (prior : BitString) (s : Saved) :
    Exec body (full (ready a (b :: us) prior) s) (1 + stepCost a b us prior)
      (full (selected (compared a b us prior) (lower a b) (lower b a)) (saved a b us prior)) := by
  cases h : affineWord b with
  | nil =>
    have length := affineWord_length b
    rw [h] at length
    exact False.elim (by simp only [List.length_nil] at length; omega)
  | cons bit rest =>
    have read : (full (ready a (b :: us) prior) s).get 0 = bit :: (rest ++ matrixBits us) := by
      change affineWord b ++ matrixBits us = _
      rw [h]
      rfl
    exact Exec.nonempty read (step_exec a b us prior s)

theorem advance_budget (n m priorBytes rowCost restCost : Nat)
    (row : rowCost ≤ 41 * (n + 1) + 32)
    (rest : restCost ≤ bound n m ((n + 1) + priorBytes)) :
    1 + ((1 + rowCost) + restCost) ≤ bound n (m + 1) priorBytes := by
  simp only [bound, Nat.mul_add, Nat.mul_one] at rest ⊢
  omega

theorem stop_budget (n m priorBytes rowCost : Nat)
    (row : rowCost ≤ 53 * (n + 1) + 4 * priorBytes + 8 * ((n + 1) * m) + 45) :
    1 + ((1 + rowCost) + 1) ≤ bound n (m + 1) priorBytes := by
  simp only [bound, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc] at row ⊢
  omega

theorem block_exec {n : Nat} (a : Affine n) (ha : Homogeneous a) (us : List (Affine n)) :
    ∀ (prior : BitString) (s : Saved), (∀ b ∈ us, Homogeneous b) →
      ∃ used after last, Exec block (full (ready a us prior) s) used (full after last) ∧
        after.active = [] ∧ after.output = prior.reverse ++ matrixBits (insertNormal a us) ∧
        used ≤ bound n us.length prior.length := by
  induction us with
  | nil =>
    intro prior s _
    let after := SourceMenuInsertOutput.endResult (ready a [] prior)
    have ended := Frame.execution (SourceMenuInsertOutput.end_exec (ready a [] prior)) s.store
    have first : Exec body (full (ready a [] prior) s)
        (1 + SourceMenuInsertOutput.endCost (ready a [] prior)) (full after s) :=
      Exec.empty rfl ended
    have stopped : Exec block (full after s) 1 (full after s) := Exec.loopStop rfl
    have checked := Exec.loopStep (source := (6 : Fin 12)) rfl first stopped
    refine ⟨1 + ((1 + SourceMenuInsertOutput.endCost (ready a [] prior)) + 1), after, s,
      checked, rfl, ?_, ?_⟩
    · exact SourceMenuInsertStep.end_output a prior
    · simp only [bound, SourceMenuInsertOutput.endCost, ready, affineWord_length,
        List.length_nil, Nat.zero_add, Nat.mul_one]
      omega
  | cons b us ih =>
    intro prior s homogeneous
    have hb := homogeneous b List.mem_cons_self
    have hu : ∀ x ∈ us, Homogeneous x :=
      fun x hx => homogeneous x (List.mem_cons_of_mem b hx)
    have first := body_exec a b us prior s
    cases lo : lower a b with
    | false =>
      have advanced : Exec body (full (ready a (b :: us) prior) s) (1 + stepCost a b us prior)
          (full (ready a us ((affineWord b).reverse ++ prior)) (saved a b us prior)) := by
        simpa only [lo, selected, Bool.false_eq_true, ↓reduceIte, advance_state] using first
      obtain ⟨used, after, last, rest, stopped, output, budget⟩ :=
        ih ((affineWord b).reverse ++ prior) (saved a b us prior) hu
      have checked := Exec.loopStep (source := (6 : Fin 12)) rfl advanced rest
      have insertion : insertNormal a (b :: us) = b :: insertNormal a us := by
        rw [insert_by_flags a b us ha hb, lo]
        rfl
      refine ⟨1 + ((1 + stepCost a b us prior) + used), after, last, checked, stopped, ?_, ?_⟩
      · simpa only [insertion, matrixBits, List.reverse_append, List.reverse_reverse,
          List.append_assoc] using output
      · have row := advance_cost_bound a b us prior lo
        simp only [List.length_append, List.length_reverse, affineWord_length] at budget
        exact advance_budget n us.length prior.length _ _ row budget
    | true =>
      have row := stop_cost_bound a b us prior lo
      cases hi : lower b a with
      | false =>
        let after := SourceMenuInsertOutput.beforeResult (compared a b us prior)
        have finishing : Exec body (full (ready a (b :: us) prior) s) (1 + stepCost a b us prior)
            (full after (saved a b us prior)) := by
          simpa only [lo, hi, selected, Bool.false_eq_true, ↓reduceIte] using first
        have stopped : Exec block (full after (saved a b us prior)) 1
            (full after (saved a b us prior)) := Exec.loopStop rfl
        have checked := Exec.loopStep (source := (6 : Fin 12)) rfl finishing stopped
        have insertion : insertNormal a (b :: us) = a :: b :: us := by
          rw [insert_by_flags a b us ha hb, lo, hi]
          rfl
        refine ⟨1 + ((1 + stepCost a b us prior) + 1), after, saved a b us prior,
          checked, rfl, ?_, stop_budget n us.length prior.length _ row⟩
        rw [insertion]
        exact SourceMenuInsertStep.before_output a b us prior
      | true =>
        let after := SourceMenuInsertOutput.equalResult (compared a b us prior)
        have finishing : Exec body (full (ready a (b :: us) prior) s) (1 + stepCost a b us prior)
            (full after (saved a b us prior)) := by
          simpa only [lo, hi, selected, ↓reduceIte] using first
        have stopped : Exec block (full after (saved a b us prior)) 1
            (full after (saved a b us prior)) := Exec.loopStop rfl
        have checked := Exec.loopStep (source := (6 : Fin 12)) rfl finishing stopped
        have insertion : insertNormal a (b :: us) = b :: us := by
          rw [insert_by_flags a b us ha hb, lo, hi]
          rfl
        refine ⟨1 + ((1 + stepCost a b us prior) + 1), after, saved a b us prior,
          checked, rfl, ?_, stop_budget n us.length prior.length _ row⟩
        rw [insertion]
        exact SourceMenuInsertStep.equal_output a b us prior

theorem output_bound {n : Nat} (a : Affine n) (us : List (Affine n)) (prior : BitString) :
    (prior.reverse ++ matrixBits (insertNormal a us)).length ≤
      prior.length + (n + 1) * (us.length + 1) := by
  have count := Nat.mul_le_mul_left (n + 1) (insertNormal_length_le a us)
  simp only [List.length_append, List.length_reverse, matrixBits_length]
  omega

def program : Program 12 := block.program 0 8

theorem program_run {n : Nat} (a : Affine n) (ha : Homogeneous a) (us : List (Affine n))
    (hu : ∀ b ∈ us, Homogeneous b) (prior : BitString) (s : Saved) :
    ∃ used after last,
      BitRegister.run program (used + 1) ⟨.running 0, full (ready a us prior) s⟩ =
        ⟨.accepted, full after last⟩ ∧
      (full after last).get 8 = prior.reverse ++ matrixBits (insertNormal a us) ∧
      used + 1 ≤ bound n us.length prior.length + 1 := by
  obtain ⟨used, after, last, checked, _, output, budget⟩ := block_exec a ha us prior s hu
  exact ⟨used, after, last, checked.program_run 0 8,
    (Frame.get_core after.store last.store (8 : Fin 9)).trans output, by omega⟩

end PNP.Concrete.ResidualReduction.SourceMenuInsertion
