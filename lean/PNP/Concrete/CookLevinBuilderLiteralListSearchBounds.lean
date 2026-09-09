/-
Copyright (c) 2026 PNP Labs.

Uniform encoded-input polynomial bounds for the complete cyclic literal-list
lookup. A single original-input span envelope covers every iteration. Retained
history is charged once per miss, while ordinal plus remaining length stays
constant and the residual position never grows. No per-iteration polynomial is
iterated through the runtime loop.
-/

import PNP.Concrete.CookLevinBuilderLiteralListSearch

namespace PNP.Concrete.CookLevin.BuilderLiteralListSearchBounds

open PipelineTape BuilderUnaryPolynomial
open BuilderLocalConstraintPayload (literalListValues)
open BuilderLiteralSearchFrame (chunk residual historyStride)
open BuilderLiteralListSearch (comparedOutside searchSteps finishValues finishOutside)

def stepAllowance (bound : Nat) : Nat := 100 * bound + 100
def entryBudget (bound ordinal : Nat) : Nat := bound + ordinal * stepAllowance bound
def envelope (bound : NatPolynomial) : NatPolynomial := BuilderLiteralSearchFrame.globalSpanPolynomial bound
def passRawPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderLiteralSearchGuard.rawTimePolynomial (envelope bound))
    (.add (BuilderLiteralSearchComparison.rawTimePolynomial (envelope bound))
      (.add (BuilderLiteralSearchAdvance.rawTimePolynomial (envelope bound))
        (.add (BuilderLiteralSearchSelect.rawTimePolynomial (envelope bound)) (.constant 18))))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.add bound (.constant 1)) (passRawPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (envelope bound) (BuilderLiteralSearchSelect.spanPolynomial (envelope bound))

theorem envelope_eval (bound : NatPolynomial) (input : Nat) :
    (envelope bound).eval input = entryBudget (bound.eval input) (bound.eval input + 1) := rfl

theorem entryBudget_step (bound ordinal : Nat) :
    entryBudget bound (ordinal + 1) = entryBudget bound ordinal + stepAllowance bound := by
  simp only [entryBudget, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem entryBudget_le_envelope (bound : NatPolynomial) (input ordinal : Nat)
    (hOrdinal : ordinal ≤ bound.eval input + 1) :
    entryBudget (bound.eval input) ordinal ≤ (envelope bound).eval input := by
  rw [envelope_eval]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hOrdinal) _

private theorem getElem_le_sum (values : List Nat) (ordinal : Nat) (hOrdinal : ordinal < values.length) :
    values[ordinal] ≤ values.sum := by
  induction values generalizing ordinal with
  | nil => simp only [List.length_nil] at hOrdinal; omega
  | cons value rest ih =>
      cases ordinal with
      | zero =>
          simp only [List.getElem_cons_zero, List.sum_cons]
          omega
      | succ ordinal =>
          have hRest : ordinal < rest.length := by simp only [List.length_cons] at hOrdinal; omega
          have h := ih ordinal hRest
          simp only [List.getElem_cons_succ, List.sum_cons]
          omega

private theorem indexed_value_le {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (bound : Nat) (hPayload : (literalListValues literals).sum ≤ bound) :
    literals[index.val].index.val ≤ bound := by
  have h := getElem_le_sum (literalListValues literals) (2 * index.val + 1)
    (BuilderPayloadFieldCopy.literal_field_lt literals index.val index.isLt ⟨1, by decide⟩)
  rw [BuilderPayloadFieldCopy.literal_field_value literals index.val index.isLt ⟨1, by decide⟩] at h
  change literals[index.val].index.val ≤ (literalListValues literals).sum at h
  exact Nat.le_trans h hPayload

/-- Comparison and advancement do not grow the exterior; the guard is charged once. -/
theorem continued_span (payload older prior : List Nat) (ordinal remaining position value : Nat)
    (outside : List WorkSymbol) :
    (registerWord (BuilderLiteralSearchComparison.initialValues payload older
      (prior ++ chunk ordinal (remaining + 1) position value) (ordinal + 1) remaining (residual position value))).length +
      (BuilderLiteralSearchAdvance.finalOutside ordinal remaining position value
        (comparedOutside ordinal (remaining + 1) position value outside)).length ≤
    (registerWord (BuilderLiteralSearchComparison.initialValues payload older prior ordinal (remaining + 1) position)).length +
      outside.length + (registerWord (chunk ordinal (remaining + 1) position value)).length + (remaining + 2) := by
  have hGuard := BuilderLiteralSearchGuard.finalOutside_length_le (remaining + 1) outside
  have hCompare := BuilderLiteralSearchComparison.finalOutside_length_le ordinal position value
    (BuilderLiteralSearchGuard.finalOutside (remaining + 1) outside)
  have hAdvance := BuilderLiteralSearchAdvance.finalOutside_length_le ordinal remaining position value
    (comparedOutside ordinal (remaining + 1) position value outside)
  have hResidual := BuilderLiteralSearchFrame.residual_le position value
  dsimp only [comparedOutside] at hAdvance ⊢
  simp only [BuilderLiteralSearchComparison.initialValues, BuilderLiteralSearchComparison.baseValues,
    registerWord_length, List.length_append, List.sum_append, List.length_cons, List.length_nil,
    List.sum_cons, List.sum_nil]
  omega

private theorem search_bounds {width : Nat} (bound : NatPolynomial) (input : Nat)
    (literals : List (BoundedLiteral width))
    (hLength : literals.length ≤ bound.eval input) (hPayload : (literalListValues literals).sum ≤ bound.eval input)
    (remaining completed : List (BoundedLiteral width)) (hList : literals = completed ++ remaining)
    (prior : List Nat) (hPrior : prior.length = historyStride * completed.length)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (hPosition : position ≤ bound.eval input)
    (hSpan : (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
      completed.length remaining.length position)).length + outside.length ≤ entryBudget (bound.eval input) completed.length) :
    (registerWord (finishValues (literalListValues literals) older remaining completed.length prior position)).length +
      (finishOutside remaining completed.length position outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * searchSteps (literalListValues literals) remaining completed.length prior position ≤
      (remaining.length + 1) * (passRawPolynomial bound).eval input := by
  induction remaining generalizing completed prior position outside with
  | nil =>
      have hOrdinal : completed.length ≤ bound.eval input := by
        rw [hList, List.length_append, List.length_nil, Nat.add_zero] at hLength
        exact hLength
      have hEnvelope := entryBudget_le_envelope bound input completed.length (by omega)
      have hEntry := Nat.le_trans hSpan hEnvelope
      have hGuard := BuilderLiteralSearchGuard.source_polynomial_bounds
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior)
        completed.length 0 position outside (envelope bound) input hEntry
      have hFinal := BuilderLiteralSearchGuard.final_span_le
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior)
        completed.length 0 position outside
      have hNext := entryBudget_le_envelope bound input (completed.length + 1) (by omega)
      rw [entryBudget_step] at hNext
      have hSpace : (registerWord (finishValues (literalListValues literals) older ([] : List (BoundedLiteral width)) completed.length prior position)).length +
          (finishOutside ([] : List (BoundedLiteral width)) completed.length position outside).length ≤ (envelope bound).eval input := by
        change (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
          completed.length 0 position)).length + (BuilderLiteralSearchGuard.finalOutside 0 outside).length ≤ _
        change (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
          completed.length 0 position)).length + (BuilderLiteralSearchGuard.finalOutside 0 outside).length ≤
          (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
          completed.length 0 position)).length + outside.length + 0 + 1 at hFinal
        unfold stepAllowance at hNext
        simp only [List.length_nil] at hSpan
        omega
      constructor
      · change _ ≤ (envelope bound).eval input + (BuilderLiteralSearchSelect.spanPolynomial (envelope bound)).eval input
        omega
      · have hTime := hGuard.2
        simp only [searchSteps, List.length_nil, Nat.zero_add, Nat.one_mul,
          passRawPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
        omega
  | cons item rest ih =>
      have hIndex : completed.length < literals.length := by
        rw [hList, List.length_append, List.length_cons]
        omega
      let index : Fin literals.length := ⟨completed.length, hIndex⟩
      have hLiteral : literals[index.val] = item := by
        change literals[completed.length] = item
        subst literals
        rw [List.getElem_append_right (show completed.length ≤ completed.length from Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
      have hOrdinal : completed.length ≤ bound.eval input := by omega
      have hCount : rest.length + 1 ≤ bound.eval input := by
        rw [hList, List.length_append, List.length_cons] at hLength
        omega
      have hValue : item.index.val ≤ bound.eval input := by
        simpa only [hLiteral] using indexed_value_le literals index (bound.eval input) hPayload
      have hChunk := BuilderLiteralSearchFrame.chunk_word_le completed.length (rest.length + 1) position
        item.index.val (bound.eval input) hOrdinal hCount hPosition hValue
      have hEnvelope := entryBudget_le_envelope bound input completed.length (by omega)
      have hNextEnvelope := entryBudget_le_envelope bound input (completed.length + 1) (by omega)
      have hBudgetNext := entryBudget_step (bound.eval input) completed.length
      have hEntry := Nat.le_trans hSpan hEnvelope
      let guarded := BuilderLiteralSearchGuard.finalOutside (rest.length + 1) outside
      let compared := comparedOutside completed.length (rest.length + 1) position item.index.val outside
      have hGuard := BuilderLiteralSearchGuard.source_polynomial_bounds
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior)
        completed.length (rest.length + 1) position outside (envelope bound) input hEntry
      have hGuardGrowth := BuilderLiteralSearchGuard.final_span_le
        (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior)
        completed.length (rest.length + 1) position outside
      have hGuardSpan :
          (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
            completed.length (rest.length + 1) position)).length + guarded.length ≤
          entryBudget (bound.eval input) completed.length + (rest.length + 2) := by
        change (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
          completed.length (rest.length + 1) position)).length + guarded.length ≤
          (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
          completed.length (rest.length + 1) position)).length + outside.length + (rest.length + 1) + 1 at hGuardGrowth
        simp only [List.length_cons] at hSpan
        omega
      have hCompareInput :
          (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
            completed.length (rest.length + 1) position)).length + guarded.length ≤ (envelope bound).eval input := by
        unfold stepAllowance at hBudgetNext
        omega
      have hCompare := BuilderLiteralSearchComparison.source_polynomial_bounds literals index prior hPrior
        (rest.length + 1) position older guarded (envelope bound) input hCompareInput
      rw [hLiteral] at hCompare
      have hCompareGrowth := BuilderLiteralSearchComparison.final_span_le_initial_add_chunk
        (literalListValues literals) older prior completed.length (rest.length + 1) position item.index.val guarded
      have hComparedInput :
          (registerWord (BuilderLiteralSearchComparison.finalValues (literalListValues literals) older prior
            completed.length (rest.length + 1) position item.index.val)).length + compared.length ≤ (envelope bound).eval input := by
        change (registerWord (BuilderLiteralSearchComparison.finalValues (literalListValues literals) older prior
          completed.length (rest.length + 1) position item.index.val)).length + compared.length ≤
          (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
          completed.length (rest.length + 1) position)).length + guarded.length +
          (registerWord (chunk completed.length (rest.length + 1) position item.index.val)).length at hCompareGrowth
        unfold stepAllowance at hBudgetNext
        omega
      by_cases hHit : position < item.index.val + 2
      · have hSelectInput :
            (registerWord (BuilderLiteralSearchSelect.initialValues (literalListValues literals) older prior index.val
              (rest.length + 1) position literals[index.val].index.val)).length + compared.length ≤ (envelope bound).eval input := by
          simpa only [hLiteral, index, BuilderLiteralSearchSelect.initialValues, BuilderLiteralSearchSelect.baseValues,
            BuilderLiteralSearchComparison.finalValues, BuilderLiteralSearchComparison.baseValues] using hComparedInput
        have hSelect := BuilderLiteralSearchSelect.source_polynomial_bounds literals index prior hPrior
          (rest.length + 1) position older compared (envelope bound) input hSelectInput
        rw [hLiteral] at hSelect
        constructor
        · simp only [finishValues, finishOutside, if_pos hHit]
          change _ ≤ (envelope bound).eval input + (BuilderLiteralSearchSelect.spanPolynomial (envelope bound)).eval input
          exact Nat.le_trans hSelect.1 (Nat.le_add_left _ _)
        · have hG := hGuard.2
          have hC := hCompare.2
          have hS := hSelect.2
          have hPass :
              6 * BuilderLiteralSearchGuard.workSteps (rest.length + 1) position +
              6 * BuilderLiteralSearchComparison.workSteps (literalListValues literals) prior completed.length
                (rest.length + 1) position item.index.val +
              6 * BuilderLiteralSearchSelect.workSteps (literalListValues literals) prior completed.length
                (rest.length + 1) position item.index.val item.positive + 18 ≤ (passRawPolynomial bound).eval input := by
            simp only [passRawPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
            dsimp only [index] at hC hS
            omega
          have hMore := Nat.mul_le_mul_right ((passRawPolynomial bound).eval input)
            (show 1 ≤ (item :: rest).length + 1 by simp only [List.length_cons]; omega)
          simp only [Nat.one_mul] at hMore
          simp only [searchSteps, if_pos hHit]
          omega
      · have hAdvance := BuilderLiteralSearchAdvance.source_polynomial_bounds
          (BuilderLiteralSearchComparison.baseValues (literalListValues literals) older prior) completed.length rest.length
          position item.index.val compared (envelope bound) input hComparedInput
        have hNextList : literals = (completed ++ [item]) ++ rest := by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hList
        have hNextPrior : (prior ++ chunk completed.length (rest.length + 1) position item.index.val).length =
            historyStride * (completed ++ [item]).length := by
          simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using
            BuilderLiteralSearchFrame.history_step prior completed.length (rest.length + 1) position item.index.val hPrior
        have hNextPosition : residual position item.index.val ≤ bound.eval input :=
          Nat.le_trans (BuilderLiteralSearchFrame.residual_le position item.index.val) hPosition
        have hNextSpan :
            (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older
              (prior ++ chunk completed.length (rest.length + 1) position item.index.val)
              (completed ++ [item]).length rest.length (residual position item.index.val))).length +
            (BuilderLiteralSearchAdvance.finalOutside completed.length rest.length position item.index.val compared).length ≤
              entryBudget (bound.eval input) (completed ++ [item]).length := by
          have hNext := continued_span (literalListValues literals) older prior completed.length rest.length position item.index.val outside
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
          unfold stepAllowance at hBudgetNext
          simp only [List.length_cons] at hSpan
          change (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older
            (prior ++ chunk completed.length (rest.length + 1) position item.index.val)
            (completed.length + 1) rest.length (residual position item.index.val))).length +
            (BuilderLiteralSearchAdvance.finalOutside completed.length rest.length position item.index.val compared).length ≤
            (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older prior
            completed.length (rest.length + 1) position)).length + outside.length +
              (registerWord (chunk completed.length (rest.length + 1) position item.index.val)).length + (rest.length + 2) at hNext
          omega
        have hTail := ih (completed ++ [item]) hNextList
          (prior ++ chunk completed.length (rest.length + 1) position item.index.val) hNextPrior
          (residual position item.index.val)
          (BuilderLiteralSearchAdvance.finalOutside completed.length rest.length position item.index.val compared)
          hNextPosition hNextSpan
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hTail
        constructor
        · simpa only [finishValues, finishOutside, if_neg hHit] using hTail.1
        · have hG := hGuard.2
          have hC := hCompare.2
          have hA := hAdvance.2
          have hPass :
              6 * BuilderLiteralSearchGuard.workSteps (rest.length + 1) position +
              6 * BuilderLiteralSearchComparison.workSteps (literalListValues literals) prior completed.length
                (rest.length + 1) position item.index.val +
              6 * BuilderLiteralSearchAdvance.workSteps completed.length rest.length position item.index.val + 18 ≤
                (passRawPolynomial bound).eval input := by
            simp only [passRawPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
            dsimp only [index] at hC
            omega
          have hTime := hTail.2
          simp only [searchSteps, if_neg hHit, List.length_cons]
          rw [Nat.add_mul, Nat.one_mul]
          omega

theorem source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderLiteralListSearch.initialValues literals position older)).length + outside.length ≤ bound.eval input) :
    (registerWord (BuilderLiteralListSearch.finalValues literals position older)).length +
      (BuilderLiteralListSearch.finalOutside literals position outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * BuilderLiteralListSearch.workSteps literals position ≤ (rawTimePolynomial bound).eval input := by
  have hScalars := hSpan
  simp only [BuilderLiteralListSearch.initialValues, registerWord_length, List.length_append, List.sum_append,
    List.length_reverse, List.sum_reverse, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hScalars
  have hLength : literals.length ≤ bound.eval input := by omega
  have hPayload : (literalListValues literals).sum ≤ bound.eval input := by omega
  have hPosition : position ≤ bound.eval input := by omega
  have hEntry :
      (registerWord (BuilderLiteralSearchComparison.initialValues (literalListValues literals) older []
        0 literals.length position)).length + outside.length ≤ entryBudget (bound.eval input) 0 := by
    simpa only [BuilderLiteralListSearch.initialValues, BuilderLiteralSearchComparison.initialValues,
      BuilderLiteralSearchComparison.baseValues, List.append_nil, entryBudget, Nat.zero_mul, Nat.add_zero] using hSpan
  have h := search_bounds bound input literals hLength hPayload literals [] rfl [] rfl position older outside hPosition hEntry
  constructor
  · exact h.1
  · have hMore := Nat.mul_le_mul_right ((passRawPolynomial bound).eval input) (Nat.add_le_add_right hLength 1)
    exact Nat.le_trans h.2 hMore

/-- One fixed raw machine performs the actual canonical lookup within one source polynomial. -/
theorem uniform_polynomial_lookup {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderLiteralListSearch.initialValues literals position older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine BuilderLiteralListSearch.machine) rawSteps
        (encodeWorkConfiguration (BuilderLiteralListSearch.initialConfiguration literals position older inside outside)) =
        encodeWorkConfiguration (BuilderLiteralListSearch.finalConfiguration literals position older inside outside) ∧
      BuilderLiteralListSearch.observe (BuilderLiteralListSearch.finalConfiguration literals position older inside outside) =
        DirectToken.boundedLiteralListSlot literals position := by
  have hBound := source_polynomial_bounds literals position older outside bound input hSpan
  exact ⟨6 * BuilderLiteralListSearch.workSteps literals position, hBound.2,
    BuilderLiteralListSearch.run_compile_exact literals position older inside outside,
    BuilderLiteralListSearch.canonical_result literals position older inside outside⟩

end PNP.Concrete.CookLevin.BuilderLiteralListSearchBounds
