/-
Copyright (c) 2026 PNP Labs.

Complete source-body search has one original-input polynomial time and final
space bound. Cost evidence is constructed by the actual execution proof, then
bounded by induction over its decreasing count. No trace or bound certificate
is supplied to the runtime machine.
-/
import PNP.Concrete.CookLevinBuilderPayloadSourceSearch
import PNP.Concrete.CookLevinBuilderPayloadSourceSearchEnvelope

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBounds

open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource
open BuilderPayloadSourceSearch (CostVisit costVisit CostTrace)
open BuilderPayloadSourceSearchControl (graph guardNode graph_wellFormed guardedOutside guardSteps)
open BuilderPayloadSourceSearchEnvelope
open BuilderLiteralSearchFrame (residual)
open BuilderLocalConstraintPayload (front)
open WorkMachineProgramGraph (endpointConfiguration)

/-- Each nonempty visit is bounded at the same original-input envelope, and a
miss advances only one linear retained-space allowance. -/
theorem visit_bounds {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (ordinal remaining : Nat) (prior : List Nat)
    (hIndex : ordinal < (body constraint).length) (hPrior : prior.length = 17 * ordinal)
    (position : Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hLength : (body constraint).length ≤ bound.eval input)
    (hPayload : (front (some (some constraint))).sum ≤ bound.eval input)
    (hBalance : ordinal + (remaining + 1) = (body constraint).length)
    (hPosition : position ≤ bound.eval input)
    (hSpan : (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length +
      outside.length ≤ entryBudget (bound.eval input) ordinal) :
    let visit := costVisit constraint request older ordinal remaining prior hIndex hPrior position outside
    (registerWord visit.hitValues).length + visit.hitOutside.length ≤ (spanPolynomial bound).eval input ∧
    6 * visit.hitSteps ≤ (passRawPolynomial bound).eval input ∧
    6 * visit.missSteps ≤ (passRawPolynomial bound).eval input ∧
    visit.nextPosition ≤ position ∧
    (registerWord (initialValues constraint request older visit.nextPrior (ordinal + 1) remaining visit.nextPosition)).length +
      visit.nextOutside.length ≤ entryBudget (bound.eval input) (ordinal + 1) := by
  let index : Fin (body constraint).length := ⟨ordinal,hIndex⟩
  let source := atSource constraint index
  let ctx := context constraint index request prior hPrior (remaining + 1) position
  let value := source.originalLiteral.index.val
  let guarded := guardedOutside (remaining + 1) outside
  let compared := BuilderPayloadSearchComparison.finalOutside source ctx guarded
  let middle := BuilderPayloadSearchComparison.cursorMiddle source.kind ordinal position value
  let nextOutside := BuilderPayloadSearchAdvance.finalOutside ordinal remaining (residual position value) compared
  have hOrdinal : ordinal ≤ bound.eval input := by omega
  have hCount : remaining + 1 ≤ bound.eval input := by omega
  have hValue : value ≤ bound.eval input := atSource_value_bound constraint index _ hPayload
  have hSourceOrdinal : source.ordinal = ordinal := atSource_ordinal constraint index
  have hInitial : BuilderPayloadLiteralTokenSelector.initialValues source ctx older =
      initialValues constraint request older prior ordinal (remaining + 1) position :=
    context_initial_values constraint index request prior hPrior (remaining + 1) position older
  have hBase : BuilderPayloadSearchComparison.baseValues source ctx older = baseValues constraint request older prior :=
    context_base_values constraint index request prior hPrior (remaining + 1) position older
  have hRoom := budget_room bound input ordinal hOrdinal
  have hEnvelope := entryBudget_le_envelope bound input ordinal (by omega)
  have hEntry := Nat.le_trans hSpan hEnvelope
  have hZeroGrowth := BuilderLiteralSearchGuard.finalOutside_length_le (remaining + 1) outside
  have hGuardGrowth := guardedOutside_length_le (remaining + 1) outside
  have hZeroInput :
      (registerWord (baseValues constraint request older prior ++ BuilderLiteralSearchGuard.frame ordinal (remaining + 1) position)).length +
        outside.length ≤ (envelope bound).eval input := by
    simpa only [BuilderLiteralSearchGuard.frame, initialValues] using hEntry
  have hZero := BuilderLiteralSearchGuard.source_polynomial_bounds
    (baseValues constraint request older prior) ordinal (remaining + 1) position outside (envelope bound) input hZeroInput
  have hOneInput :
      (registerWord (baseValues constraint request older prior ++ BuilderPayloadConclusionGuard.frame ordinal (remaining + 1) position)).length +
        (BuilderLiteralSearchGuard.finalOutside (remaining + 1) outside).length ≤ (envelope bound).eval input := by
    change (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length + _ ≤ _
    unfold stepAllowance at hRoom
    omega
  have hOne := BuilderPayloadConclusionGuard.source_polynomial_bounds
    (baseValues constraint request older prior) ordinal (remaining + 1) position
    (BuilderLiteralSearchGuard.finalOutside (remaining + 1) outside) (envelope bound) input hOneInput
  have hGuardBudget :
      (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length + guarded.length ≤
        entryBudget (bound.eval input) ordinal + 2 * (remaining + 1) + 2 := by
    dsimp only [guarded]
    omega
  have hAfterGuards :
      (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length + guarded.length ≤
        (envelope bound).eval input := by
    unfold stepAllowance at hRoom
    omega
  have hCompareInput :
      (registerWord (BuilderPayloadSearchComparison.initialValues source ctx older)).length + guarded.length ≤
        (envelope bound).eval input := by
    simpa only [BuilderPayloadSearchComparison.initialValues, hInitial] using hAfterGuards
  have hCompare := BuilderPayloadSearchComparison.source_polynomial_bounds source ctx older guarded (envelope bound) input hCompareInput
  have hChunk := chunk_word_bound source.kind ordinal (remaining + 1) position value (bound.eval input)
    hOrdinal hCount hPosition hValue
  have hCompareGrowth := BuilderPayloadSearchComparison.final_span_le_initial_add_chunk source ctx older guarded
  rw [BuilderPayloadSearchComparison.initialValues, hInitial] at hCompareGrowth
  have hSourceChunk :
      (registerWord (BuilderPayloadSearchComparison.chunk source.kind source.ordinal ctx.remaining ctx.position source.originalLiteral.index.val)).length ≤
        50 * bound.eval input + 90 := by
    simpa only [hSourceOrdinal, ctx, context, value] using hChunk
  have hComparedInput :
      (registerWord (BuilderPayloadSearchComparison.finalValues source ctx older)).length + compared.length ≤ (envelope bound).eval input := by
    change (registerWord (BuilderPayloadSearchComparison.finalValues source ctx older)).length + compared.length ≤
      (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length + guarded.length +
        (registerWord (BuilderPayloadSearchComparison.chunk source.kind source.ordinal ctx.remaining ctx.position source.originalLiteral.index.val)).length at hCompareGrowth
    unfold stepAllowance at hRoom
    omega
  have hHitInput :
      (registerWord (BuilderPayloadSearchHit.initialValues source ctx older)).length + compared.length ≤ (envelope bound).eval input :=
    hComparedInput
  have hHit := BuilderPayloadSearchHit.source_polynomial_bounds source ctx older compared (envelope bound) input hHitInput
  have hAdvanceInput : BuilderPayloadSearchAdvance.initialValues (baseValues constraint request older prior)
      middle ordinal remaining (residual position value) = BuilderPayloadSearchComparison.finalValues source ctx older := by
    rw [BuilderPayloadSearchComparison.finalValues, hBase]
    simp only [BuilderPayloadSearchAdvance.initialValues, hSourceOrdinal, ctx, context, value,
      BuilderPayloadSearchComparison.chunk_cursor_layout, middle, List.append_assoc]
  have hAdvanceSpan :
      (registerWord (BuilderPayloadSearchAdvance.initialValues (baseValues constraint request older prior)
        middle ordinal remaining (residual position value))).length + compared.length ≤ (envelope bound).eval input := by
    rw [hAdvanceInput]
    exact hComparedInput
  have hAdvance := BuilderPayloadSearchAdvance.source_polynomial_bounds
    (baseValues constraint request older prior) middle ordinal remaining (residual position value) compared (envelope bound) input hAdvanceSpan
  have hCompareTime := Nat.le_trans hCompare.2
    (kind_le_sum (fun kind => BuilderPayloadSearchComparison.rawTimePolynomial kind (envelope bound)) source.kind input)
  have hHitTime := Nat.le_trans hHit.2
    (kind_le_sum (fun kind => BuilderPayloadSearchHit.rawTimePolynomial kind (envelope bound)) source.kind input)
  have hHitSpace := Nat.le_trans hHit.1
    (kind_le_sum (fun kind => BuilderPayloadSearchHit.spanPolynomial kind (envelope bound)) source.kind input)
  have hCompareExterior := comparisonOutside_length_le source ctx outside
  have hAdvanceExterior := BuilderPayloadSearchAdvance.finalOutside_length_le ordinal remaining (residual position value) compared
  have hExterior : nextOutside.length ≤ outside.length + 2 * (remaining + 1) + 2 := by
    change compared.length ≤ outside.length + 2 * (remaining + 1) + 2 at hCompareExterior
    dsimp only [nextOutside]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (registerWord (BuilderPayloadSearchHit.finalValues source ctx older)).length +
      (BuilderPayloadSearchHit.finalOutside source ctx compared).length ≤ _
    change _ ≤ (envelope bound).eval input +
      (kindSum fun kind => BuilderPayloadSearchHit.spanPolynomial kind (envelope bound)).eval input
    omega
  · change 6 * (guardSteps (remaining + 1) position +
      (BuilderPayloadSearchComparison.workSteps source ctx + 1 + (BuilderPayloadSearchHit.workSteps source ctx + 1))) ≤ _
    simp only [guardSteps, passRawPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, Nat.mul_add, Nat.mul_one]
    omega
  · change 6 * (guardSteps (remaining + 1) position +
      (BuilderPayloadSearchComparison.workSteps source ctx + 1 +
        (BuilderPayloadSearchAdvance.workSteps middle ordinal remaining (residual position value) + 1))) ≤ _
    simp only [guardSteps, passRawPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, Nat.mul_add, Nat.mul_one]
    omega
  · exact BuilderLiteralSearchFrame.residual_le position value
  · exact continued_budget constraint request older prior source.kind ordinal remaining position value
      (bound.eval input) outside nextOutside hOrdinal hCount hPosition hValue hSpan hExterior

/-- The finite trace is generated by the execution proof. Its remaining count
strictly decreases on each miss, so the per-visit polynomial is summed, not iterated. -/
theorem trace_bounds {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (bound : NatPolynomial) (input : Nat)
    (ordinal count : Nat) (prior : List Nat) (position : Nat) (outside : List WorkSymbol)
    (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol)
    (hTrace : CostTrace constraint request older ordinal count prior position outside steps resultValues resultOutside)
    (hLength : (body constraint).length ≤ bound.eval input)
    (hPayload : (front (some (some constraint))).sum ≤ bound.eval input)
    (hBalance : ordinal + count = (body constraint).length)
    (hPosition : position ≤ bound.eval input)
    (hSpan : (registerWord (initialValues constraint request older prior ordinal count position)).length + outside.length ≤
      entryBudget (bound.eval input) ordinal) :
    (registerWord resultValues).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (count + 1) * (passRawPolynomial bound).eval input := by
  revert hBalance hPosition hSpan
  induction hTrace with
  | empty ordinal prior position outside =>
      intro hBalance hPosition hSpan
      have hOrdinal : ordinal ≤ bound.eval input := by omega
      have hEnvelope := entryBudget_le_envelope bound input ordinal (by omega)
      have hRoom := budget_room bound input ordinal hOrdinal
      have hEntry :
          (registerWord (baseValues constraint request older prior ++ BuilderLiteralSearchGuard.frame ordinal 0 position)).length +
            outside.length ≤ (envelope bound).eval input := by
        simpa only [initialValues, BuilderLiteralSearchGuard.frame] using Nat.le_trans hSpan hEnvelope
      have hGuard := BuilderLiteralSearchGuard.source_polynomial_bounds
        (baseValues constraint request older prior) ordinal 0 position outside (envelope bound) input hEntry
      have hGrowth := BuilderLiteralSearchGuard.finalOutside_length_le 0 outside
      constructor
      · change _ ≤ (envelope bound).eval input +
          (kindSum fun kind => BuilderPayloadSearchHit.spanPolynomial kind (envelope bound)).eval input
        unfold stepAllowance at hRoom
        omega
      · simp only [Nat.zero_add, Nat.one_mul, passRawPolynomial, NatPolynomial.eval_add,
          NatPolynomial.eval_constant, Nat.mul_add, Nat.mul_one]
        omega
  | hit ordinal remaining prior hIndex hPrior position outside =>
      intro hBalance hPosition hSpan
      have hVisit := visit_bounds constraint request older ordinal remaining prior hIndex hPrior
        position outside bound input hLength hPayload hBalance hPosition hSpan
      refine ⟨hVisit.1, ?_⟩
      have hAllowance : (passRawPolynomial bound).eval input ≤
          (remaining + 1 + 1) * (passRawPolynomial bound).eval input := by
        have h := Nat.mul_le_mul_right ((passRawPolynomial bound).eval input) (show 1 ≤ remaining + 1 + 1 from by omega)
        simpa only [Nat.one_mul] using h
      exact Nat.le_trans hVisit.2.1 hAllowance
  | miss ordinal remaining prior hIndex hPrior position outside tailSteps resultValues resultOutside hTail ih =>
      intro hBalance hPosition hSpan
      have hVisit := visit_bounds constraint request older ordinal remaining prior hIndex hPrior
        position outside bound input hLength hPayload hBalance hPosition hSpan
      have hTailBounds := ih (by omega) (Nat.le_trans hVisit.2.2.2.1 hPosition) hVisit.2.2.2.2
      refine ⟨hTailBounds.1, ?_⟩
      have hMissTime := hVisit.2.2.1
      have hTailTime := hTailBounds.2
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] at hTailTime ⊢
      omega

/-- Both the exact canonical execution and its bound are derived from the actual
input. No cost trace, selected literal or branch certificate is a premise. -/
theorem source_polynomial_bounds {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request older [] 0 (body constraint).length position)).length +
      outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol),
      workRunExact? (BuilderPayloadSourceSearchControl.machine (family constraint)) steps
        (workStartConfiguration (BuilderPayloadSourceSearchControl.machine (family constraint))
          (endTape (initialValues constraint request older [] 0 (body constraint).length position) inside outside)) =
        some (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
          (endTape resultValues inside resultOutside)) ∧
      BuilderLiteralTokenSelector.observe
        (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
          (endTape resultValues inside resultOutside)) =
        DirectToken.boundedLiteralListSlot (body constraint) position ∧
      (∃ scratch, resultValues = requestValues constraint request older ++ scratch) ∧
      (BuilderLiteralListSearch.endpoint (body constraint) position = .dead →
        ∃ finalPrior, finalPrior.length = 17 * (body constraint).length ∧
          resultValues = initialValues constraint request older finalPrior (body constraint).length 0
            (position - DirectToken.boundedLiteralListWidth (body constraint))) ∧
      (registerWord resultValues).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  obtain ⟨steps, resultValues, resultOutside, hTrace, hPath, hRetained, hExhausted⟩ :=
    BuilderPayloadSourceSearch.loop_path_traced (body constraint) constraint [] rfl request [] rfl position older inside outside
  have hScalars := initial_scalar_bounds constraint request position older outside (bound.eval input) hSpan
  have hInitialBudget :
      (registerWord (initialValues constraint request older [] 0 (body constraint).length position)).length +
        outside.length ≤ entryBudget (bound.eval input) 0 := by
    simpa only [entryBudget, Nat.zero_mul, Nat.add_zero] using hSpan
  have hBounds := trace_bounds constraint request older bound input 0 (body constraint).length [] position outside
    steps resultValues resultOutside hTrace hScalars.1 hScalars.2.1 (by omega) hScalars.2.2 hInitialBudget
  have hRun := WorkMachineProgramPath.runExact (graph (family constraint)) _ _ _ _ _
    (graph_wellFormed (family constraint)) hPath
  refine ⟨steps, resultValues, resultOutside, ?_, ?_, hRetained, hExhausted, hBounds.1, ?_⟩
  · exact hRun
  · exact BuilderLiteralListSearch.endpoint_observes_list (body constraint) position _
  · have hCount := Nat.add_le_add_right hScalars.1 1
    have h := Nat.le_trans hBounds.2 (Nat.mul_le_mul_right ((passRawPolynomial bound).eval input) hCount)
    simpa only [rawTimePolynomial, NatPolynomial.eval_mul, NatPolynomial.eval_add, NatPolynomial.eval_constant] using h

/-- The total bound applies to the actual compiled raw machine as well. -/
theorem run_compile_polynomial_bound {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request older [] 0 (body constraint).length position)).length +
      outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol),
      run (compileWorkMachine (BuilderPayloadSourceSearchControl.machine (family constraint))) (6 * steps)
        (encodeWorkConfiguration
          (workStartConfiguration (BuilderPayloadSourceSearchControl.machine (family constraint))
            (endTape (initialValues constraint request older [] 0 (body constraint).length position) inside outside))) =
        encodeWorkConfiguration
          (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
            (endTape resultValues inside resultOutside)) ∧
      BuilderLiteralTokenSelector.observe
        (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
          (endTape resultValues inside resultOutside)) =
        DirectToken.boundedLiteralListSlot (body constraint) position ∧
      (∃ scratch, resultValues = requestValues constraint request older ++ scratch) ∧
      (BuilderLiteralListSearch.endpoint (body constraint) position = .dead →
        ∃ finalPrior, finalPrior.length = 17 * (body constraint).length ∧
          resultValues = initialValues constraint request older finalPrior (body constraint).length 0
            (position - DirectToken.boundedLiteralListWidth (body constraint))) ∧
      (registerWord resultValues).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  obtain ⟨steps, resultValues, resultOutside, hRun, hToken, hRetained, hExhausted, hSpace, hTime⟩ :=
    source_polynomial_bounds constraint request position older inside outside bound input hSpan
  exact ⟨steps, resultValues, resultOutside, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun,
    hToken, hRetained, hExhausted, hSpace, hTime⟩

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBounds
