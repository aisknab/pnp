/-
Copyright (c) 2026 PNP Labs.

Whole-body execution for the fixed source-search graph. The induction derives
every literal adapter from the actual source body and the physical count
invariant. No selected literal, branch verdict or execution certificate is a
runtime input.

This establishes complete body-search execution and source retention. The
single original-input polynomial envelope, clause wrapper and outer source
dispatch remain separate obligations before complete-builder credit.
-/
import PNP.Concrete.CookLevinBuilderPayloadSourceSearchControl

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearch

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource
open BuilderPayloadSourceSearchControl
open BuilderLiteralSearchFrame (residual)
open WorkMachineProgramGraph (Endpoint endpointConfiguration)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

/-- Data computed from an actual source ordinal for cost accounting only. It
does not choose or construct the runtime machine. -/
structure CostVisit where
  hitSteps : Nat
  hitValues : List Nat
  hitOutside : List WorkSymbol
  missSteps : Nat
  nextPrior : List Nat
  nextPosition : Nat
  nextOutside : List WorkSymbol

def costVisit {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (ordinal remaining : Nat) (prior : List Nat)
    (hIndex : ordinal < (body constraint).length) (hPrior : prior.length = 17 * ordinal)
    (position : Nat) (outside : List WorkSymbol) : CostVisit :=
  let index : Fin (body constraint).length := ⟨ordinal,hIndex⟩
  let source := atSource constraint index
  let ctx := context constraint index request prior hPrior (remaining + 1) position
  let value := source.originalLiteral.index.val
  let visitChunk := BuilderPayloadSearchComparison.chunk source.kind ordinal (remaining + 1) position value
  let middle := BuilderPayloadSearchComparison.cursorMiddle source.kind ordinal position value
  let compared := BuilderPayloadSearchComparison.finalOutside source ctx (guardedOutside (remaining + 1) outside)
  {hitSteps := guardSteps (remaining + 1) position +
      (BuilderPayloadSearchComparison.workSteps source ctx + 1 + (BuilderPayloadSearchHit.workSteps source ctx + 1)),
   hitValues := BuilderPayloadSearchHit.finalValues source ctx older,
   hitOutside := BuilderPayloadSearchHit.finalOutside source ctx compared,
   missSteps := guardSteps (remaining + 1) position +
      (BuilderPayloadSearchComparison.workSteps source ctx + 1 +
        (BuilderPayloadSearchAdvance.workSteps middle ordinal remaining (residual position value) + 1)),
   nextPrior := prior ++ visitChunk, nextPosition := residual position value,
   nextOutside := BuilderPayloadSearchAdvance.finalOutside ordinal remaining (residual position value) compared}

/-- Internally produced cost evidence for the complete loop. The three cases
overapproximate branch costs; they are not a correctness certificate or an
additional runtime input. Every read still comes from an actual source ordinal. -/
inductive CostTrace {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat) :
    Nat → Nat → List Nat → Nat → List WorkSymbol → Nat → List Nat → List WorkSymbol → Prop where
  | empty (ordinal : Nat) (prior : List Nat) (position : Nat) (outside : List WorkSymbol) :
      CostTrace constraint request older ordinal 0 prior position outside
        (BuilderLiteralSearchGuard.workSteps 0 position + 1)
        (initialValues constraint request older prior ordinal 0 position)
        (BuilderLiteralSearchGuard.finalOutside 0 outside)
  | hit (ordinal remaining : Nat) (prior : List Nat)
      (hIndex : ordinal < (body constraint).length) (hPrior : prior.length = 17 * ordinal)
      (position : Nat) (outside : List WorkSymbol) :
      CostTrace constraint request older ordinal (remaining + 1) prior position outside
        (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).hitSteps
        (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).hitValues
        (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).hitOutside
  | miss (ordinal remaining : Nat) (prior : List Nat)
      (hIndex : ordinal < (body constraint).length) (hPrior : prior.length = 17 * ordinal)
      (position : Nat) (outside : List WorkSymbol)
      (tailSteps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol)
      (hTail : CostTrace constraint request older (ordinal + 1) remaining
        (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).nextPrior
        (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).nextPosition
        (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).nextOutside
        tailSteps resultValues resultOutside) :
      CostTrace constraint request older ordinal (remaining + 1) prior position outside
        ((costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).missSteps + tailSteps)
        resultValues resultOutside

private theorem append_index {width : Nat} (completed : List (BoundedLiteral width))
    (item : BoundedLiteral width) (rest : List (BoundedLiteral width)) :
    (completed ++ item :: rest)[completed.length]'(by
      simp only [List.length_append, List.length_cons]; omega) = item := by
  rw [List.getElem_append_right (show completed.length ≤ completed.length from Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem_cons_zero]

/-- Internal complete-list invariant. The outer theorem starts with the actual
body, empty history and zero ordinal, rather than accepting this decomposition
as a replacement source or a route certificate. -/
theorem loop_path_traced {width : Nat} (remaining : List (BoundedLiteral width))
    (constraint : LocalConstraint width) (completed : List (BoundedLiteral width))
    (hList : body constraint = completed ++ remaining)
    (request : Request) (prior : List Nat) (hPrior : prior.length = 17 * completed.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    ∃ (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol),
      CostTrace constraint request older completed.length remaining.length prior position outside steps resultValues resultOutside ∧
      AcceptPath (graph (family constraint)) (.node (guardNode (family constraint)).reference)
        (BuilderLiteralListSearch.endpoint remaining position) steps
        (endTape (initialValues constraint request older prior completed.length remaining.length position) inside outside)
        (endTape resultValues inside resultOutside) ∧
      (∃ scratch, resultValues = requestValues constraint request older ++ scratch) ∧
      (BuilderLiteralListSearch.endpoint remaining position = .dead →
        ∃ finalPrior, finalPrior.length = 17 * (body constraint).length ∧
          resultValues = initialValues constraint request older finalPrior (body constraint).length 0
            (position - DirectToken.boundedLiteralListWidth remaining)) := by
  induction remaining generalizing completed prior position outside with
  | nil =>
      let resultOutside := BuilderLiteralSearchGuard.finalOutside 0 outside
      have hRun := BuilderLiteralSearchGuard.workRunExact
        (baseValues constraint request older prior) completed.length 0 position inside outside
      have hState := (BuilderLiteralSearchGuard.final_accept_iff
        (baseValues constraint request older prior) completed.length 0 position inside outside).2 rfl
      have hTape := BuilderLiteralSearchGuard.final_tape
        (baseValues constraint request older prior) completed.length 0 position inside outside
      rw [configuration_eq_of_fields _ _ _ hState hTape] at hRun
      have hPath := AcceptPath.step (guardNode (family constraint)) .dead _ 0 _ _ _
        (guard_mem (family constraint)) hRun (.terminal .dead _)
      refine ⟨BuilderLiteralSearchGuard.workSteps 0 position + 1,
        initialValues constraint request older prior completed.length 0 position, resultOutside, ?_, ?_, ?_, ?_⟩
      · exact CostTrace.empty completed.length prior position outside
      · simpa only [BuilderLiteralListSearch.endpoint, initialValues,
          BuilderLiteralSearchGuard.frame, List.length_nil, Nat.add_zero, resultOutside] using hPath
      · exact ⟨prior ++ [completed.length,0,position], by
          simp only [initialValues, baseValues, List.append_assoc]⟩
      · intro _
        have hLength : (body constraint).length = completed.length := by
          rw [hList, List.append_nil]
        refine ⟨prior, ?_, ?_⟩
        · rw [hLength]
          exact hPrior
        · simp only [hLength, DirectToken.boundedLiteralListWidth, Nat.sub_zero]
  | cons item rest ih =>
      have hIndex : completed.length < (body constraint).length := by
        rw [hList, List.length_append, List.length_cons]
        omega
      let index : Fin (body constraint).length := ⟨completed.length, hIndex⟩
      have hLiteral : (body constraint)[index.val] = item := by
        change (body constraint)[completed.length] = item
        simpa only [hList] using append_index completed item rest
      let source := atSource constraint index
      let ctx := context constraint index request prior hPrior (rest.length + 1) position
      have hSelected : source.selectedLiteral = item := by
        dsimp only [source]
        rw [atSource_selected, hLiteral]
      have hValue : source.originalLiteral.index.val = item.index.val := by
        dsimp only [source]
        rw [atSource_original_index, hLiteral]
      have hOrdinal : source.ordinal = completed.length := atSource_ordinal constraint index
      have hKind : source.kind = visitKind (family constraint) (lastFlag (rest.length + 1)) := by
        rw [visitKind_lastFlag]
        apply atSource_kind
        change completed.length + (rest.length + 1) = (body constraint).length
        rw [hList, List.length_append, List.length_cons]
      have hInput : BuilderPayloadSearchComparison.initialValues source ctx older =
          initialValues constraint request older prior completed.length (rest.length + 1) position :=
        context_initial_values constraint index request prior hPrior (rest.length + 1) position older
      have hBase : BuilderPayloadSearchComparison.baseValues source ctx older =
          baseValues constraint request older prior :=
        context_base_values constraint index request prior hPrior (rest.length + 1) position older
      let guarded := guardedOutside (rest.length + 1) outside
      let compared := BuilderPayloadSearchComparison.finalOutside source ctx guarded
      have hCompare := BuilderPayloadSearchComparison.workRunExact source ctx older inside guarded
      have hCompareTape := BuilderPayloadSearchComparison.final_tape source ctx older inside guarded
      by_cases hHit : position < item.index.val + 2
      · have hSourceHit : ctx.position < source.originalLiteral.index.val + 2 := by
          simpa only [ctx, context, hValue] using hHit
        have hState := (BuilderPayloadSearchComparison.final_accept_iff source ctx older inside guarded).2 hSourceHit
        rw [configuration_eq_of_fields _ _ _ hState hCompareTape] at hCompare
        have hLocal : LocalAcceptRun (compareNode (family constraint) (lastFlag (rest.length + 1)))
            (BuilderPayloadSearchComparison.workSteps source ctx)
            (endTape (initialValues constraint request older prior completed.length (rest.length + 1) position) inside guarded)
            (endTape (BuilderPayloadSearchComparison.finalValues source ctx older) inside compared) := by
          unfold LocalAcceptRun
          rw [compare_program, ← hKind]
          simpa only [BuilderPayloadSearchComparison.initialConfiguration, workStartConfiguration, hInput, compared] using hCompare
        have hHitPath := hit_path (family constraint) (lastFlag (rest.length + 1))
          source ctx older inside compared hKind hSourceHit
        rw [hSelected, hValue, BuilderPayloadSearchHit.final_tape] at hHitPath
        have hContinuation : AcceptPath (graph (family constraint))
            (compareNode (family constraint) (lastFlag (rest.length + 1))).onAccept
            (BuilderLiteralTokenSelector.endpoint item.positive item.index.val position)
            (BuilderPayloadSearchHit.workSteps source ctx + 1)
            (endTape (BuilderPayloadSearchComparison.finalValues source ctx older) inside compared)
            (endTape (BuilderPayloadSearchHit.finalValues source ctx older) inside
              (BuilderPayloadSearchHit.finalOutside source ctx compared)) := by
          rw [compare_accept]
          exact hHitPath
        have hPath := AcceptPath.step (compareNode (family constraint) (lastFlag (rest.length + 1))) _ _ _ _ _ _
          (compare_mem _ _) hLocal hContinuation
        have hWhole := guards_path (family constraint) (baseValues constraint request older prior)
          completed.length (rest.length + 1) position inside outside _ _ _ (by omega) hPath
        refine ⟨guardSteps (rest.length + 1) position +
          (BuilderPayloadSearchComparison.workSteps source ctx + 1 +
            (BuilderPayloadSearchHit.workSteps source ctx + 1)), BuilderPayloadSearchHit.finalValues source ctx older,
          BuilderPayloadSearchHit.finalOutside source ctx compared, ?_, ?_, ?_, ?_⟩
        · exact CostTrace.hit completed.length rest.length prior hIndex hPrior position outside
        · simpa only [BuilderLiteralListSearch.endpoint, if_pos hHit, List.length_cons, initialValues] using hWhole
        · obtain ⟨scratch, hScratch⟩ := BuilderPayloadSearchHit.original_frame_preserved source ctx older
          refine ⟨prior ++ [completed.length,rest.length + 1,position] ++ scratch, ?_⟩
          rw [hScratch]
          have hOriginal := context_initial_values constraint index request prior hPrior (rest.length + 1) position older
          rw [hOriginal]
          simp only [initialValues, baseValues, List.append_assoc, index]
        · intro hDead
          simp only [BuilderLiteralListSearch.endpoint, if_pos hHit] at hDead
          rcases literal_endpoint_terminal item.positive item.index.val position hHit with hAccept | hReject
          · rw [hAccept] at hDead
            cases hDead
          · rw [hReject] at hDead
            cases hDead
      · have hSourceMiss : source.originalLiteral.index.val + 2 ≤ ctx.position := by
          simp only [ctx, context, hValue]
          omega
        have hState := (BuilderPayloadSearchComparison.final_reject_iff source ctx older inside guarded).2 hSourceMiss
        rw [configuration_eq_of_fields _ _ _ hState hCompareTape] at hCompare
        have hLocal : LocalRejectRun (compareNode (family constraint) (lastFlag (rest.length + 1)))
            (BuilderPayloadSearchComparison.workSteps source ctx)
            (endTape (initialValues constraint request older prior completed.length (rest.length + 1) position) inside guarded)
            (endTape (BuilderPayloadSearchComparison.finalValues source ctx older) inside compared) := by
          unfold LocalRejectRun
          rw [compare_program, ← hKind]
          simpa only [BuilderPayloadSearchComparison.initialConfiguration, workStartConfiguration, hInput, compared] using hCompare
        let visitChunk := BuilderPayloadSearchComparison.chunk source.kind completed.length (rest.length + 1) position item.index.val
        let middle := BuilderPayloadSearchComparison.cursorMiddle source.kind completed.length position item.index.val
        let nextOutside := BuilderPayloadSearchAdvance.finalOutside completed.length rest.length (residual position item.index.val) compared
        have hNextList : body constraint = (completed ++ [item]) ++ rest := by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using hList
        have hNextPrior : (prior ++ visitChunk).length = 17 * (completed ++ [item]).length := by
          simpa only [List.length_append, List.length_cons, List.length_nil, visitChunk] using
            BuilderPayloadSearchComparison.history_step source.kind prior completed.length (rest.length + 1) position item.index.val hPrior
        obtain ⟨tailSteps, resultValues, resultOutside, hCostTail, hTail, hRetained, hExhausted⟩ :=
          ih (completed ++ [item]) hNextList (prior ++ visitChunk) hNextPrior
            (residual position item.index.val) nextOutside
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hTail hCostTail
        have hAdvanceInput : BuilderPayloadSearchAdvance.initialValues
            (baseValues constraint request older prior) middle completed.length rest.length (residual position item.index.val) =
            BuilderPayloadSearchComparison.finalValues source ctx older := by
          rw [BuilderPayloadSearchComparison.finalValues, hBase]
          simp only [BuilderPayloadSearchAdvance.initialValues,
            hOrdinal, ctx, context, hValue, BuilderPayloadSearchComparison.chunk_cursor_layout, middle,
            List.append_assoc]
        have hAdvanceOutput : BuilderPayloadSearchAdvance.finalValues
            (baseValues constraint request older prior) middle completed.length rest.length (residual position item.index.val) =
            initialValues constraint request older (prior ++ visitChunk) (completed.length + 1) rest.length
              (residual position item.index.val) := by
          simp only [BuilderPayloadSearchAdvance.finalValues, BuilderPayloadSearchAdvance.initialValues,
            initialValues, baseValues, visitChunk, BuilderPayloadSearchComparison.chunk_cursor_layout, middle,
            List.append_assoc]
        have hAdvanceLocal : LocalAcceptRun advanceNode
            (BuilderPayloadSearchAdvance.workSteps middle completed.length rest.length (residual position item.index.val))
            (endTape (BuilderPayloadSearchComparison.finalValues source ctx older) inside compared)
            (endTape (initialValues constraint request older (prior ++ visitChunk) (completed.length + 1) rest.length
              (residual position item.index.val)) inside nextOutside) := by
          have hRun := BuilderPayloadSearchAdvance.workRunExact
            (baseValues constraint request older prior) middle completed.length rest.length
            (residual position item.index.val) inside compared
            (BuilderPayloadSearchComparison.cursorMiddle_length _ _ _ _)
          exact (by simpa only [LocalAcceptRun, advanceNode,
            BuilderPayloadSearchAdvance.initialConfiguration, BuilderPayloadSearchAdvance.finalConfiguration,
            workStartConfiguration, hAdvanceInput, hAdvanceOutput, nextOutside] using hRun)
        have hAdvancePath := advance_path (family constraint) _ _ _ _ _ _ hAdvanceLocal hTail
        have hContinuation : AcceptPath (graph (family constraint))
            (compareNode (family constraint) (lastFlag (rest.length + 1))).onReject
            (BuilderLiteralListSearch.endpoint rest (residual position item.index.val))
            (BuilderPayloadSearchAdvance.workSteps middle completed.length rest.length (residual position item.index.val) + 1 + tailSteps)
            (endTape (BuilderPayloadSearchComparison.finalValues source ctx older) inside compared)
            (endTape resultValues inside resultOutside) := by
          rw [compare_reject]
          exact hAdvancePath
        have hPath := AcceptPath.stepReject (compareNode (family constraint) (lastFlag (rest.length + 1))) _ _ _ _ _ _
          (compare_mem _ _) hLocal hContinuation
        have hWhole := guards_path (family constraint) (baseValues constraint request older prior)
          completed.length (rest.length + 1) position inside outside _ _ _ (by omega) hPath
        refine ⟨guardSteps (rest.length + 1) position +
          (BuilderPayloadSearchComparison.workSteps source ctx + 1 +
            (BuilderPayloadSearchAdvance.workSteps middle completed.length rest.length (residual position item.index.val) + 1 + tailSteps)),
          resultValues, resultOutside, ?_, ?_, hRetained, ?_⟩
        · have hValue' : (atSource constraint ⟨completed.length,hIndex⟩).originalLiteral.index.val = item.index.val := hValue
          have hCost := CostTrace.miss (constraint := constraint) (request := request) (older := older)
            completed.length rest.length prior hIndex hPrior position outside tailSteps resultValues resultOutside
          simp only [costVisit, hValue'] at hCost
          simpa only [Nat.add_assoc, List.length_cons, source, ctx, index, middle] using hCost hCostTail
        · simpa only [BuilderLiteralListSearch.endpoint, if_neg hHit, List.length_cons, initialValues] using hWhole
        · intro hDead
          simp only [BuilderLiteralListSearch.endpoint, if_neg hHit] at hDead
          obtain ⟨finalPrior, hLength, hValues⟩ := hExhausted hDead
          refine ⟨finalPrior, hLength, ?_⟩
          simpa only [DirectToken.boundedLiteralListWidth, DirectToken.boundedLiteralWidth,
            residual, if_neg hHit, Nat.sub_sub] using hValues

theorem loop_path {width : Nat} (remaining : List (BoundedLiteral width))
    (constraint : LocalConstraint width) (completed : List (BoundedLiteral width))
    (hList : body constraint = completed ++ remaining)
    (request : Request) (prior : List Nat) (hPrior : prior.length = 17 * completed.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    ∃ (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol),
      AcceptPath (graph (family constraint)) (.node (guardNode (family constraint)).reference)
        (BuilderLiteralListSearch.endpoint remaining position) steps
        (endTape (initialValues constraint request older prior completed.length remaining.length position) inside outside)
        (endTape resultValues inside resultOutside) ∧
      (∃ scratch, resultValues = requestValues constraint request older ++ scratch) ∧
      (BuilderLiteralListSearch.endpoint remaining position = .dead →
        ∃ finalPrior, finalPrior.length = 17 * (body constraint).length ∧
          resultValues = initialValues constraint request older finalPrior (body constraint).length 0
            (position - DirectToken.boundedLiteralListWidth remaining)) := by
  obtain ⟨steps, resultValues, resultOutside, _, hPath, hRetained, hExhausted⟩ :=
    loop_path_traced remaining constraint completed hList request prior hPrior position older inside outside
  exact ⟨steps, resultValues, resultOutside, hPath, hRetained, hExhausted⟩

/-- An arbitrary actual source body has a terminating execution with its exact
canonical token outcome and an intact original source/request prefix. This
This result alone does not assert a polynomial runtime. -/
theorem workRun_observes_body {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
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
            (position - DirectToken.boundedLiteralListWidth (body constraint))) := by
  obtain ⟨steps, resultValues, resultOutside, hPath, hRetained, hExhausted⟩ :=
    loop_path (body constraint) constraint [] rfl request [] rfl position older inside outside
  have hRun := WorkMachineProgramPath.runExact (graph (family constraint)) _ _ _ _ _
    (graph_wellFormed (family constraint)) hPath
  refine ⟨steps, resultValues, resultOutside, ?_, ?_, hRetained, hExhausted⟩
  · exact hRun
  · exact BuilderLiteralListSearch.endpoint_observes_list (body constraint) position _

/-- Compile the same complete execution to the raw finite machine. The sixfold
simulation cost is exact; the whole-loop polynomial bound remains to be proved. -/
theorem run_compile_observes_body {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
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
            (position - DirectToken.boundedLiteralListWidth (body constraint))) := by
  obtain ⟨steps, resultValues, resultOutside, hRun, hToken, hRetained, hExhausted⟩ :=
    workRun_observes_body constraint request position older inside outside
  exact ⟨steps, resultValues, resultOutside,
    run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hToken, hRetained, hExhausted⟩

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearch
