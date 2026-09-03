import PNP.Concrete.CookLevinBuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch

namespace PNP.Concrete.CookLevin

namespace BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch

open PipelineStateNamespace
open BuilderPostDividerSelectedTokenLaunch

abbrev classifierMachine : WorkMachine :=
  BuilderPhysicalClassifierPipeline.machine

abbrev sourceDispatchMachine : WorkMachine :=
  BuilderPhysicalOptionalTokenDispatch.machine

abbrev unitSymbol : WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.unitSymbol

/-- The complete clause-token rectangle, excluding the unique final `Finish`
opportunity. -/
def bodyOpportunityCount {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.formulaClauseSlotCount * problem.formulaTokensPerClause

/-- Embed one body opportunity into the complete post-header schedule. -/
def bodyIndex {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    Fin (BuilderFullScheduleCursorController.bodySlotCount problem) :=
  ⟨index.val, by
    rw [BuilderFullScheduleCursorController.bodySlotCount_eq]
    exact Nat.lt_succ_of_lt index.isLt⟩

@[simp] theorem bodyIndex_val {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    (bodyIndex problem index).val = index.val := rfl

/-- Every coordinate in the body opportunity type is decoded as one genuine
clause-token rectangle coordinate, including coordinates whose selected entry
is padding. -/
theorem bodyIndex_route {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    exists clauseCoordinate tokenCoordinate,
      BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val =
        .body clauseCoordinate tokenCoordinate := by
  cases hCoordinate :
      BuilderArbitrarySlotPostHeaderDecoder.rectangleCoordinate?
        problem.formulaClauseSlotCount problem.formulaTokensPerClause
        index.val with
  | none =>
      have hOutside :=
        (BuilderArbitrarySlotPostHeaderDecoder.rectangleCoordinate?_eq_none_iff
          problem.formulaClauseSlotCount problem.formulaTokensPerClause
          index.val).1 hCoordinate
      exact False.elim (Nat.not_le_of_lt index.isLt hOutside)
  | some coordinate =>
      rcases coordinate with ⟨clauseCoordinate, tokenCoordinate⟩
      exact ⟨clauseCoordinate, tokenCoordinate,
        (BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_eq_body_iff
          problem index.val clauseCoordinate tokenCoordinate).2 hCoordinate⟩

def output {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : List CNFToken :=
  emittedPrefix problem index.val

def request {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : Option CNFToken :=
  BuilderPhysicalOptionalTokenDispatch.canonicalRequest problem
    (bodyIndex problem index)

def requestCell {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkSymbol :=
  BuilderPhysicalOptionalTokenDispatch.requestSymbol (request problem index)

theorem request_mem_requestOrder {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    request problem index ∈
      BuilderPhysicalOptionalTokenDispatch.requestOrder := by
  cases hRequest : request problem index with
  | none => simp [BuilderPhysicalOptionalTokenDispatch.requestOrder]
  | some token =>
      cases token <;>
        simp [BuilderPhysicalOptionalTokenDispatch.requestOrder]

def builderWord {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : List WorkSymbol :=
  let workspace := BuilderTokenAppender.workspaceTape problem.input []
    (output problem index)
  workspace.head :: workspace.right

/-- The request is deliberately explicit on the protected input tape.  The
module proves physical relay and dispatch, not raw request synthesis. -/
def classifierWorkspace {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : List WorkSymbol :=
  WorkSymbol.blank :: requestCell problem index :: builderWord problem index

def classifierEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkConfiguration :=
  BuilderPhysicalClassifierPipeline.entryConfiguration problem
    (bodyIndex problem index) (classifierWorkspace problem index)

def classifierFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem))
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPhysicalClassifierPipeline.finalConfiguration problem
    (bodyIndex problem index) workspace

def classifierPrefix {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : List WorkSymbol :=
  (classifierFinalConfiguration problem index []).tape.left

theorem classifier_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    workRunExact? classifierMachine
        (BuilderPhysicalClassifierPipeline.workSteps problem
          (bodyIndex problem index))
        (classifierEntryConfiguration problem index) =
      some (classifierFinalConfiguration problem index
        (classifierWorkspace problem index)) := by
  exact BuilderPhysicalClassifierPipeline.workRunExact problem
    (bodyIndex problem index) (classifierWorkspace problem index)

theorem classifierFinal_state {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem))
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem index workspace).state =
      classifierMachine.acceptState := by
  rcases bodyIndex_route problem index with
    ⟨clauseCoordinate, tokenCoordinate, hRoute⟩
  have hAgreement := BuilderPhysicalClassifierPipeline.routeAgreement problem
    (bodyIndex problem index) workspace
  simpa only [BuilderPhysicalClassifierPipeline.RouteAgreement, bodyIndex_val,
    hRoute, classifierFinalConfiguration, classifierMachine] using hAgreement

private theorem preservedExterior_append_workspace
    (consumed remainder width : Nat) (exteriorPrefix : List WorkSymbol)
    (count : Nat) (workspace : List WorkSymbol) :
    BuilderPostDividerRawRouteClassifier.preservedExterior consumed remainder
        width exteriorPrefix count workspace =
      BuilderPostDividerRawRouteClassifier.preservedExterior consumed remainder
        width exteriorPrefix count [] ++ workspace := by
  simp [BuilderPostDividerRawRouteClassifier.preservedExterior,
    BuilderPostDividerRawRouteClassifier.sidecar, List.append_assoc]

theorem classifierFinal_left_append {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem))
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem index workspace).tape.left =
      classifierPrefix problem index ++ workspace := by
  cases hIndex : (bodyIndex problem index).val with
  | zero =>
      simp only [classifierFinalConfiguration, classifierPrefix,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        hIndex,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalClassifierExterior,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        renameConfiguration]
      simp [BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.sidecar, List.append_assoc]
  | succ remaining =>
      simp only [classifierFinalConfiguration, classifierPrefix,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        hIndex,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        renameConfiguration]
      simp [BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.sidecar, List.append_assoc]

private theorem rawResult_left_length_le
    (processed coordinate boundary : Nat) :
    (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
      (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult processed
        coordinate boundary)).tape.left.length ≤
      2 * processed + 2 * coordinate + 2 := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary <;>
        simp [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
          BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration] <;> omega
  | succ coordinate ih =>
      cases boundary with
      | zero =>
          simp [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
            BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration]
          omega
      | succ boundary =>
          simp only [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult]
          have hBound := ih (processed + 1) boundary
          omega

private theorem rawFinal_head_of_lt (coordinate boundary : Nat)
    (hLess : coordinate < boundary) :
    (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
      coordinate boundary).tape.head = unitSymbol := by
  have hIsLess :=
    (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult_isLess_iff
      0 coordinate boundary).2 hLess
  unfold BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
  cases hResult :
      BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
        boundary with
  | less processed remainingBoundary => rfl
  | equal processed =>
      simp [hResult,
        BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult.isLess]
        at hIsLess
  | greater processed remainingCoordinate =>
      simp [hResult,
        BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult.isLess]
        at hIsLess

private theorem rawFinal_left_length_le (coordinate boundary : Nat) :
    (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
      coordinate boundary).tape.left.length ≤ 2 * coordinate + 2 := by
  unfold BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
  have hBound := rawResult_left_length_le 0 coordinate boundary
  omega

private theorem body_quotient_lt_clauseCount {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    index.val / BuilderPhysicalClassifierPipeline.width problem <
      BuilderPhysicalClassifierPipeline.clauseCount problem := by
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  apply (Nat.div_lt_iff_lt_mul hWidth).2
  exact index.isLt

theorem classifierFinal_head {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem))
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem index workspace).tape.head =
      unitSymbol := by
  have hLess := body_quotient_lt_clauseCount problem index
  have hRaw := rawFinal_head_of_lt
    (index.val / BuilderPhysicalClassifierPipeline.width problem)
    (BuilderPhysicalClassifierPipeline.clauseCount problem) hLess
  cases hIndex : index.val with
  | zero =>
      simpa [classifierFinalConfiguration, bodyIndex, hIndex,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        renameConfiguration] using hRaw
  | succ remaining =>
      simpa [classifierFinalConfiguration, bodyIndex, hIndex,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterQuotient,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        renameConfiguration] using hRaw

private theorem blank_ne_raw_separator :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.separatorSymbol := by decide

private theorem blank_ne_raw_left_boundary :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.leftBoundary := by decide

private theorem blank_ne_unit :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.unitSymbol := by
  decide

private theorem blank_ne_separator :
    WorkSymbol.blank ≠
      BuilderPostDividerRawRouteClassifier.separatorSymbol := by decide

private theorem blank_ne_left_boundary :
    WorkSymbol.blank ≠
      BuilderPostDividerRawRouteClassifier.leftBoundary := by decide

private theorem blank_ne_copied_width :
    WorkSymbol.blank ≠ BuilderPostHeaderRawTapeBridge.copiedWidthMark := by
  decide

private theorem blank_ne_copied_remainder :
    WorkSymbol.blank ≠ BuilderPostHeaderRawTapeBridge.copiedRemainderMark := by
  decide

private theorem blank_ne_end :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.endSymbol := by
  decide

private theorem blank_ne_boundary :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.boundaryMark := by decide

private theorem blank_ne_coordinate :
    WorkSymbol.blank ≠
      BuilderPostDividerRawRouteClassifier.coordinateMark := by decide

private theorem blank_ne_consumed :
    WorkSymbol.blank ≠
      BuilderPostDividerRawRouteClassifier.consumedDividend := by decide

private theorem rawFinal_left_blank_free (coordinate boundary : Nat) :
    WorkSymbol.blank ∉
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
        coordinate boundary).tape.left := by
  unfold BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
  cases hResult :
      BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
        boundary <;>
    simp [
      BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
      blank_ne_raw_separator, blank_ne_raw_left_boundary,
      blank_ne_boundary, blank_ne_coordinate, blank_ne_unit]

private theorem equalExteriorPrefix_blank_free (processed width : Nat) :
    WorkSymbol.blank ∉
      BuilderPostDividerRawRouteClassifier.equalExteriorPrefix processed
        width := by
  simp [BuilderPostDividerRawRouteClassifier.equalExteriorPrefix,
    blank_ne_separator, blank_ne_copied_width, blank_ne_end,
    blank_ne_boundary, blank_ne_coordinate]

private theorem greaterExteriorPrefix_blank_free
    (processed remaining width : Nat) :
    WorkSymbol.blank ∉
      BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix processed
        remaining width := by
  simp [BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix,
    blank_ne_separator, blank_ne_copied_width, blank_ne_copied_remainder,
    blank_ne_end, blank_ne_boundary, blank_ne_coordinate]

private theorem preservedExterior_blank_free
    (consumed remainder width : Nat) (exteriorPrefix : List WorkSymbol)
    (count : Nat) (hExterior : WorkSymbol.blank ∉ exteriorPrefix) :
    WorkSymbol.blank ∉
      BuilderPostDividerRawRouteClassifier.preservedExterior consumed
        remainder width exteriorPrefix count [] := by
  simp [BuilderPostDividerRawRouteClassifier.preservedExterior,
    BuilderPostDividerRawRouteClassifier.terminalPrefix,
    BuilderPostDividerRawRouteClassifier.sidecar, hExterior,
    blank_ne_unit, blank_ne_separator, blank_ne_left_boundary, blank_ne_end,
    blank_ne_consumed]

theorem blank_not_mem_classifierPrefix {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    WorkSymbol.blank ∉ classifierPrefix problem index := by
  cases hIndex : index.val with
  | zero =>
      have hRaw := rawFinal_left_blank_free 0
        (BuilderPhysicalClassifierPipeline.clauseCount problem)
      have hExterior := preservedExterior_blank_free 0 0
        (BuilderPhysicalClassifierPipeline.width problem)
        (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix
          (BuilderPhysicalClassifierPipeline.firstBodySlot problem)
          (BuilderPhysicalClassifierPipeline.width problem))
        (BuilderPhysicalClassifierPipeline.clauseCount problem)
        (equalExteriorPrefix_blank_free
          (BuilderPhysicalClassifierPipeline.firstBodySlot problem)
          (BuilderPhysicalClassifierPipeline.width problem))
      change WorkSymbol.blank ∉
        BuilderPhysicalClassifierPipeline.equalClassifierExterior
          problem [] at hExterior
      simpa [classifierPrefix, classifierFinalConfiguration, bodyIndex, hIndex,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalClassifierExterior,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        renameConfiguration] using
        (show WorkSymbol.blank ∉
            (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration 0
              (BuilderPhysicalClassifierPipeline.clauseCount problem)).tape.left ++
              BuilderPhysicalClassifierPipeline.equalClassifierExterior
                problem [] by
          simpa only [List.mem_append, not_or] using And.intro hRaw hExterior)
  | succ remaining =>
      let quotient := BuilderPhysicalClassifierPipeline.greaterQuotient problem
        remaining
      let consumed := BuilderPhysicalClassifierPipeline.greaterConsumed problem
        remaining
      let remainder :=
        BuilderPhysicalClassifierPipeline.greaterRemainder problem remaining
      let exterior :=
        BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix
          (BuilderPhysicalClassifierPipeline.firstBodySlot problem) remaining
          (BuilderPhysicalClassifierPipeline.width problem)
      have hRaw := rawFinal_left_blank_free quotient
        (BuilderPhysicalClassifierPipeline.clauseCount problem)
      have hExterior := preservedExterior_blank_free consumed remainder
        (BuilderPhysicalClassifierPipeline.width problem) exterior
        (BuilderPhysicalClassifierPipeline.clauseCount problem)
        (greaterExteriorPrefix_blank_free
          (BuilderPhysicalClassifierPipeline.firstBodySlot problem) remaining
          (BuilderPhysicalClassifierPipeline.width problem))
      change WorkSymbol.blank ∉
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior
          problem remaining [] at hExterior
      simpa [classifierPrefix, classifierFinalConfiguration, bodyIndex, hIndex,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        renameConfiguration,
        quotient, consumed, remainder, exterior] using
        (show WorkSymbol.blank ∉
            (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
              quotient (BuilderPhysicalClassifierPipeline.clauseCount problem)).tape.left ++
              BuilderPhysicalClassifierPipeline.greaterClassifierExterior
                problem remaining [] by
          simpa only [List.mem_append, not_or] using And.intro hRaw hExterior)

/-! ## Fixed request-sidecar relay -/

def relayScanState : Nat := 0
def relayCaptureState : Nat := 1
def relayAcceptState : Nat := 2
def relayRejectState : Nat := 3

def relayScanRule (symbol : WorkSymbol) : WorkRule :=
  if symbol == WorkSymbol.blank then
    { sourceState := relayScanState
      readSymbol := symbol
      targetState := relayCaptureState
      writeSymbol := symbol
      move := .left }
  else
    { sourceState := relayScanState
      readSymbol := symbol
      targetState := relayScanState
      writeSymbol := symbol
      move := .left }

def relayCaptureRule (selected : Option CNFToken) : WorkRule :=
  { sourceState := relayCaptureState
    readSymbol := BuilderPhysicalOptionalTokenDispatch.requestSymbol selected
    targetState := relayAcceptState
    writeSymbol := BuilderPhysicalOptionalTokenDispatch.requestSymbol selected
    move := .stay }

def relayRules : List WorkRule :=
  PipelineMachineSimulation.allWorkSymbols.map relayScanRule ++
    BuilderPhysicalOptionalTokenDispatch.requestOrder.map relayCaptureRule

def relayMachine : WorkMachine :=
  { rules := relayRules
    startState := relayScanState
    acceptState := relayAcceptState
    rejectState := relayRejectState }

theorem relayRules_length : relayRules.length = 14 := by rfl

theorem relayRules_pairwise_query_distinct :
    relayRules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem relayMachine_acceptState_ne_rejectState :
    relayMachine.acceptState ≠ relayMachine.rejectState := by decide

private def leftPathTape (rightSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := WorkSymbol.blank, right := rightSide }
  | head :: left => { left := left, head := head, right := rightSide }

@[simp] private theorem leftPathTape_moveLeft_cons
    (rightSide : List WorkSymbol) (head : WorkSymbol)
    (left : List WorkSymbol) :
    (leftPathTape rightSide (head :: left)).moveLeft =
      leftPathTape (head :: rightSide) left := by
  cases left <;> rfl

private theorem relayRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? relayMachine start = some next) :
    workRunExact? relayMachine 1 start = some next := by
  change
    (match workStep? relayMachine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

theorem relayScan_nonblank_workStep (tape : WorkTape)
    (hHead : tape.head ≠ WorkSymbol.blank) :
    workStep? relayMachine
        { state := relayScanState, tape := tape } =
      some { state := relayScanState, tape := tape.moveLeft } := by
  rcases tape with ⟨left, ⟨first, second⟩, right⟩
  cases first <;> cases second
  all_goals first | exact False.elim (hHead rfl) | rfl

theorem relayScan_blank_workStep (left right : List WorkSymbol) :
    workStep? relayMachine
        { state := relayScanState
          tape := { left := left, head := WorkSymbol.blank, right := right } } =
      some
        { state := relayCaptureState
          tape :=
            ({ left := left, head := WorkSymbol.blank, right := right } :
              WorkTape).moveLeft } := by
  rfl

theorem relayCapture_workStep (selected : Option CNFToken)
    (left right : List WorkSymbol) :
    workStep? relayMachine
        { state := relayCaptureState
          tape :=
            { left := left
              head := BuilderPhysicalOptionalTokenDispatch.requestSymbol selected
              right := right } } =
      some
        { state := relayAcceptState
          tape :=
            { left := left
              head := BuilderPhysicalOptionalTokenDispatch.requestSymbol selected
              right := right } } := by
  cases selected with
  | none => rfl
  | some token => cases token <;> rfl

private theorem relayScan_prefix_exact :
    forall (scanWord tail right : List WorkSymbol)
      (selected : Option CNFToken),
      (forall symbol, symbol ∈ scanWord -> symbol ≠ WorkSymbol.blank) ->
      workRunExact? relayMachine (scanWord.length + 2)
          { state := relayScanState
            tape := leftPathTape right
              (scanWord ++ WorkSymbol.blank ::
                BuilderPhysicalOptionalTokenDispatch.requestSymbol selected ::
                  tail) } =
        some
          { state := relayAcceptState
            tape :=
              { left := tail
                head :=
                  BuilderPhysicalOptionalTokenDispatch.requestSymbol selected
                right := WorkSymbol.blank :: scanWord.reverse ++ right } } := by
  intro scanWord
  induction scanWord with
  | nil =>
      intro tail right selected _hScan
      have hBlank := relayRunExact_one
        { state := relayScanState
          tape := leftPathTape right
            (WorkSymbol.blank ::
              BuilderPhysicalOptionalTokenDispatch.requestSymbol selected ::
                tail) }
        { state := relayCaptureState
          tape :=
            { left := tail
              head := BuilderPhysicalOptionalTokenDispatch.requestSymbol selected
              right := WorkSymbol.blank :: right } } (by
          simpa [leftPathTape, WorkTape.moveLeft] using relayScan_blank_workStep
            (BuilderPhysicalOptionalTokenDispatch.requestSymbol selected :: tail)
            right)
      have hCapture := relayRunExact_one
        { state := relayCaptureState
          tape :=
            { left := tail
              head := BuilderPhysicalOptionalTokenDispatch.requestSymbol selected
              right := WorkSymbol.blank :: right } }
        { state := relayAcceptState
          tape :=
            { left := tail
              head := BuilderPhysicalOptionalTokenDispatch.requestSymbol selected
              right := WorkSymbol.blank :: right } }
        (relayCapture_workStep selected tail (WorkSymbol.blank :: right))
      have hAll := PipelineMachineSimulation.workRunExact?_compose relayMachine
        1 1 _ _ _ hBlank hCapture
      simpa using hAll
  | cons first rest inductionHypothesis =>
      intro tail right selected hScan
      have hFirst : first ≠ WorkSymbol.blank :=
        hScan first (List.Mem.head rest)
      have hRest : forall symbol,
          symbol ∈ rest -> symbol ≠ WorkSymbol.blank := by
        intro symbol hSymbol
        exact hScan symbol (List.Mem.tail first hSymbol)
      have hOne := relayRunExact_one
        { state := relayScanState
          tape := leftPathTape right
            (first :: rest ++ WorkSymbol.blank ::
              BuilderPhysicalOptionalTokenDispatch.requestSymbol selected ::
                tail) }
        { state := relayScanState
          tape := leftPathTape (first :: right)
            (rest ++ WorkSymbol.blank ::
              BuilderPhysicalOptionalTokenDispatch.requestSymbol selected ::
                tail) } (by
          simpa using relayScan_nonblank_workStep
            (leftPathTape right
              (first :: rest ++ WorkSymbol.blank ::
                BuilderPhysicalOptionalTokenDispatch.requestSymbol selected ::
                  tail)) hFirst)
      have hTail := inductionHypothesis tail (first :: right) selected hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose relayMachine
        1 (rest.length + 2) _ _ _ hOne hTail
      have hSteps :
          1 + (rest.length + 2) = (first :: rest).length + 2 := by
        simp only [List.length_cons]
        omega
      rw [← hSteps]
      simpa [List.reverse_cons, List.append_assoc] using hAll

def relayEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkConfiguration :=
  { state := relayMachine.startState
    tape := (classifierFinalConfiguration problem index
      (classifierWorkspace problem index)).tape }

def dispatchOutsideLeft {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : List WorkSymbol :=
  let final := classifierFinalConfiguration problem index
    (classifierWorkspace problem index)
  WorkSymbol.blank ::
    (final.tape.head :: classifierPrefix problem index).reverse ++
      final.tape.right

def relayFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkConfiguration :=
  { state := relayMachine.acceptState
    tape :=
      { left := builderWord problem index
        head := requestCell problem index
        right := dispatchOutsideLeft problem index } }

def relayWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : Nat :=
  (classifierPrefix problem index).length + 3

private theorem workTape_ext {left right : WorkTape}
    (hLeft : left.left = right.left)
    (hHead : left.head = right.head)
    (hRight : left.right = right.right) : left = right := by
  cases left
  cases right
  simp_all

private theorem workConfiguration_ext {left right : WorkConfiguration}
    (hState : left.state = right.state)
    (hTape : left.tape = right.tape) : left = right := by
  cases left
  cases right
  simp_all

theorem relay_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    workRunExact? relayMachine (relayWorkSteps problem index)
        (relayEntryConfiguration problem index) =
      some (relayFinalConfiguration problem index) := by
  let final := classifierFinalConfiguration problem index
    (classifierWorkspace problem index)
  have hLeft := classifierFinal_left_append problem index
    (classifierWorkspace problem index)
  have hHead := classifierFinal_head problem index
    (classifierWorkspace problem index)
  have hScan : forall symbol,
      symbol ∈ (final.tape.head :: classifierPrefix problem index) ->
        symbol ≠ WorkSymbol.blank := by
    intro symbol hSymbol
    rcases List.mem_cons.mp hSymbol with hCurrent | hPrefix
    · subst symbol
      rw [hHead]
      exact blank_ne_unit.symm
    · exact fun hBlank =>
        blank_not_mem_classifierPrefix problem index (hBlank ▸ hPrefix)
  have hRun := relayScan_prefix_exact
    (final.tape.head :: classifierPrefix problem index)
    (builderWord problem index) final.tape.right (request problem index) hScan
  have hEntry :
      { state := relayScanState
        tape := leftPathTape final.tape.right
          ((final.tape.head :: classifierPrefix problem index) ++
            WorkSymbol.blank :: requestCell problem index ::
              builderWord problem index) } =
        relayEntryConfiguration problem index := by
    apply workConfiguration_ext
    · rfl
    · apply workTape_ext
      · simpa [leftPathTape, relayEntryConfiguration, classifierWorkspace,
          final] using hLeft.symm
      · rfl
      · rfl
  have hSteps :
      (final.tape.head :: classifierPrefix problem index).length + 2 =
        relayWorkSteps problem index := by
    simp [relayWorkSteps]
  rw [← hSteps, ← hEntry]
  simpa [relayMachine, relayFinalConfiguration, dispatchOutsideLeft, requestCell, final,
    List.reverse_cons, List.append_assoc] using hRun

/-! ## Classifier-to-relay composition -/

def classifierRelayMachine : WorkMachine :=
  WorkMachineChain.machine classifierMachine relayMachine

def classifierRelayEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (classifierEntryConfiguration problem index)

def classifierRelayFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (relayFinalConfiguration problem index)

def classifierRelayWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : Nat :=
  BuilderPhysicalClassifierPipeline.workSteps problem (bodyIndex problem index) +
    1 + relayWorkSteps problem index

theorem classifierRelay_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    workRunExact? classifierRelayMachine
        (classifierRelayWorkSteps problem index)
        (classifierRelayEntryConfiguration problem index) =
      some (classifierRelayFinalConfiguration problem index) := by
  have hAll := WorkMachineChain.workRunExact classifierMachine relayMachine
    (BuilderPhysicalClassifierPipeline.workSteps problem
      (bodyIndex problem index))
    (relayWorkSteps problem index)
    (classifierEntryConfiguration problem index)
    (classifierFinalConfiguration problem index
      (classifierWorkspace problem index))
    (relayFinalConfiguration problem index)
    (classifier_workRunExact problem index)
    (classifierFinal_state problem index (classifierWorkspace problem index))
    (relay_workRunExact problem index)
  simpa [classifierRelayMachine, classifierRelayWorkSteps,
    classifierRelayEntryConfiguration, classifierRelayFinalConfiguration,
    relayEntryConfiguration] using hAll

set_option maxRecDepth 1000000 in
theorem classifierRelayRules_length :
    classifierRelayMachine.rules.length = 734 := by rfl

set_option maxRecDepth 1000000 in
private theorem classifier_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept classifierMachine := by
  intro rule hRule
  change rule ∈ BuilderPhysicalClassifierPipeline.machine.rules at hRule
  change rule.sourceState ≠
    BuilderPhysicalClassifierPipeline.machine.acceptState
  decide +revert

theorem classifierRelayRules_pairwise_query_distinct :
    classifierRelayMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    classifierMachine relayMachine
    BuilderPhysicalClassifierPipeline.rules_pairwise_query_distinct
    relayRules_pairwise_query_distinct classifier_noRuleAtAccept

theorem classifierRelayMachine_acceptState_ne_rejectState :
    classifierRelayMachine.acceptState ≠
      classifierRelayMachine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    classifierMachine relayMachine relayMachine_acceptState_ne_rejectState

/-! ## Reflected all-request dispatch -/

def dispatchMachine : WorkMachine :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorMachine
    sourceDispatchMachine

def dispatchEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkConfiguration :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
    (BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
      (dispatchOutsideLeft problem index) (output problem index)
      (request problem index))

def dispatchFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkConfiguration :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
    (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
      (BuilderTokenAppender.finalConfiguration problem.input
        (dispatchOutsideLeft problem index)
        (emittedPrefix problem (index.val + 1))))

def dispatchWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : Nat :=
  BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem
    (bodyIndex problem index)

theorem dispatch_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    workRunExact? dispatchMachine (dispatchWorkSteps problem index)
        (dispatchEntryConfiguration problem index) =
      some (dispatchFinalConfiguration problem index) := by
  have hRun := BuilderPhysicalOptionalTokenDispatch.canonical_workRunExact
    problem (bodyIndex problem index) (dispatchOutsideLeft problem index)
  exact
    BuilderPhysicalClassifierFinishMirroredDispatch.workRunExact?_mirror_of_some
      sourceDispatchMachine (dispatchWorkSteps problem index)
      (BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
        (dispatchOutsideLeft problem index) (output problem index)
        (request problem index))
      (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
        (BuilderTokenAppender.finalConfiguration problem.input
          (dispatchOutsideLeft problem index)
          (emittedPrefix problem (index.val + 1)))) (by
        simpa [dispatchWorkSteps, dispatchMachine,
          dispatchEntryConfiguration, dispatchFinalConfiguration,
          output, request, bodyIndex] using hRun)

theorem dispatchRules_length : dispatchMachine.rules.length = 64 := by rfl

theorem dispatchRules_pairwise_query_distinct :
    dispatchMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact
    BuilderPhysicalClassifierFinishMirroredDispatch.mirrorRules_pairwise_query_distinct
      sourceDispatchMachine
      BuilderPhysicalOptionalTokenDispatch.rules_pairwise_query_distinct

theorem dispatchMachine_acceptState_ne_rejectState :
    dispatchMachine.acceptState ≠ dispatchMachine.rejectState := by
  exact
    BuilderPhysicalClassifierFinishMirroredDispatch.mirrorMachine_acceptState_ne_rejectState
      sourceDispatchMachine
      BuilderPhysicalOptionalTokenDispatch.machine_acceptState_ne_rejectState

theorem relayFinal_tape_eq_dispatchEntry {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    (relayFinalConfiguration problem index).tape =
      (dispatchEntryConfiguration problem index).tape := by
  rfl

/-! ## Complete all-body composition -/

def machine : WorkMachine :=
  WorkMachineChain.machine classifierRelayMachine dispatchMachine

def entryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (classifierRelayEntryConfiguration problem index)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (dispatchFinalConfiguration problem index)

def workSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : Nat :=
  classifierRelayWorkSteps problem index + 1 + dispatchWorkSteps problem index

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index) =
      some (finalConfiguration problem index) := by
  have hFirst := classifierRelay_workRunExact problem index
  have hEntry :
      ({ state := dispatchMachine.startState
         tape := (classifierRelayFinalConfiguration problem index).tape } :
        WorkConfiguration) = dispatchEntryConfiguration problem index := by
    apply workConfiguration_ext
    · rfl
    · exact relayFinal_tape_eq_dispatchEntry problem index
  have hSecond : workRunExact? dispatchMachine
      (dispatchWorkSteps problem index)
      { state := dispatchMachine.startState
        tape := (classifierRelayFinalConfiguration problem index).tape } =
      some (dispatchFinalConfiguration problem index) := by
    rw [hEntry]
    exact dispatch_workRunExact problem index
  have hAll := WorkMachineChain.workRunExact classifierRelayMachine
    dispatchMachine (classifierRelayWorkSteps problem index)
    (dispatchWorkSteps problem index)
    (classifierRelayEntryConfiguration problem index)
    (classifierRelayFinalConfiguration problem index)
    (dispatchFinalConfiguration problem index) hFirst rfl hSecond
  simpa [machine, workSteps, entryConfiguration, finalConfiguration] using hAll

set_option maxRecDepth 1000000 in
theorem rules_length : machine.rules.length = 807 := by rfl

private theorem relay_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept relayMachine := by
  intro rule hRule
  change rule ∈ relayRules at hRule
  change rule.sourceState ≠ relayAcceptState
  decide +revert

private theorem classifierRelay_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept classifierRelayMachine := by
  exact WorkMachineChain.noRuleAtAccept classifierMachine relayMachine
    relay_noRuleAtAccept

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    classifierRelayMachine dispatchMachine
    classifierRelayRules_pairwise_query_distinct
    dispatchRules_pairwise_query_distinct classifierRelay_noRuleAtAccept

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    classifierRelayMachine dispatchMachine
    dispatchMachine_acceptState_ne_rejectState

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index)) =
      encodeWorkConfiguration (finalConfiguration problem index) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps problem index) (entryConfiguration problem index)
    (finalConfiguration problem index) (workRunExact problem index)

private theorem workRunExact_succ_split_last (selectedMachine : WorkMachine) :
    forall (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? selectedMachine (steps + 1) initial = some final ->
      exists before,
        workRunExact? selectedMachine steps initial = some before /\
          workStep? selectedMachine before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? selectedMachine initial with
      | none =>
          change
            (match workStep? selectedMachine initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? selectedMachine initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps inductionHypothesis =>
      intro initial final hRun
      cases hStep : workStep? selectedMachine initial with
      | none =>
          change
            (match workStep? selectedMachine initial with
             | none => none
             | some next => workRunExact? selectedMachine (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? selectedMachine (steps + 1) next =
              some final := by
            change
              (match workStep? selectedMachine initial with
               | none => none
               | some result =>
                   workRunExact? selectedMachine (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases inductionHypothesis next final hTail with
            ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? selectedMachine initial with
             | none => none
             | some result => workRunExact? selectedMachine steps result) =
              some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some
    (selectedMachine : WorkMachine) (configuration next : WorkConfiguration)
    (hStep : workStep? selectedMachine configuration = some next) :
    selectedMachine.isHalted configuration = false := by
  cases hHalted : selectedMachine.isHalted configuration with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    0 < workSteps problem index := by
  unfold workSteps classifierRelayWorkSteps relayWorkSteps dispatchWorkSteps
  omega

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index)) = false := by
  have hPositive := workSteps_positive problem index
  let short := workSteps problem index - 1
  have hStepCount : short + 1 = workSteps problem index := by
    unfold short
    omega
  have hExact := workRunExact problem index
  rw [← hStepCount] at hExact
  rcases workRunExact_succ_split_last machine short
      (entryConfiguration problem index) (finalConfiguration problem index)
      hExact with ⟨before, hPrefix, hLast⟩
  have hRun :
      workRun machine short (entryConfiguration problem index) = before :=
    workRun_eq_of_workRunExact machine short
      (entryConfiguration problem index) before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine before
    (finalConfiguration problem index) hLast

/-! ## Uniform source-input-size polynomial bound -/

theorem classifierPrefix_length_le {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    (classifierPrefix problem index).length ≤
      24 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1) := by
  have hLess := body_quotient_lt_clauseCount problem index
  have hBody := BuilderFullScheduleCursorController.bodySlotCount_eq problem
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  have hCountLeBody :
      BuilderPhysicalClassifierPipeline.clauseCount problem ≤
        BuilderFullScheduleCursorController.bodySlotCount problem := by
    rw [hBody]
    change BuilderPhysicalClassifierPipeline.clauseCount problem ≤
      BuilderPhysicalClassifierPipeline.clauseCount problem *
          BuilderPhysicalClassifierPipeline.width problem + 1
    calc
      BuilderPhysicalClassifierPipeline.clauseCount problem =
          BuilderPhysicalClassifierPipeline.clauseCount problem * 1 := by omega
      _ ≤ BuilderPhysicalClassifierPipeline.clauseCount problem *
          BuilderPhysicalClassifierPipeline.width problem :=
        Nat.mul_le_mul_left _ hWidth
      _ ≤ BuilderPhysicalClassifierPipeline.clauseCount problem *
          BuilderPhysicalClassifierPipeline.width problem + 1 := by omega
  have hIndexLeBody :
      index.val ≤ BuilderFullScheduleCursorController.bodySlotCount problem := by
    rw [hBody]
    exact Nat.le_trans (Nat.le_of_lt index.isLt) (Nat.le_add_right _ _)
  have hRemainder :
      index.val % BuilderPhysicalClassifierPipeline.width problem <
        BuilderPhysicalClassifierPipeline.width problem :=
    Nat.mod_lt _ hWidth
  have hConsumed :
      (index.val / BuilderPhysicalClassifierPipeline.width problem) *
          BuilderPhysicalClassifierPipeline.width problem ≤ index.val :=
    Nat.div_mul_le_self _ _
  cases hIndex : index.val with
  | zero =>
      have hRaw := rawFinal_left_length_le 0
        (BuilderPhysicalClassifierPipeline.clauseCount problem)
      simp [classifierPrefix, classifierFinalConfiguration, bodyIndex, hIndex,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalClassifierExterior,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.sidecar,
        BuilderPostDividerRawRouteClassifier.terminalPrefix,
        BuilderPostDividerRawRouteClassifier.equalExteriorPrefix,
        renameConfiguration] at hBody hCountLeBody hIndexLeBody hRemainder hConsumed ⊢
      omega
  | succ remaining =>
      have hLessSucc :
          (remaining + 1) / BuilderPhysicalClassifierPipeline.width problem <
            BuilderPhysicalClassifierPipeline.clauseCount problem := by
        simpa [hIndex] using hLess
      have hRaw := rawFinal_left_length_le
        ((remaining + 1) / BuilderPhysicalClassifierPipeline.width problem)
        (BuilderPhysicalClassifierPipeline.clauseCount problem)
      simp [classifierPrefix, classifierFinalConfiguration, bodyIndex, hIndex,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior,
        BuilderPhysicalClassifierPipeline.greaterConsumed,
        BuilderPhysicalClassifierPipeline.greaterRemainder,
        BuilderPhysicalClassifierPipeline.greaterQuotient,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.sidecar,
        BuilderPostDividerRawRouteClassifier.terminalPrefix,
        BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix,
        renameConfiguration] at hBody hCountLeBody hIndexLeBody hRemainder hConsumed ⊢
      omega

def sizePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch.sizePolynomial
    verifier

theorem sizePolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (sizePolynomial problem.verifier).eval problem.input.length =
      BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1 := by
  exact
    BuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch.sizePolynomial_eval
      problem

def relayRawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (.constant 180) (sizePolynomial verifier)

theorem relayRawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (relayRawTimeBound problem.verifier).eval problem.input.length =
      180 *
        (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
          BuilderFullScheduleCursorController.bodySlotCount problem +
          BuilderPhysicalClassifierPipeline.width problem + 1) := by
  unfold relayRawTimeBound
  simp only [NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  rw [sizePolynomial_eval]

theorem relayCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    6 * (relayWorkSteps problem index + 2) ≤
      (relayRawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := classifierPrefix_length_le problem index
  rw [relayRawTimeBound_eval]
  unfold relayWorkSteps
  omega

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPhysicalClassifierPipeline.rawTimeBound verifier)
    (.add (relayRawTimeBound verifier)
      (BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier))

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPhysicalClassifierPipeline.rawTimeBound
          problem.verifier).eval problem.input.length +
        ((relayRawTimeBound problem.verifier).eval problem.input.length +
          (BuilderPhysicalOptionalTokenDispatch.rawTimeBound
            problem.verifier).eval problem.input.length) := by
  rfl

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier :=
    BuilderPhysicalClassifierPipeline.compiledSteps_le_rawTimeBound problem
      (bodyIndex problem index)
  have hRelay := relayCompiledSteps_le_rawTimeBound problem index
  have hDispatch :=
    BuilderPhysicalOptionalTokenDispatch.canonicalCompiledSteps_le_rawTimeBound
      problem (bodyIndex problem index)
  rw [rawTimeBound_eval]
  unfold workSteps classifierRelayWorkSteps dispatchWorkSteps
  omega

def AllBodyStagedRequestMirroredDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) : Prop :=
  (exists clauseCoordinate tokenCoordinate,
    BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val =
      .body clauseCoordinate tokenCoordinate) /\
    request problem index ∈
      BuilderPhysicalOptionalTokenDispatch.requestOrder /\
    (classifierFinalConfiguration problem index
      (classifierWorkspace problem index)).state = classifierMachine.acceptState /\
    workRunExact? relayMachine (relayWorkSteps problem index)
        (relayEntryConfiguration problem index) =
      some (relayFinalConfiguration problem index) /\
    (relayFinalConfiguration problem index).tape =
      (dispatchEntryConfiguration problem index).tape /\
    workRunExact? dispatchMachine (dispatchWorkSteps problem index)
        (dispatchEntryConfiguration problem index) =
      some (dispatchFinalConfiguration problem index) /\
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index) =
      some (finalConfiguration problem index) /\
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index)) =
      encodeWorkConfiguration (finalConfiguration problem index) /\
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index)) = false /\
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length

theorem allBodyStagedRequestMirroredDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (bodyOpportunityCount problem)) :
    AllBodyStagedRequestMirroredDispatchHolds problem index := by
  exact ⟨bodyIndex_route problem index, request_mem_requestOrder problem index,
    classifierFinal_state problem index (classifierWorkspace problem index),
    relay_workRunExact problem index,
    relayFinal_tape_eq_dispatchEntry problem index,
    dispatch_workRunExact problem index, workRunExact problem index,
    run_compile_exact problem index, one_step_short_not_halted problem index,
    compiledSteps_le_rawTimeBound problem index⟩

/-- M225 replaces M224's single first-separator coordinate with the complete
arbitrary finite clause-token rectangle.  One fixed 807-rule composition
accepts every body classifier terminal, scans to a protected tape-resident
canonical optional-token request, validates all five request symbols, and runs
the reflected fixed dispatcher to the exact next emitted prefix.  Padding and
all four token values share the same literal machine, exact work and compiled
traces, one-step-short witness and source-size polynomial bound.  The canonical
request is still staged in the initial protected workspace: raw request
synthesis, the combined body/Finish loop, successive-configuration iteration,
builder `RawRefinement` and the packaged Cook-Levin reduction remain open. -/
theorem cook_levin_builder_physical_classifier_all_body_staged_request_mirrored_dispatch_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    relayMachine.rules.length = 14 /\
    dispatchMachine.rules.length = 64 /\
    machine.rules.length = 807 /\
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) /\
    machine.acceptState ≠ machine.rejectState /\
    (forall index : Fin (bodyOpportunityCount problem),
      AllBodyStagedRequestMirroredDispatchHolds problem index) := by
  exact ⟨relayRules_length, dispatchRules_length, rules_length,
    rules_pairwise_query_distinct, machine_acceptState_ne_rejectState,
    allBodyStagedRequestMirroredDispatchHolds problem⟩

end BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch

end PNP.Concrete.CookLevin
