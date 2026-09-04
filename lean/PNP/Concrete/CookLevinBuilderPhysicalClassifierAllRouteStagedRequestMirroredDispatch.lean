/-
Copyright (c) 2026 PNP Labs.

One fixed physical composition over the complete post-header Cook--Levin
schedule.  M226's common classifier terminal feeds a protected-request relay
and the reflected M217 dispatcher at every body coordinate and at the unique
Finish coordinate.

The canonical request remains staged on the initial protected tape.  This
module does not synthesize that request, connect successive coordinates,
implement a repeated builder loop, construct a RawRefinement, or package the
Cook--Levin reduction.
-/

import PNP.Concrete.CookLevinBuilderPhysicalClassifierTerminalJoin

namespace PNP.Concrete.CookLevin

namespace BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch

open PipelineStateNamespace
open BuilderPostDividerSelectedTokenLaunch

abbrev classifierMachine : WorkMachine :=
  BuilderPhysicalClassifierTerminalJoin.machine
abbrev relayMachine : WorkMachine :=
  BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayMachine
abbrev dispatchMachine : WorkMachine :=
  BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.dispatchMachine
abbrev sourceDispatchMachine : WorkMachine :=
  BuilderPhysicalOptionalTokenDispatch.machine

abbrev unitSymbol : WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.unitSymbol
abbrev endSymbol : WorkSymbol := BuilderPhysicalClassifierFinishRequest.endSymbol

def output {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List CNFToken :=
  emittedPrefix problem index.val

def request {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Option CNFToken :=
  BuilderPhysicalOptionalTokenDispatch.canonicalRequest problem index

def requestCell {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkSymbol :=
  BuilderPhysicalOptionalTokenDispatch.requestSymbol (request problem index)

theorem request_mem_requestOrder {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    request problem index ∈
      BuilderPhysicalOptionalTokenDispatch.requestOrder := by
  cases hRequest : request problem index with
  | none => simp [BuilderPhysicalOptionalTokenDispatch.requestOrder]
  | some token =>
      cases token <;>
        simp [BuilderPhysicalOptionalTokenDispatch.requestOrder]

def builderWord {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  let workspace := BuilderTokenAppender.workspaceTape problem.input []
    (output problem index)
  workspace.head :: workspace.right

/-- The request cell is deliberately staged behind a blank sentinel. -/
def classifierWorkspace {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  WorkSymbol.blank :: requestCell problem index :: builderWord problem index

def classifierEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  BuilderPhysicalClassifierTerminalJoin.entryConfiguration problem index
    (classifierWorkspace problem index)

def classifierBaseFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPhysicalClassifierPipeline.finalConfiguration problem index workspace

def classifierFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPhysicalClassifierTerminalJoin.finalConfiguration problem index workspace

def classifierPrefix {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  (classifierBaseFinalConfiguration problem index []).tape.left

theorem route_ne_outOfRange {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val ≠
      .outOfRange := by
  intro hRoute
  have hAgreement := BuilderPhysicalClassifierPipeline.routeAgreement problem
    index []
  unfold BuilderPhysicalClassifierPipeline.RouteAgreement at hAgreement
  rw [hRoute] at hAgreement
  exact hAgreement

theorem classifier_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? classifierMachine (BuilderPhysicalClassifierTerminalJoin.workSteps problem index)
        (classifierEntryConfiguration problem index) =
      some (classifierFinalConfiguration problem index
        (classifierWorkspace problem index)) := by
  exact BuilderPhysicalClassifierTerminalJoin.workRunExact problem index (classifierWorkspace problem index)

theorem classifierFinal_state {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem index workspace).state =
      classifierMachine.acceptState := by
  rfl

private theorem preservedExterior_append_workspace
    (consumed remainder width : Nat) (exteriorPrefix : List WorkSymbol)
    (count : Nat) (workspace : List WorkSymbol) :
    BuilderPostDividerRawRouteClassifier.preservedExterior consumed remainder
        width exteriorPrefix count workspace =
      BuilderPostDividerRawRouteClassifier.preservedExterior consumed remainder
        width exteriorPrefix count [] ++ workspace := by
  simp [BuilderPostDividerRawRouteClassifier.preservedExterior,
    BuilderPostDividerRawRouteClassifier.sidecar, List.append_assoc]

theorem classifierBaseFinal_left_append {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    (classifierBaseFinalConfiguration problem index workspace).tape.left =
      classifierPrefix problem index ++ workspace := by
  cases hIndex : index.val with
  | zero =>
      simp only [classifierBaseFinalConfiguration, classifierPrefix,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hIndex,
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
      simp only [classifierBaseFinalConfiguration, classifierPrefix,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hIndex,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        renameConfiguration]
      simp [BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.sidecar, List.append_assoc]

theorem classifierFinal_left_append {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem index workspace).tape.left =
      classifierPrefix problem index ++ workspace := by
  simpa [classifierFinalConfiguration,
    BuilderPhysicalClassifierTerminalJoin.finalConfiguration,
    classifierBaseFinalConfiguration, renameConfiguration]
    using classifierBaseFinal_left_append problem index workspace

private theorem blank_ne_unit : WorkSymbol.blank ≠ unitSymbol := by decide
private theorem blank_ne_end : WorkSymbol.blank ≠ endSymbol := by decide

theorem classifierBaseFinal_head_ne_blank {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    (classifierBaseFinalConfiguration problem index workspace).tape.head ≠
      WorkSymbol.blank := by
  have hAgreement := BuilderPhysicalClassifierPipeline.routeAgreement problem
    index workspace
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      have hCoordinate :=
        (BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_eq_body_iff
          problem index.val clauseCoordinate tokenCoordinate).1 hRoute
      have hNotBound :
          ¬BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.bodyOpportunityCount
              problem ≤ index.val := by
        intro hBound
        have hNone :=
          (BuilderArbitrarySlotPostHeaderDecoder.rectangleCoordinate?_eq_none_iff
            problem.formulaClauseSlotCount problem.formulaTokensPerClause
            index.val).2 hBound
        rw [hNone] at hCoordinate
        contradiction
      have hLt : index.val <
          BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.bodyOpportunityCount
            problem := by
        omega
      let bodyCoordinate : Fin (BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.bodyOpportunityCount problem) :=
        ⟨index.val, hLt⟩
      have hIndex : BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.bodyIndex problem bodyCoordinate = index := by
        apply Fin.ext
        rfl
      have hHead := BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.classifierFinal_head problem bodyCoordinate
        workspace
      have hExact :
          (classifierBaseFinalConfiguration problem index workspace).tape.head =
            unitSymbol := by
        simpa [classifierBaseFinalConfiguration,
          BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.classifierFinalConfiguration, hIndex] using hHead
      rw [hExact]
      exact blank_ne_unit.symm
  | finish =>
      have hValue :=
        (BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_eq_finish_iff
          problem index.val).1 hRoute
      have hIndex : index = BuilderPhysicalClassifierFinishRequest.finishIndex
          problem := by
        apply Fin.ext
        simpa [BuilderPhysicalClassifierFinishRequest.finishIndex,
          BuilderPhysicalFinishRequest.finishIndex] using hValue
      have hHead := BuilderPhysicalClassifierFinishRequest.classifierFinal_head
        problem workspace
      have hExact :
          (classifierBaseFinalConfiguration problem index workspace).tape.head =
            endSymbol := by
        simpa [classifierBaseFinalConfiguration,
          BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
          hIndex] using hHead
      rw [hExact]
      exact blank_ne_end.symm
  | outOfRange =>
      unfold BuilderPhysicalClassifierPipeline.RouteAgreement at hAgreement
      rw [hRoute] at hAgreement
      exact False.elim hAgreement

theorem classifierFinal_head_ne_blank {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem index workspace).tape.head ≠
      WorkSymbol.blank := by
  simpa [classifierFinalConfiguration,
    BuilderPhysicalClassifierTerminalJoin.finalConfiguration,
    classifierBaseFinalConfiguration, renameConfiguration]
    using classifierBaseFinal_head_ne_blank problem index workspace

private theorem blank_ne_raw_separator :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.separatorSymbol := by decide
private theorem blank_ne_raw_left_boundary :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.leftBoundary := by decide
private theorem blank_ne_separator :
    WorkSymbol.blank ≠
      BuilderPostDividerRawRouteClassifier.separatorSymbol := by decide
private theorem blank_ne_left_boundary :
    WorkSymbol.blank ≠
      BuilderPostDividerRawRouteClassifier.leftBoundary := by decide
private theorem blank_ne_copied_width :
    WorkSymbol.blank ≠ BuilderPostHeaderRawTapeBridge.copiedWidthMark := by decide
private theorem blank_ne_copied_remainder :
    WorkSymbol.blank ≠ BuilderPostHeaderRawTapeBridge.copiedRemainderMark := by
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
    simp [BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
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
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
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
      simpa [classifierPrefix, classifierBaseFinalConfiguration, hIndex,
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
      simpa [classifierPrefix, classifierBaseFinalConfiguration, hIndex,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        renameConfiguration, quotient, consumed, remainder, exterior] using
        (show WorkSymbol.blank ∉
            (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
              quotient (BuilderPhysicalClassifierPipeline.clauseCount problem)).tape.left ++
              BuilderPhysicalClassifierPipeline.greaterClassifierExterior
                problem remaining [] by
          simpa only [List.mem_append, not_or] using And.intro hRaw hExterior)

/-! ## Fixed staged-request relay -/

def relayEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  { state := relayMachine.startState
    tape := (classifierFinalConfiguration problem index
      (classifierWorkspace problem index)).tape }

def dispatchOutsideLeft {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  let final := classifierFinalConfiguration problem index
    (classifierWorkspace problem index)
  WorkSymbol.blank ::
    (final.tape.head :: classifierPrefix problem index).reverse ++
      final.tape.right

def relayFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  { state := relayMachine.acceptState
    tape :=
      { left := builderWord problem index
        head := requestCell problem index
        right := dispatchOutsideLeft problem index } }

def relayWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) : Nat :=
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
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? relayMachine (relayWorkSteps problem index)
        (relayEntryConfiguration problem index) =
      some (relayFinalConfiguration problem index) := by
  let final := classifierFinalConfiguration problem index
    (classifierWorkspace problem index)
  have hLeft := classifierFinal_left_append problem index
    (classifierWorkspace problem index)
  have hHead := classifierFinal_head_ne_blank problem index
    (classifierWorkspace problem index)
  have hScan : forall symbol,
      symbol ∈ (final.tape.head :: classifierPrefix problem index) ->
        symbol ≠ WorkSymbol.blank := by
    intro symbol hSymbol
    rcases List.mem_cons.mp hSymbol with hCurrent | hPrefix
    · subst symbol
      exact hHead
    · exact fun hBlank =>
        blank_not_mem_classifierPrefix problem index (hBlank ▸ hPrefix)
  have hRun := BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayScan_prefix_exact
    (final.tape.head :: classifierPrefix problem index)
    (builderWord problem index) final.tape.right (request problem index) hScan
  have hEntry :
      { state := BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayScanState
        tape := BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.leftPathTape final.tape.right
          ((final.tape.head :: classifierPrefix problem index) ++
            WorkSymbol.blank :: requestCell problem index ::
              builderWord problem index) } =
        relayEntryConfiguration problem index := by
    apply workConfiguration_ext
    · rfl
    · apply workTape_ext
      · simpa [BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.leftPathTape, relayEntryConfiguration,
          classifierWorkspace, final] using hLeft.symm
      · rfl
      · rfl
  have hSteps :
      (final.tape.head :: classifierPrefix problem index).length + 2 =
        relayWorkSteps problem index := by
    simp [relayWorkSteps]
  rw [← hSteps, ← hEntry]
  simpa [relayMachine,
    BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayMachine,
    relayFinalConfiguration, dispatchOutsideLeft,
    requestCell, final, List.reverse_cons, List.append_assoc] using hRun

/-! ## Terminal-joined classifier followed by the relay -/

def classifierRelayMachine : WorkMachine :=
  WorkMachineChain.machine classifierMachine relayMachine

def classifierRelayEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (classifierEntryConfiguration problem index)

def classifierRelayFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (relayFinalConfiguration problem index)

def classifierRelayWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) : Nat :=
  BuilderPhysicalClassifierTerminalJoin.workSteps problem index + 1 + relayWorkSteps problem index

theorem classifierRelay_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? classifierRelayMachine
        (classifierRelayWorkSteps problem index)
        (classifierRelayEntryConfiguration problem index) =
      some (classifierRelayFinalConfiguration problem index) := by
  have hAll := WorkMachineChain.workRunExact classifierMachine relayMachine
    (BuilderPhysicalClassifierTerminalJoin.workSteps problem index)
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
    classifierRelayMachine.rules.length = 743 := by rfl

theorem classifierRelayRules_pairwise_query_distinct :
    classifierRelayMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    classifierMachine relayMachine BuilderPhysicalClassifierTerminalJoin.rules_pairwise_query_distinct
    BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayRules_pairwise_query_distinct BuilderPhysicalClassifierTerminalJoin.noRuleAtAccept

theorem classifierRelayMachine_acceptState_ne_rejectState :
    classifierRelayMachine.acceptState ≠
      classifierRelayMachine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    classifierMachine relayMachine BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayMachine_acceptState_ne_rejectState

/-! ## Reflected all-request dispatch -/

def dispatchEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
    (BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
      (dispatchOutsideLeft problem index) (output problem index)
      (request problem index))

def dispatchFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
    (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
      (BuilderTokenAppender.finalConfiguration problem.input
        (dispatchOutsideLeft problem index)
        (emittedPrefix problem (index.val + 1))))

def dispatchWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) : Nat :=
  BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem index

theorem dispatch_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? dispatchMachine (dispatchWorkSteps problem index)
        (dispatchEntryConfiguration problem index) =
      some (dispatchFinalConfiguration problem index) := by
  have hRun := BuilderPhysicalOptionalTokenDispatch.canonical_workRunExact
    problem index (dispatchOutsideLeft problem index)
  exact
    BuilderPhysicalClassifierFinishMirroredDispatch.workRunExact?_mirror_of_some
      sourceDispatchMachine
      (dispatchWorkSteps problem index)
      (BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
        (dispatchOutsideLeft problem index) (output problem index)
        (request problem index))
      (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
        (BuilderTokenAppender.finalConfiguration problem.input
          (dispatchOutsideLeft problem index)
          (emittedPrefix problem (index.val + 1)))) (by
        simpa [dispatchWorkSteps, dispatchMachine,
          dispatchEntryConfiguration, dispatchFinalConfiguration,
          output, request] using hRun)

theorem relayFinal_tape_eq_dispatchEntry {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    (relayFinalConfiguration problem index).tape =
      (dispatchEntryConfiguration problem index).tape := by
  rfl

/-! ## Complete all-route composition -/

def machine : WorkMachine :=
  WorkMachineChain.machine classifierRelayMachine dispatchMachine

def entryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (classifierRelayEntryConfiguration problem index)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (dispatchFinalConfiguration problem index)

def workSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) : Nat :=
  classifierRelayWorkSteps problem index + 1 + dispatchWorkSteps problem index

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
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
theorem rules_length : machine.rules.length = 816 := by rfl

private theorem relay_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept relayMachine := by
  intro rule hRule
  change rule ∈ BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayRules at hRule
  change rule.sourceState ≠ BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayAcceptState
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
    BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.dispatchRules_pairwise_query_distinct
    classifierRelay_noRuleAtAccept

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    classifierRelayMachine dispatchMachine
    BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.dispatchMachine_acceptState_ne_rejectState

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
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
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    0 < workSteps problem index := by
  unfold workSteps classifierRelayWorkSteps relayWorkSteps dispatchWorkSteps
  omega

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
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
  have hRun : workRun machine short (entryConfiguration problem index) = before :=
    workRun_eq_of_workRunExact machine short
      (entryConfiguration problem index) before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine before
    (finalConfiguration problem index) hLast

/-! ## Uniform encoded-source-size polynomial bound -/

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
          BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration] <;>
        omega
  | succ coordinate inductionHypothesis =>
      cases boundary with
      | zero =>
          simp [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
            BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration]
          omega
      | succ boundary =>
          simp only [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult]
          have hBound := inductionHypothesis (processed + 1) boundary
          omega

private theorem rawFinal_left_length_le (coordinate boundary : Nat) :
    (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
      coordinate boundary).tape.left.length ≤ 2 * coordinate + 2 := by
  unfold BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
  have hBound := rawResult_left_length_le 0 coordinate boundary
  omega

theorem classifierPrefix_length_le {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    (classifierPrefix problem index).length ≤
      24 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1) := by
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
      index.val ≤ BuilderFullScheduleCursorController.bodySlotCount problem :=
    Nat.le_of_lt index.isLt
  have hIndexBound :
      index.val ≤ BuilderPhysicalClassifierPipeline.clauseCount problem *
        BuilderPhysicalClassifierPipeline.width problem := by
    have hIndexLt : index.val <
        problem.formulaClauseSlotCount * problem.formulaTokensPerClause + 1 := by
      simpa only [BuilderFullScheduleCursorController.bodySlotCount_eq] using
        index.isLt
    change index.val <
      BuilderPhysicalClassifierPipeline.clauseCount problem *
          BuilderPhysicalClassifierPipeline.width problem + 1 at hIndexLt
    omega
  have hQuotientLe :
      index.val / BuilderPhysicalClassifierPipeline.width problem ≤
        BuilderPhysicalClassifierPipeline.clauseCount problem :=
    Nat.div_le_of_le_mul (by
      simpa [Nat.mul_comm] using hIndexBound)
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
      simp [classifierPrefix, classifierBaseFinalConfiguration, hIndex,
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
        renameConfiguration] at hBody hCountLeBody hIndexLeBody hIndexBound hQuotientLe hRemainder hConsumed ⊢
      omega
  | succ remaining =>
      have hRaw := rawFinal_left_length_le
        ((remaining + 1) / BuilderPhysicalClassifierPipeline.width problem)
        (BuilderPhysicalClassifierPipeline.clauseCount problem)
      simp [classifierPrefix, classifierBaseFinalConfiguration, hIndex,
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
        renameConfiguration] at hBody hCountLeBody hIndexLeBody hIndexBound hQuotientLe hRemainder hConsumed ⊢
      omega

def sizePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.sizePolynomial verifier

theorem sizePolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (sizePolynomial problem.verifier).eval problem.input.length =
      BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1 := by
  exact BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.sizePolynomial_eval problem

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
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * (relayWorkSteps problem index + 2) ≤
      (relayRawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := classifierPrefix_length_le problem index
  rw [relayRawTimeBound_eval]
  unfold relayWorkSteps
  omega

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPhysicalClassifierTerminalJoin.rawTimeBound verifier)
    (.add (relayRawTimeBound verifier)
      (BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier))

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPhysicalClassifierTerminalJoin.rawTimeBound problem.verifier).eval problem.input.length +
        ((relayRawTimeBound problem.verifier).eval problem.input.length +
          (BuilderPhysicalOptionalTokenDispatch.rawTimeBound
            problem.verifier).eval problem.input.length) := by
  rfl

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier := BuilderPhysicalClassifierTerminalJoin.compiledSteps_le_rawTimeBound problem index
  have hRelay := relayCompiledSteps_le_rawTimeBound problem index
  have hDispatch :=
    BuilderPhysicalOptionalTokenDispatch.canonicalCompiledSteps_le_rawTimeBound
      problem index
  rw [rawTimeBound_eval]
  unfold workSteps classifierRelayWorkSteps dispatchWorkSteps
  omega

def AllRouteStagedRequestMirroredDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) : Prop :=
  BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val ≠
      .outOfRange /\
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

theorem allRouteStagedRequestMirroredDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    AllRouteStagedRequestMirroredDispatchHolds problem index := by
  exact ⟨route_ne_outOfRange problem index,
    request_mem_requestOrder problem index,
    classifierFinal_state problem index (classifierWorkspace problem index),
    relay_workRunExact problem index,
    relayFinal_tape_eq_dispatchEntry problem index,
    dispatch_workRunExact problem index, workRunExact problem index,
    run_compile_exact problem index, one_step_short_not_halted problem index,
    compiledSteps_le_rawTimeBound problem index⟩

/-- M227 composes M226's common classifier terminal with one protected-request
relay and reflected dispatcher over the complete post-header schedule.  One
fixed 816-rule machine handles every body token, padding request, and the unique
Finish coordinate and reaches the exact next emitted prefix with exact work and
compiled traces, a one-step-short witness, collision freedom, and one
source-input-size polynomial bound.  The request is still staged on the initial
protected tape: raw request synthesis, successive-configuration iteration, the
repeated physical loop, builder `RawRefinement`, and the packaged Cook--Levin
reduction remain open. -/
theorem cook_levin_builder_physical_classifier_all_route_staged_request_mirrored_dispatch_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayRules.length = 14 /\
    dispatchMachine.rules.length = 64 /\
    machine.rules.length = 816 /\
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) /\
    machine.acceptState ≠ machine.rejectState /\
    (forall index, AllRouteStagedRequestMirroredDispatchHolds problem index) := by
  exact ⟨BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.relayRules_length, BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.dispatchRules_length,
    rules_length, rules_pairwise_query_distinct,
    machine_acceptState_ne_rejectState,
    allRouteStagedRequestMirroredDispatchHolds problem⟩

end BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch

end PNP.Concrete.CookLevin
