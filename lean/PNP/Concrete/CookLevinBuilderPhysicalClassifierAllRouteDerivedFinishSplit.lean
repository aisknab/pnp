/-
Copyright (c) 2026 PNP Labs.

An all-coordinate physical body/Finish request-control split after M226's
terminal-joined Cook--Levin classifier.

The protected builder workspace carries no staged optional-token request.
One fixed relay reads the classifier's physical body-or-Finish head, crosses
the complete blank-free classifier prefix, writes either an explicit pending
body marker or the canonical Finish request, and then launches a reflected
M217 dispatcher.  Finish reaches the exact next canonical emitted prefix;
body coordinates halt at the explicit request-synthesis boundary.

This module does not synthesize padding or body-token requests, select a raw
constraint or clause, connect successive coordinates, implement a repeated
builder loop, construct a RawRefinement, or package the Cook--Levin reduction.
-/

import PNP.Concrete.CookLevinBuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch

namespace PNP.Concrete.CookLevin

namespace BuilderPhysicalClassifierAllRouteDerivedFinishSplit

open PipelineTape PipelineStateNamespace
open BuilderPostDividerSelectedTokenLaunch

abbrev classifierMachine : WorkMachine :=
  BuilderPhysicalClassifierTerminalJoin.machine
abbrev sourceDispatchMachine : WorkMachine :=
  BuilderPhysicalOptionalTokenDispatch.machine
abbrev mirroredDispatchMachine : WorkMachine :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorMachine
    sourceDispatchMachine

abbrev unitSymbol : WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.unitSymbol
abbrev endSymbol : WorkSymbol :=
  BuilderPhysicalClassifierFinishRequest.endSymbol

def output {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List CNFToken :=
  emittedPrefix problem index.val

def builderWord {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  let workspace := BuilderTokenAppender.workspaceTape problem.input []
    (output problem index)
  workspace.head :: workspace.right

/-- Unlike M227, the protected suffix has only a sentinel and the canonical
builder word.  No optional-token request is present. -/
def classifierWorkspace {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  WorkSymbol.blank :: builderWord problem index

def classifierEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  BuilderPhysicalClassifierTerminalJoin.entryConfiguration problem index
    (classifierWorkspace problem index)

def classifierFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPhysicalClassifierTerminalJoin.finalConfiguration problem index
    workspace

def classifierPrefix {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.classifierPrefix
    problem index

theorem classifier_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? classifierMachine
        (BuilderPhysicalClassifierTerminalJoin.workSteps problem index)
        (classifierEntryConfiguration problem index) =
      some (classifierFinalConfiguration problem index
        (classifierWorkspace problem index)) := by
  exact BuilderPhysicalClassifierTerminalJoin.workRunExact problem index
    (classifierWorkspace problem index)

theorem classifierFinal_state {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem index workspace).state =
      classifierMachine.acceptState := by
  rfl

theorem classifierFinal_left_append {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem index workspace).tape.left =
      classifierPrefix problem index ++ workspace := by
  simpa [classifierFinalConfiguration, classifierPrefix,
    BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.classifierFinalConfiguration]
    using
    (BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.classifierFinal_left_append
      problem index workspace)

theorem blank_not_mem_classifierPrefix {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkSymbol.blank ∉ classifierPrefix problem index := by
  simpa [classifierPrefix] using
    (BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.blank_not_mem_classifierPrefix
      problem index)

theorem route_ne_outOfRange {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val ≠
      .outOfRange := by
  exact
    BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.route_ne_outOfRange
      problem index

theorem classifierFinal_head_eq_unit_of_body {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol)
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .body clauseCoordinate tokenCoordinate) :
    (classifierFinalConfiguration problem index workspace).tape.head =
      unitSymbol := by
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
  let bodyCoordinate : Fin
      (BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.bodyOpportunityCount
        problem) :=
    ⟨index.val, hLt⟩
  have hIndex :
      BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.bodyIndex
        problem bodyCoordinate = index := by
    apply Fin.ext
    rfl
  have hHead :=
    BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.classifierFinal_head
      problem bodyCoordinate workspace
  simpa [classifierFinalConfiguration,
    BuilderPhysicalClassifierTerminalJoin.finalConfiguration,
    BuilderPhysicalClassifierAllBodyStagedRequestMirroredDispatch.classifierFinalConfiguration,
    hIndex,
    renameConfiguration] using hHead

theorem classifierFinal_head_eq_end_of_finish {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol)
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .finish) :
    (classifierFinalConfiguration problem index workspace).tape.head =
      endSymbol := by
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
  simpa [classifierFinalConfiguration,
    BuilderPhysicalClassifierTerminalJoin.finalConfiguration,
    BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
    hIndex, renameConfiguration] using hHead

/-! ## Route-derived sentinel relay -/

/-- A control-only marker.  It is deliberately outside M217's five physical
optional-token request symbols. -/
def bodyPendingSymbol : WorkSymbol := leftMarker

theorem bodyPendingSymbol_ne_requestSymbol (request : Option CNFToken) :
    bodyPendingSymbol ≠
      BuilderPhysicalOptionalTokenDispatch.requestSymbol request := by
  cases request with
  | none => decide
  | some token => cases token <;> decide

def relayStartState : Nat := 0
def relayBodyScanState : Nat := 1
def relayFinishScanState : Nat := 2
def relayAcceptState : Nat := 3
def relayRejectState : Nat := 4

def relayStartBodyRule : WorkRule :=
  { sourceState := relayStartState
    readSymbol := unitSymbol
    targetState := relayBodyScanState
    writeSymbol := unitSymbol
    move := .left }

def relayStartFinishRule : WorkRule :=
  { sourceState := relayStartState
    readSymbol := endSymbol
    targetState := relayFinishScanState
    writeSymbol := endSymbol
    move := .left }

def relayScanRule (source : Nat) (terminal : WorkSymbol)
    (symbol : WorkSymbol) : WorkRule :=
  if symbol == WorkSymbol.blank then
    { sourceState := source
      readSymbol := symbol
      targetState := relayAcceptState
      writeSymbol := terminal
      move := .stay }
  else
    { sourceState := source
      readSymbol := symbol
      targetState := source
      writeSymbol := symbol
      move := .left }

def relayRules : List WorkRule :=
  [relayStartBodyRule, relayStartFinishRule] ++
    PipelineMachineSimulation.allWorkSymbols.map
      (relayScanRule relayBodyScanState bodyPendingSymbol) ++
    PipelineMachineSimulation.allWorkSymbols.map
      (relayScanRule relayFinishScanState
        (BuilderPhysicalOptionalTokenDispatch.requestSymbol
          (some CNFToken.finish)))

def relayMachine : WorkMachine :=
  { rules := relayRules
    startState := relayStartState
    acceptState := relayAcceptState
    rejectState := relayRejectState }

theorem relayRules_length : relayRules.length = 20 := by rfl

theorem relayRules_pairwise_query_distinct :
    relayRules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem relayMachine_acceptState_ne_rejectState :
    relayMachine.acceptState ≠ relayMachine.rejectState := by decide

theorem relay_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept relayMachine := by
  intro rule hRule
  change rule ∈ relayRules at hRule
  change rule.sourceState ≠ relayAcceptState
  decide +revert

def leftPathTape (rightSide : List WorkSymbol) :
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

theorem relayStart_body_workStep (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? relayMachine { state := relayStartState, tape := tape } =
      some { state := relayBodyScanState, tape := tape.moveLeft } := by
  rcases tape with ⟨left, head, right⟩
  simp only at hHead
  subst head
  rfl

theorem relayStart_finish_workStep (tape : WorkTape)
    (hHead : tape.head = endSymbol) :
    workStep? relayMachine { state := relayStartState, tape := tape } =
      some { state := relayFinishScanState, tape := tape.moveLeft } := by
  rcases tape with ⟨left, head, right⟩
  simp only at hHead
  subst head
  rfl

theorem relayBodyScan_nonblank_workStep (tape : WorkTape)
    (hHead : tape.head ≠ WorkSymbol.blank) :
    workStep? relayMachine
        { state := relayBodyScanState, tape := tape } =
      some { state := relayBodyScanState, tape := tape.moveLeft } := by
  rcases tape with ⟨left, ⟨first, second⟩, right⟩
  cases first <;> cases second
  all_goals first | exact False.elim (hHead rfl) | rfl

theorem relayFinishScan_nonblank_workStep (tape : WorkTape)
    (hHead : tape.head ≠ WorkSymbol.blank) :
    workStep? relayMachine
        { state := relayFinishScanState, tape := tape } =
      some { state := relayFinishScanState, tape := tape.moveLeft } := by
  rcases tape with ⟨left, ⟨first, second⟩, right⟩
  cases first <;> cases second
  all_goals first | exact False.elim (hHead rfl) | rfl

theorem relayBodyScan_blank_workStep (left right : List WorkSymbol) :
    workStep? relayMachine
        { state := relayBodyScanState
          tape := { left := left, head := WorkSymbol.blank, right := right } } =
      some
        { state := relayAcceptState
          tape := { left := left, head := bodyPendingSymbol, right := right } } := by
  rfl

theorem relayFinishScan_blank_workStep (left right : List WorkSymbol) :
    workStep? relayMachine
        { state := relayFinishScanState
          tape := { left := left, head := WorkSymbol.blank, right := right } } =
      some
        { state := relayAcceptState
          tape :=
            { left := left
              head := BuilderPhysicalOptionalTokenDispatch.requestSymbol
                (some CNFToken.finish)
              right := right } } := by
  rfl

private theorem relayScan_prefix_exact
    (scanState : Nat) (terminal : WorkSymbol)
    (hNonblank : ∀ tape : WorkTape, tape.head ≠ WorkSymbol.blank →
      workStep? relayMachine { state := scanState, tape := tape } =
        some { state := scanState, tape := tape.moveLeft })
    (hBlank : ∀ left right : List WorkSymbol,
      workStep? relayMachine
          { state := scanState
            tape := { left := left, head := WorkSymbol.blank, right := right } } =
        some
          { state := relayAcceptState
            tape := { left := left, head := terminal, right := right } }) :
    ∀ (scanWord tail right : List WorkSymbol),
      (∀ symbol, symbol ∈ scanWord → symbol ≠ WorkSymbol.blank) →
      workRunExact? relayMachine (scanWord.length + 1)
          { state := scanState
            tape := leftPathTape right
              (scanWord ++ WorkSymbol.blank :: tail) } =
        some
          { state := relayAcceptState
            tape :=
              { left := tail
                head := terminal
                right := scanWord.reverse ++ right } } := by
  intro scanWord
  induction scanWord with
  | nil =>
      intro tail right _hScan
      have hOne := relayRunExact_one
        { state := scanState
          tape := leftPathTape right (WorkSymbol.blank :: tail) }
        { state := relayAcceptState
          tape := { left := tail, head := terminal, right := right } }
        (by simpa [leftPathTape] using hBlank tail right)
      simpa using hOne
  | cons first rest inductionHypothesis =>
      intro tail right hScan
      have hFirst : first ≠ WorkSymbol.blank :=
        hScan first (List.Mem.head rest)
      have hRest : ∀ symbol, symbol ∈ rest → symbol ≠ WorkSymbol.blank := by
        intro symbol hSymbol
        exact hScan symbol (List.Mem.tail first hSymbol)
      have hOne := relayRunExact_one
        { state := scanState
          tape := leftPathTape right
            (first :: rest ++ WorkSymbol.blank :: tail) }
        { state := scanState
          tape := leftPathTape (first :: right)
            (rest ++ WorkSymbol.blank :: tail) }
        (by
          simpa using
            (hNonblank
              (leftPathTape right
                (first :: rest ++ WorkSymbol.blank :: tail)) hFirst))
      have hTail := inductionHypothesis tail (first :: right) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose relayMachine
        1 (rest.length + 1) _ _ _ hOne hTail
      have hSteps :
          1 + (rest.length + 1) = (first :: rest).length + 1 := by
        simp only [List.length_cons]
        omega
      rw [← hSteps]
      simpa [List.reverse_cons, List.append_assoc] using hAll

theorem relayBody_prefix_exact
    (scanWord tail right : List WorkSymbol)
    (hScan : ∀ symbol, symbol ∈ scanWord → symbol ≠ WorkSymbol.blank) :
    workRunExact? relayMachine (scanWord.length + 2)
        { state := relayStartState
          tape := leftPathTape right
            (unitSymbol :: scanWord ++ WorkSymbol.blank :: tail) } =
      some
        { state := relayAcceptState
          tape :=
            { left := tail
              head := bodyPendingSymbol
              right := (unitSymbol :: scanWord).reverse ++ right } } := by
  have hStart := relayRunExact_one
    { state := relayStartState
      tape := leftPathTape right
        (unitSymbol :: scanWord ++ WorkSymbol.blank :: tail) }
    { state := relayBodyScanState
      tape := leftPathTape (unitSymbol :: right)
        (scanWord ++ WorkSymbol.blank :: tail) }
    (by
      simpa using
        (relayStart_body_workStep
          (leftPathTape right
            (unitSymbol :: scanWord ++ WorkSymbol.blank :: tail)) rfl))
  have hScanRun := relayScan_prefix_exact relayBodyScanState
    bodyPendingSymbol relayBodyScan_nonblank_workStep
    relayBodyScan_blank_workStep scanWord tail (unitSymbol :: right) hScan
  have hAll := PipelineMachineSimulation.workRunExact?_compose relayMachine
    1 (scanWord.length + 1) _ _ _ hStart hScanRun
  have hSteps : 1 + (scanWord.length + 1) = scanWord.length + 2 := by omega
  rw [← hSteps]
  simpa [List.reverse_cons, List.append_assoc] using hAll

theorem relayFinish_prefix_exact
    (scanWord tail right : List WorkSymbol)
    (hScan : ∀ symbol, symbol ∈ scanWord → symbol ≠ WorkSymbol.blank) :
    workRunExact? relayMachine (scanWord.length + 2)
        { state := relayStartState
          tape := leftPathTape right
            (endSymbol :: scanWord ++ WorkSymbol.blank :: tail) } =
      some
        { state := relayAcceptState
          tape :=
            { left := tail
              head := BuilderPhysicalOptionalTokenDispatch.requestSymbol
                (some CNFToken.finish)
              right := (endSymbol :: scanWord).reverse ++ right } } := by
  have hStart := relayRunExact_one
    { state := relayStartState
      tape := leftPathTape right
        (endSymbol :: scanWord ++ WorkSymbol.blank :: tail) }
    { state := relayFinishScanState
      tape := leftPathTape (endSymbol :: right)
        (scanWord ++ WorkSymbol.blank :: tail) }
    (by
      simpa using
        (relayStart_finish_workStep
          (leftPathTape right
            (endSymbol :: scanWord ++ WorkSymbol.blank :: tail)) rfl))
  have hScanRun := relayScan_prefix_exact relayFinishScanState
    (BuilderPhysicalOptionalTokenDispatch.requestSymbol
      (some CNFToken.finish)) relayFinishScan_nonblank_workStep
    relayFinishScan_blank_workStep scanWord tail (endSymbol :: right) hScan
  have hAll := PipelineMachineSimulation.workRunExact?_compose relayMachine
    1 (scanWord.length + 1) _ _ _ hStart hScanRun
  have hSteps : 1 + (scanWord.length + 1) = scanWord.length + 2 := by omega
  rw [← hSteps]
  simpa [List.reverse_cons, List.append_assoc] using hAll

def routeCell {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkSymbol :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val with
  | .body _ _ => bodyPendingSymbol
  | .finish =>
      BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)
  | .outOfRange => WorkSymbol.blank

def relayEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  { state := relayMachine.startState
    tape := (classifierFinalConfiguration problem index
      (classifierWorkspace problem index)).tape }

def classifierTrail {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  let final := classifierFinalConfiguration problem index
    (classifierWorkspace problem index)
  (final.tape.head :: classifierPrefix problem index).reverse ++
    final.tape.right

def relayFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  { state := relayMachine.acceptState
    tape :=
      { left := builderWord problem index
        head := routeCell problem index
        right := classifierTrail problem index } }

def relayWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) : Nat :=
  (classifierPrefix problem index).length + 2

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
  have hScan : ∀ symbol, symbol ∈ classifierPrefix problem index →
      symbol ≠ WorkSymbol.blank := by
    intro symbol hSymbol hBlank
    exact blank_not_mem_classifierPrefix problem index (hBlank ▸ hSymbol)
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      have hHead := classifierFinal_head_eq_unit_of_body problem index
        (classifierWorkspace problem index) clauseCoordinate tokenCoordinate
        hRoute
      have hRun := relayBody_prefix_exact
        (classifierPrefix problem index) (builderWord problem index)
        final.tape.right hScan
      have hEntry :
          { state := relayStartState
            tape := leftPathTape final.tape.right
              (unitSymbol :: classifierPrefix problem index ++
                WorkSymbol.blank :: builderWord problem index) } =
            relayEntryConfiguration problem index := by
        apply workConfiguration_ext
        · rfl
        · apply workTape_ext
          · simpa [leftPathTape, relayEntryConfiguration,
              classifierWorkspace, final] using hLeft.symm
          · change unitSymbol = final.tape.head
            exact hHead.symm
          · rfl
      rw [← hEntry]
      simpa [relayWorkSteps, relayFinalConfiguration, routeCell, hRoute,
        classifierTrail, final, hHead, relayMachine] using hRun
  | finish =>
      have hHead := classifierFinal_head_eq_end_of_finish problem index
        (classifierWorkspace problem index) hRoute
      have hRun := relayFinish_prefix_exact
        (classifierPrefix problem index) (builderWord problem index)
        final.tape.right hScan
      have hEntry :
          { state := relayStartState
            tape := leftPathTape final.tape.right
              (endSymbol :: classifierPrefix problem index ++
                WorkSymbol.blank :: builderWord problem index) } =
            relayEntryConfiguration problem index := by
        apply workConfiguration_ext
        · rfl
        · apply workTape_ext
          · simpa [leftPathTape, relayEntryConfiguration,
              classifierWorkspace, final] using hLeft.symm
          · change endSymbol = final.tape.head
            exact hHead.symm
          · rfl
      rw [← hEntry]
      simpa [relayWorkSteps, relayFinalConfiguration, routeCell, hRoute,
        classifierTrail, final, hHead, relayMachine] using hRun
  | outOfRange =>
      exact False.elim (route_ne_outOfRange problem index hRoute)

/-! ## Terminal-joined classifier followed by the route relay -/

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
  BuilderPhysicalClassifierTerminalJoin.workSteps problem index + 1 +
    relayWorkSteps problem index

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
    classifierRelayMachine.rules.length = 749 := by rfl

theorem classifierRelayRules_pairwise_query_distinct :
    classifierRelayMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    classifierMachine relayMachine
    BuilderPhysicalClassifierTerminalJoin.rules_pairwise_query_distinct
    relayRules_pairwise_query_distinct
    BuilderPhysicalClassifierTerminalJoin.noRuleAtAccept

theorem classifierRelayMachine_acceptState_ne_rejectState :
    classifierRelayMachine.acceptState ≠
      classifierRelayMachine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    classifierMachine relayMachine relayMachine_acceptState_ne_rejectState

/-! ## Body-pending terminal plus reflected optional-token dispatcher -/

def bodyPendingRule : WorkRule :=
  { sourceState := mirroredDispatchMachine.startState
    readSymbol := bodyPendingSymbol
    targetState := mirroredDispatchMachine.rejectState
    writeSymbol := bodyPendingSymbol
    move := .stay }

def dispatchRules : List WorkRule :=
  mirroredDispatchMachine.rules ++ [bodyPendingRule]

def dispatchMachine : WorkMachine :=
  { rules := dispatchRules
    startState := mirroredDispatchMachine.startState
    acceptState := mirroredDispatchMachine.acceptState
    rejectState := mirroredDispatchMachine.rejectState }

theorem dispatchRules_length : dispatchRules.length = 65 := by rfl

set_option maxRecDepth 1000000 in
theorem dispatchRules_pairwise_query_distinct :
    dispatchRules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide +revert

theorem dispatchMachine_acceptState_ne_rejectState :
    dispatchMachine.acceptState ≠ dispatchMachine.rejectState := by
  exact BuilderPhysicalClassifierFinishMirroredDispatch.mirrorMachine_acceptState_ne_rejectState
    sourceDispatchMachine
    BuilderPhysicalOptionalTokenDispatch.machine_acceptState_ne_rejectState

theorem dispatch_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept dispatchMachine := by
  intro rule hRule
  change rule ∈ dispatchRules at hRule
  change rule.sourceState ≠ mirroredDispatchMachine.acceptState
  decide +revert

theorem bodyPending_workStep (left right : List WorkSymbol) :
    workStep? dispatchMachine
        { state := dispatchMachine.startState
          tape := { left := left, head := bodyPendingSymbol, right := right } } =
      some
        { state := dispatchMachine.rejectState
          tape := { left := left, head := bodyPendingSymbol, right := right } } := by
  rfl

private theorem dispatchRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? dispatchMachine start = some next) :
    workRunExact? dispatchMachine 1 start = some next := by
  change
    (match workStep? dispatchMachine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem mirroredDispatch_workStep_of_some
    (configuration next : WorkConfiguration)
    (hStep : workStep? mirroredDispatchMachine configuration = some next) :
    workStep? dispatchMachine configuration = some next := by
  rcases workStep?_some_exists mirroredDispatchMachine configuration next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hGlobalHalted : dispatchMachine.isHalted configuration = false := by
    change mirroredDispatchMachine.isHalted configuration = false
    exact hHalted
  have hGlobalFind : findWorkRule dispatchMachine.rules
      configuration.state configuration.tape.head = some rule := by
    unfold dispatchMachine dispatchRules
    exact findWorkRule_append_of_some _ _ _ _ _ hFind
  have hGlobalStep := workStep?_eq_apply_of_find dispatchMachine configuration
    rule hGlobalHalted hGlobalFind
  simpa [hNext] using hGlobalStep

private theorem mirroredDispatch_workRunExact
    (steps : Nat) (initial final : WorkConfiguration)
    (hRun : workRunExact? mirroredDispatchMachine steps initial = some final) :
    workRunExact? dispatchMachine steps initial = some final := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    mirroredDispatchMachine dispatchMachine (fun state => state)
    mirroredDispatch_workStep_of_some steps initial final hRun
  simpa [renameConfiguration] using hTransport

theorem canonicalRequest_eq_finish_of_route {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .finish) :
    BuilderPhysicalOptionalTokenDispatch.canonicalRequest problem index =
      some .finish := by
  have hSelected := selectedEntry?_eq_some_getElem problem index
  have hFinish := selectedEntry?_finish problem index.val hRoute
  unfold BuilderPhysicalOptionalTokenDispatch.canonicalRequest
  rw [hSelected] at hFinish
  exact Option.some.inj hFinish

def dispatchEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  { state := dispatchMachine.startState
    tape := (relayFinalConfiguration problem index).tape }

def bodyFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  { state := dispatchMachine.rejectState
    tape := (relayFinalConfiguration problem index).tape }

def finishDispatchFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
    (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
      (BuilderTokenAppender.finalConfiguration problem.input
        (classifierTrail problem index)
        (emittedPrefix problem (index.val + 1))))

def dispatchFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val with
  | .body _ _ => bodyFinalConfiguration problem index
  | .finish => finishDispatchFinalConfiguration problem index
  | .outOfRange => bodyFinalConfiguration problem index

def dispatchWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) : Nat :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val with
  | .body _ _ => 1
  | .finish => BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem index
  | .outOfRange => 0

theorem dispatch_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? dispatchMachine (dispatchWorkSteps problem index)
        (dispatchEntryConfiguration problem index) =
      some (dispatchFinalConfiguration problem index) := by
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      have hStep := bodyPending_workStep (builderWord problem index)
        (classifierTrail problem index)
      have hRun := dispatchRunExact_one
        { state := dispatchMachine.startState
          tape :=
            { left := builderWord problem index
              head := bodyPendingSymbol
              right := classifierTrail problem index } }
        { state := dispatchMachine.rejectState
          tape :=
            { left := builderWord problem index
              head := bodyPendingSymbol
              right := classifierTrail problem index } }
        hStep
      simpa [dispatchWorkSteps, dispatchEntryConfiguration,
        dispatchFinalConfiguration, bodyFinalConfiguration,
        relayFinalConfiguration, routeCell, hRoute] using
        hRun
  | finish =>
      have hRequest := canonicalRequest_eq_finish_of_route problem index hRoute
      have hBase := BuilderPhysicalOptionalTokenDispatch.canonical_workRunExact
        problem index (classifierTrail problem index)
      have hMirror :=
        BuilderPhysicalClassifierFinishMirroredDispatch.workRunExact?_mirror_of_some
          sourceDispatchMachine
          (BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem index)
          (BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
            (classifierTrail problem index) (output problem index)
            (BuilderPhysicalOptionalTokenDispatch.canonicalRequest problem index))
          (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
            (BuilderTokenAppender.finalConfiguration problem.input
              (classifierTrail problem index)
              (emittedPrefix problem (index.val + 1)))) (by
            simpa [output] using hBase)
      have hExtended := mirroredDispatch_workRunExact
        (BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem index)
        _ _ hMirror
      rw [hRequest] at hExtended
      have hEntry : dispatchEntryConfiguration problem index =
          BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
            (BuilderPhysicalOptionalTokenDispatch.entryConfiguration
              problem.input (classifierTrail problem index)
              (output problem index) (some CNFToken.finish)) := by
        apply workConfiguration_ext
        · rfl
        · cases hInput : problem.input <;>
            simp [dispatchEntryConfiguration, relayFinalConfiguration,
              routeCell, hRoute, builderWord, output,
              BuilderPhysicalOptionalTokenDispatch.entryConfiguration,
              BuilderPhysicalOptionalTokenDispatch.requestTape,
              BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration,
              BuilderPhysicalClassifierFinishMirroredDispatch.mirrorTape,
              BuilderPhysicalClassifierFinishWorkspaceOrientation.mirrorTape,
              BuilderTokenAppender.workspaceTape, frameWithGarbage, hInput]
      rw [dispatchWorkSteps, hRoute, dispatchFinalConfiguration, hRoute,
        hEntry]
      simpa [finishDispatchFinalConfiguration] using hExtended
  | outOfRange =>
      exact False.elim (route_ne_outOfRange problem index hRoute)

/-! ## Complete classifier, route relay, and conditional Finish dispatch -/

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

theorem relayFinal_tape_eq_dispatchEntry {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    (relayFinalConfiguration problem index).tape =
      (dispatchEntryConfiguration problem index).tape := by
  rfl

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
theorem rules_length : machine.rules.length = 823 := by rfl

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
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index)) =
      encodeWorkConfiguration (finalConfiguration problem index) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps problem index) (entryConfiguration problem index)
    (finalConfiguration problem index) (workRunExact problem index)

private theorem workRunExact_succ_split_last (selectedMachine : WorkMachine) :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? selectedMachine (steps + 1) initial = some final →
      ∃ before,
        workRunExact? selectedMachine steps initial = some before ∧
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
  unfold workSteps classifierRelayWorkSteps
  omega

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index)) = false := by
  let short := workSteps problem index - 1
  have hSucc : short + 1 = workSteps problem index := by
    have hPositive := workSteps_positive problem index
    dsimp [short]
    omega
  have hExact := workRunExact problem index
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last machine short
      (entryConfiguration problem index) (finalConfiguration problem index)
      hExact with ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short (entryConfiguration problem index) =
      before :=
    workRun_eq_of_workRunExact machine short (entryConfiguration problem index)
      before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine before
    (finalConfiguration problem index) hLast

/-! ## Route-specific terminal contract and polynomial bound -/

def RouteTerminalHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Prop :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val with
  | .body _ _ =>
      (finalConfiguration problem index).state = machine.rejectState ∧
      (finalConfiguration problem index).tape.left = builderWord problem index ∧
      (finalConfiguration problem index).tape.head = bodyPendingSymbol ∧
      (finalConfiguration problem index).tape.right = classifierTrail problem index
  | .finish =>
      (finalConfiguration problem index).state = machine.acceptState ∧
      (finalConfiguration problem index).tape =
        (BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
          (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
            (BuilderTokenAppender.finalConfiguration problem.input
              (classifierTrail problem index)
              (emittedPrefix problem (index.val + 1))))).tape
  | .outOfRange => False

theorem routeTerminalHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    RouteTerminalHolds problem index := by
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      simp [RouteTerminalHolds, hRoute, finalConfiguration,
        dispatchFinalConfiguration, bodyFinalConfiguration, machine,
        relayFinalConfiguration, routeCell, renameConfiguration,
        WorkMachineChain.machine, dispatchMachine]
  | finish =>
      simp [RouteTerminalHolds, hRoute, finalConfiguration,
        dispatchFinalConfiguration, finishDispatchFinalConfiguration, machine,
        renameConfiguration, WorkMachineChain.machine, dispatchMachine,
        BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration,
        mirroredDispatchMachine, sourceDispatchMachine,
        BuilderPhysicalClassifierFinishMirroredDispatch.mirrorMachine,
        BuilderPhysicalOptionalTokenDispatch.machine,
        BuilderPhysicalOptionalTokenDispatch.appenderState,
        BuilderTokenAppender.finalConfiguration]
  | outOfRange =>
      exact False.elim (route_ne_outOfRange problem index hRoute)

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.rawTimeBound
    verifier

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrevious :=
    BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.compiledSteps_le_rawTimeBound
      problem index
  have hStepLe : workSteps problem index ≤
      BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.workSteps
        problem index := by
    cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
        problem index.val with
    | body clauseCoordinate tokenCoordinate =>
        unfold workSteps classifierRelayWorkSteps relayWorkSteps dispatchWorkSteps
          BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.workSteps
          BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.classifierRelayWorkSteps
          BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.relayWorkSteps
          BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.dispatchWorkSteps
        rw [hRoute]
        simp only [classifierPrefix]
        omega
    | finish =>
        unfold workSteps classifierRelayWorkSteps relayWorkSteps dispatchWorkSteps
          BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.workSteps
          BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.classifierRelayWorkSteps
          BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.relayWorkSteps
          BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.dispatchWorkSteps
        rw [hRoute]
        simp only [classifierPrefix]
        omega
    | outOfRange =>
        exact False.elim (route_ne_outOfRange problem index hRoute)
  exact Nat.le_trans (Nat.mul_le_mul_left 6 hStepLe) (by
    simpa [rawTimeBound] using hPrevious)

def AllRouteDerivedFinishSplitHolds {language : Language}
    (problem : VerifierTableauProblem language) : Prop :=
  ∀ index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem),
    classifierWorkspace problem index =
        WorkSymbol.blank :: builderWord problem index ∧
    workRunExact? relayMachine (relayWorkSteps problem index)
        (relayEntryConfiguration problem index) =
      some (relayFinalConfiguration problem index) ∧
    workRunExact? dispatchMachine (dispatchWorkSteps problem index)
        (dispatchEntryConfiguration problem index) =
      some (dispatchFinalConfiguration problem index) ∧
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index) =
      some (finalConfiguration problem index) ∧
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index)) =
      encodeWorkConfiguration (finalConfiguration problem index) ∧
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index)) = false ∧
    RouteTerminalHolds problem index ∧
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length

theorem allRouteDerivedFinishSplitHolds {language : Language}
    (problem : VerifierTableauProblem language) :
    AllRouteDerivedFinishSplitHolds problem := by
  intro index
  exact ⟨rfl, relay_workRunExact problem index,
    dispatch_workRunExact problem index, workRunExact problem index,
    run_compile_exact problem index, one_step_short_not_halted problem index,
    routeTerminalHolds problem index,
    compiledSteps_le_rawTimeBound problem index⟩

/-- M228 removes M227's staged optional-token cell and closes the physical
all-coordinate classifier-to-request-control edge. One collision-free
823-rule machine derives body versus Finish from the classifier terminal,
halts every body route at an explicit request-pending marker, and dispatches
the derived Finish request to the exact next canonical emitted prefix. Exact
work, compiled, one-step-short, route-terminal, and source-size polynomial
evidence hold over the complete post-header schedule. Arbitrary body-token
and padding synthesis, raw clause selection, successive-coordinate
connection, the repeated builder loop, builder RawRefinement, and the packaged
Cook--Levin reduction remain open. -/
theorem cook_levin_builder_physical_classifier_all_route_derived_finish_split_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    relayMachine.rules.length = 20 ∧
    classifierRelayMachine.rules.length = 749 ∧
    dispatchMachine.rules.length = 65 ∧
    machine.rules.length = 823 ∧
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) ∧
    machine.acceptState ≠ machine.rejectState ∧
    (∀ request, bodyPendingSymbol ≠
      BuilderPhysicalOptionalTokenDispatch.requestSymbol request) ∧
    AllRouteDerivedFinishSplitHolds problem := by
  exact ⟨relayRules_length, classifierRelayRules_length,
    dispatchRules_length, rules_length, rules_pairwise_query_distinct,
    machine_acceptState_ne_rejectState, bodyPendingSymbol_ne_requestSymbol,
    allRouteDerivedFinishSplitHolds problem⟩

end BuilderPhysicalClassifierAllRouteDerivedFinishSplit

end PNP.Concrete.CookLevin
