/-
Copyright (c) 2026 PNP Labs.

A fixed workspace-orientation pass after the complete physical classifier's
Finish-request writer.

The classifier preserves arbitrary builder data on its left while accumulating
its own finite routing evidence closer to the head.  This module inserts one
blank sentinel before the canonical builder workspace, then uses a literal
finite scanner to cross exactly the classifier prefix and halt at the sentinel.
The final tape is the spatial mirror of M217's canonical Finish-dispatch entry.

Mirrored dispatcher execution, body-token and padding request generation, a
repeated physical loop, builder RawRefinement, and the packaged Cook--Levin
reduction remain open.
-/

import PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishRequest

namespace PNP.Concrete.CookLevin

namespace BuilderPhysicalClassifierFinishWorkspaceOrientation

open PipelineStateNamespace
open BuilderPostDividerSelectedTokenLaunch

abbrev finishIndex {language : Language}
    (problem : VerifierTableauProblem language) :=
  BuilderPhysicalClassifierFinishRequest.finishIndex problem

def classifierPrefix {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration
    problem []).tape.left

private theorem blank_ne_unit :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.unitSymbol := by
  decide

private theorem blank_ne_separator :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.separatorSymbol := by
  decide

private theorem blank_ne_end :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.endSymbol := by
  decide

private theorem blank_ne_coordinate :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.coordinateMark := by
  decide

private theorem blank_ne_boundary :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.boundaryMark := by
  decide

private theorem blank_ne_left_boundary :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.leftBoundary := by
  decide

private theorem blank_ne_raw_left_boundary :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.leftBoundary := by
  decide

private theorem blank_ne_consumed :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.consumedDividend := by
  decide

private theorem blank_ne_copied_width :
    WorkSymbol.blank ≠ BuilderPostHeaderRawTapeBridge.copiedWidthMark := by
  decide

private theorem blank_ne_copied_remainder :
    WorkSymbol.blank ≠ BuilderPostHeaderRawTapeBridge.copiedRemainderMark := by
  decide

private theorem workTape_ext {left right : WorkTape}
    (hLeft : left.left = right.left)
    (hHead : left.head = right.head)
    (hRight : left.right = right.right) :
    left = right := by
  cases left
  cases right
  simp_all

theorem classifierFinal_left_append {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration
      problem workspace).tape.left =
      classifierPrefix problem ++ workspace := by
  cases hValue : (finishIndex problem).val with
  | zero =>
      simp [BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalClassifierExterior,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.sidecar,
        classifierPrefix, renameConfiguration,
        List.append_assoc]
  | succ remaining =>
      simp [BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.sidecar,
        classifierPrefix, renameConfiguration,
        List.append_assoc]

theorem classifierFinal_right_nil {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration
      problem workspace).tape.right = [] := by
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  have hFinish := BuilderPhysicalFinishRequest.finishIndex_postHeaderRoute problem
  have hIndex :=
    (BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_eq_finish_iff
      problem (finishIndex problem).val).1 hFinish
  have hQuotient :
      (finishIndex problem).val /
          BuilderPhysicalClassifierPipeline.width problem =
        BuilderPhysicalClassifierPipeline.clauseCount problem := by
    rw [hIndex]
    simpa [BuilderPhysicalClassifierPipeline.width,
      BuilderPhysicalClassifierPipeline.clauseCount, Nat.mul_comm] using
        (Nat.mul_div_right problem.formulaClauseSlotCount hWidth)
  cases hValue : (finishIndex problem).val with
  | zero =>
      have hCount :
          BuilderPhysicalClassifierPipeline.clauseCount problem = 0 := by
        simpa [hValue] using hQuotient.symm
      simp [BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        BuilderPostDividerRawRouteClassifier.compareResult_self, hCount,
        renameConfiguration]
  | succ remaining =>
      have hGreaterQuotient :
          BuilderPhysicalClassifierPipeline.greaterQuotient problem remaining =
            BuilderPhysicalClassifierPipeline.clauseCount problem := by
        unfold BuilderPhysicalClassifierPipeline.greaterQuotient
        rw [← hValue]
        exact hQuotient
      simp [BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        BuilderPostDividerRawRouteClassifier.compareResult_self,
        hGreaterQuotient, renameConfiguration]

theorem blank_not_mem_classifierPrefix {language : Language}
    (problem : VerifierTableauProblem language) :
    WorkSymbol.blank ∉ classifierPrefix problem := by
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  have hFinish := BuilderPhysicalFinishRequest.finishIndex_postHeaderRoute problem
  have hIndex :=
    (BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_eq_finish_iff
      problem (finishIndex problem).val).1 hFinish
  have hQuotient :
      (finishIndex problem).val /
          BuilderPhysicalClassifierPipeline.width problem =
        BuilderPhysicalClassifierPipeline.clauseCount problem := by
    rw [hIndex]
    simpa [BuilderPhysicalClassifierPipeline.width,
      BuilderPhysicalClassifierPipeline.clauseCount, Nat.mul_comm] using
        (Nat.mul_div_right problem.formulaClauseSlotCount hWidth)
  cases hValue : (finishIndex problem).val with
  | zero =>
      have hCount :
          BuilderPhysicalClassifierPipeline.clauseCount problem = 0 := by
        simpa [hValue] using hQuotient.symm
      simp [classifierPrefix,
        BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
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
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        BuilderPostDividerRawRouteClassifier.compareResult_self, hCount,
        renameConfiguration, blank_ne_unit, blank_ne_separator,
        blank_ne_end, blank_ne_coordinate, blank_ne_boundary,
        blank_ne_left_boundary, blank_ne_raw_left_boundary,
        blank_ne_copied_width]
  | succ remaining =>
      have hGreaterQuotient :
          BuilderPhysicalClassifierPipeline.greaterQuotient problem remaining =
            BuilderPhysicalClassifierPipeline.clauseCount problem := by
        unfold BuilderPhysicalClassifierPipeline.greaterQuotient
        rw [← hValue]
        exact hQuotient
      simp [classifierPrefix,
        BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior,
        BuilderPhysicalClassifierPipeline.greaterConsumed,
        BuilderPhysicalClassifierPipeline.greaterRemainder,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.sidecar,
        BuilderPostDividerRawRouteClassifier.terminalPrefix,
        BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix,
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        BuilderPostDividerRawRouteClassifier.compareResult_self,
        hGreaterQuotient, renameConfiguration, blank_ne_unit,
        blank_ne_separator, blank_ne_end, blank_ne_coordinate,
        blank_ne_boundary, blank_ne_left_boundary,
        blank_ne_raw_left_boundary, blank_ne_consumed,
        blank_ne_copied_width, blank_ne_copied_remainder]

theorem classifierPrefix_length_le {language : Language}
    (problem : VerifierTableauProblem language) :
    (classifierPrefix problem).length ≤
      12 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1) := by
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  have hFinish := BuilderPhysicalFinishRequest.finishIndex_postHeaderRoute problem
  have hIndex :=
    (BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_eq_finish_iff
      problem (finishIndex problem).val).1 hFinish
  have hQuotient :
      (finishIndex problem).val /
          BuilderPhysicalClassifierPipeline.width problem =
        BuilderPhysicalClassifierPipeline.clauseCount problem := by
    rw [hIndex]
    simpa [BuilderPhysicalClassifierPipeline.width,
      BuilderPhysicalClassifierPipeline.clauseCount, Nat.mul_comm] using
        (Nat.mul_div_right problem.formulaClauseSlotCount hWidth)
  have hBody := BuilderFullScheduleCursorController.bodySlotCount_eq problem
  cases hValue : (finishIndex problem).val with
  | zero =>
      have hCount :
          BuilderPhysicalClassifierPipeline.clauseCount problem = 0 := by
        simpa [hValue] using hQuotient.symm
      simp [classifierPrefix,
        BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
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
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        BuilderPostDividerRawRouteClassifier.compareResult_self, hCount,
        renameConfiguration] at *
      omega
  | succ remaining =>
      have hGreaterQuotient :
          BuilderPhysicalClassifierPipeline.greaterQuotient problem remaining =
            BuilderPhysicalClassifierPipeline.clauseCount problem := by
        unfold BuilderPhysicalClassifierPipeline.greaterQuotient
        rw [← hValue]
        exact hQuotient
      have hDiv :=
        BuilderPostHeaderRawDivider.quotient_remainder_reconstruct
          (remaining + 1) (BuilderPhysicalClassifierPipeline.width problem)
      have hClauseCountLe :
          BuilderPhysicalClassifierPipeline.clauseCount problem ≤ remaining + 1 := by
        rw [← hQuotient, hValue]
        exact Nat.div_le_self _ _
      simp [classifierPrefix,
        BuilderPhysicalClassifierFinishRequest.classifierFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hValue,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior,
        BuilderPhysicalClassifierPipeline.greaterConsumed,
        BuilderPhysicalClassifierPipeline.greaterRemainder,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.sidecar,
        BuilderPostDividerRawRouteClassifier.terminalPrefix,
        BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix,
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        BuilderPostDividerRawRouteClassifier.compareResult_self,
        hGreaterQuotient, renameConfiguration] at *
      omega

/-! ## Fixed blank-sentinel workspace orienter -/

abbrev requestSymbol : WorkSymbol :=
  BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)

def orientStartState : Nat := 0
def orientScanState : Nat := 1
def orientAcceptState : Nat := 2
def orientRejectState : Nat := 3

def orientStartRule : WorkRule :=
  { sourceState := orientStartState
    readSymbol := requestSymbol
    targetState := orientScanState
    writeSymbol := requestSymbol
    move := .left }

def orientScanRule (symbol : WorkSymbol) : WorkRule :=
  if symbol == WorkSymbol.blank then
    { sourceState := orientScanState
      readSymbol := symbol
      targetState := orientAcceptState
      writeSymbol := requestSymbol
      move := .stay }
  else
    { sourceState := orientScanState
      readSymbol := symbol
      targetState := orientScanState
      writeSymbol := symbol
      move := .left }

def orientRules : List WorkRule :=
  orientStartRule ::
    PipelineMachineSimulation.allWorkSymbols.map orientScanRule

def orientMachine : WorkMachine :=
  { rules := orientRules
    startState := orientStartState
    acceptState := orientAcceptState
    rejectState := orientRejectState }

theorem orientRules_length : orientRules.length = 10 := by
  rfl

theorem orientRules_pairwise_query_distinct :
    orientRules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem orientMachine_acceptState_ne_rejectState :
    orientMachine.acceptState ≠ orientMachine.rejectState := by
  decide

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

private theorem workRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? orientMachine start = some next) :
    workRunExact? orientMachine 1 start = some next := by
  change
    (match workStep? orientMachine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

theorem orientStart_workStep (left right : List WorkSymbol) :
    workStep? orientMachine
        { state := orientStartState
          tape := { left := left, head := requestSymbol, right := right } } =
      some
        { state := orientScanState
          tape :=
            ({ left := left, head := requestSymbol, right := right } :
              WorkTape).moveLeft } := by
  rfl

theorem orientScan_nonblank_workStep (tape : WorkTape)
    (hHead : tape.head ≠ WorkSymbol.blank) :
    workStep? orientMachine
        { state := orientScanState, tape := tape } =
      some { state := orientScanState, tape := tape.moveLeft } := by
  rcases tape with ⟨left, ⟨first, second⟩, right⟩
  cases first <;> cases second
  all_goals first | exact False.elim (hHead rfl) | rfl

theorem orientScan_blank_workStep (left right : List WorkSymbol) :
    workStep? orientMachine
        { state := orientScanState
          tape := { left := left, head := WorkSymbol.blank, right := right } } =
      some
        { state := orientAcceptState
          tape := { left := left, head := requestSymbol, right := right } } := by
  rfl

private theorem orientScan_prefix_exact (scanWord tail right : List WorkSymbol)
    (hScanWord : ∀ symbol ∈ scanWord, symbol ≠ WorkSymbol.blank) :
    workRunExact? orientMachine (scanWord.length + 1)
        { state := orientScanState
          tape := leftPathTape right
            (scanWord ++ WorkSymbol.blank :: tail) } =
      some
        { state := orientAcceptState
          tape :=
            { left := tail
              head := requestSymbol
              right := scanWord.reverse ++ right } } := by
  induction scanWord generalizing right with
  | nil =>
      simpa using workRunExact_one
        { state := orientScanState
          tape := leftPathTape right (WorkSymbol.blank :: tail) }
        { state := orientAcceptState
          tape := { left := tail, head := requestSymbol, right := right } }
        (orientScan_blank_workStep tail right)
  | cons first rest ih =>
      have hFirst : first ≠ WorkSymbol.blank :=
        hScanWord first (List.Mem.head rest)
      have hRest : ∀ symbol ∈ rest, symbol ≠ WorkSymbol.blank := by
        intro symbol hSymbol
        exact hScanWord symbol (List.Mem.tail first hSymbol)
      have hOne := workRunExact_one
        { state := orientScanState
          tape := leftPathTape right
            (first :: rest ++ WorkSymbol.blank :: tail) }
        { state := orientScanState
          tape := leftPathTape (first :: right)
            (rest ++ WorkSymbol.blank :: tail) } (by
          simpa using orientScan_nonblank_workStep
            (leftPathTape right
              (first :: rest ++ WorkSymbol.blank :: tail)) hFirst)
      have hTail := ih (first :: right) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose orientMachine
        1 (rest.length + 1) _ _ _ hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm] using hAll

def orientEntryConfiguration (scanWord builderWord : List WorkSymbol) :
    WorkConfiguration :=
  { state := orientMachine.startState
    tape :=
      { left := scanWord ++ WorkSymbol.blank :: builderWord
        head := requestSymbol
        right := [] } }

def orientFinalConfiguration (scanWord builderWord : List WorkSymbol) :
    WorkConfiguration :=
  { state := orientMachine.acceptState
    tape :=
      { left := builderWord
        head := requestSymbol
        right := scanWord.reverse ++ [requestSymbol] } }

def orientWorkSteps (scanWord : List WorkSymbol) : Nat :=
  scanWord.length + 2

theorem orient_workRunExact (scanWord builderWord : List WorkSymbol)
    (hScanWord : ∀ symbol ∈ scanWord,
      symbol ≠ WorkSymbol.blank) :
    workRunExact? orientMachine (orientWorkSteps scanWord)
        (orientEntryConfiguration scanWord builderWord) =
      some (orientFinalConfiguration scanWord builderWord) := by
  have hStart := workRunExact_one
    (orientEntryConfiguration scanWord builderWord)
    { state := orientScanState
      tape := leftPathTape [requestSymbol]
        (scanWord ++ WorkSymbol.blank :: builderWord) } (by
      have hMove :
          ({ left := scanWord ++ WorkSymbol.blank :: builderWord
             head := requestSymbol
             right := [] } : WorkTape).moveLeft =
            leftPathTape [requestSymbol]
              (scanWord ++ WorkSymbol.blank :: builderWord) := by
        cases scanWord <;> rfl
      rw [← hMove]
      simpa [orientEntryConfiguration, orientMachine] using
        orientStart_workStep
          (scanWord ++ WorkSymbol.blank :: builderWord) [])
  have hScan := orientScan_prefix_exact scanWord builderWord [requestSymbol]
    hScanWord
  have hAll := PipelineMachineSimulation.workRunExact?_compose orientMachine
    1 (scanWord.length + 1) _ _ _ hStart hScan
  have hSteps : 1 + (scanWord.length + 1) = orientWorkSteps scanWord := by
    unfold orientWorkSteps
    omega
  rw [← hSteps]
  simpa [orientFinalConfiguration, orientMachine] using hAll

/-! ## Canonical full-classifier composition -/

def output {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  emittedPrefix problem (finishIndex problem).val

def builderWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  let workspace := BuilderTokenAppender.workspaceTape problem.input []
    (output problem)
  workspace.head :: workspace.right

def classifierWorkspace {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  WorkSymbol.blank :: builderWord problem

def classifierWriterEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  BuilderPhysicalClassifierFinishRequest.entryConfiguration problem
    (classifierWorkspace problem)

def classifierWriterFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  BuilderPhysicalClassifierFinishRequest.finalConfiguration problem
    (classifierWorkspace problem)

theorem classifierWriterFinal_tape_eq_orientEntry {language : Language}
    (problem : VerifierTableauProblem language) :
    (classifierWriterFinalConfiguration problem).tape =
      (orientEntryConfiguration (classifierPrefix problem)
        (builderWord problem)).tape := by
  unfold classifierWriterFinalConfiguration
  rw [BuilderPhysicalClassifierFinishRequest.final_request_exact]
  apply workTape_ext
  · simpa [orientEntryConfiguration, classifierWorkspace,
      WorkTape.write] using
      classifierFinal_left_append problem (classifierWorkspace problem)
  · rfl
  · simpa [orientEntryConfiguration, WorkTape.write] using
      classifierFinal_right_nil problem (classifierWorkspace problem)

theorem classifierWriterFinal_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (classifierWriterFinalConfiguration problem).state =
      BuilderPhysicalClassifierFinishRequest.machine.acceptState := by
  rfl

abbrev classifierWriterMachine : WorkMachine :=
  BuilderPhysicalClassifierFinishRequest.machine

def composedMachine : WorkMachine :=
  WorkMachineChain.machine classifierWriterMachine orientMachine

def composedEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (classifierWriterEntryConfiguration problem)

def composedFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (orientFinalConfiguration (classifierPrefix problem) (builderWord problem))

def composedWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderPhysicalClassifierFinishRequest.workSteps problem + 1 +
    orientWorkSteps (classifierPrefix problem)

theorem composed_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? composedMachine (composedWorkSteps problem)
        (composedEntryConfiguration problem) =
      some (composedFinalConfiguration problem) := by
  have hFirst := BuilderPhysicalClassifierFinishRequest.workRunExact problem
    (classifierWorkspace problem)
  have hSecond : workRunExact? orientMachine
      (orientWorkSteps (classifierPrefix problem))
      { state := orientMachine.startState
        tape := (classifierWriterFinalConfiguration problem).tape } =
      some (orientFinalConfiguration (classifierPrefix problem)
        (builderWord problem)) := by
    rw [classifierWriterFinal_tape_eq_orientEntry problem]
    exact orient_workRunExact (classifierPrefix problem) (builderWord problem)
      (fun symbol hSymbol hBlank =>
        blank_not_mem_classifierPrefix problem (hBlank ▸ hSymbol))
  have hAll := WorkMachineChain.workRunExact classifierWriterMachine
    orientMachine
    (BuilderPhysicalClassifierFinishRequest.workSteps problem)
    (orientWorkSteps (classifierPrefix problem))
    (classifierWriterEntryConfiguration problem)
    (classifierWriterFinalConfiguration problem)
    (orientFinalConfiguration (classifierPrefix problem) (builderWord problem))
    (by simpa [classifierWriterEntryConfiguration,
      classifierWriterFinalConfiguration] using hFirst)
    (classifierWriterFinal_state problem) hSecond
  simpa [composedMachine, composedWorkSteps, composedEntryConfiguration,
    composedFinalConfiguration] using hAll

set_option maxRecDepth 1000000 in
theorem composedRules_length : composedMachine.rules.length = 740 := by
  rfl

set_option maxRecDepth 1000000 in
private theorem classifierWriter_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept classifierWriterMachine := by
  intro rule hRule
  change rule ∈ BuilderPhysicalClassifierFinishRequest.machine.rules at hRule
  change rule.sourceState ≠
    BuilderPhysicalClassifierFinishRequest.machine.acceptState
  decide +revert

theorem composedRules_pairwise_query_distinct :
    composedMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    classifierWriterMachine orientMachine
    BuilderPhysicalClassifierFinishRequest.rules_pairwise_query_distinct
    orientRules_pairwise_query_distinct
    classifierWriter_noRuleAtAccept

theorem composedMachine_acceptState_ne_rejectState :
    composedMachine.acceptState ≠ composedMachine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    classifierWriterMachine orientMachine
    orientMachine_acceptState_ne_rejectState

theorem composed_run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine composedMachine) (6 * composedWorkSteps problem)
        (encodeWorkConfiguration (composedEntryConfiguration problem)) =
      encodeWorkConfiguration (composedFinalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact composedMachine
    (composedWorkSteps problem) (composedEntryConfiguration problem)
    (composedFinalConfiguration problem) (composed_workRunExact problem)

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
  | succ steps ih =>
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
               | some result => workRunExact? selectedMachine (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
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

theorem composedWorkSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < composedWorkSteps problem := by
  unfold composedWorkSteps
  omega

theorem composed_one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language) :
    composedMachine.isHalted
      (workRun composedMachine (composedWorkSteps problem - 1)
        (composedEntryConfiguration problem)) = false := by
  have hPositive := composedWorkSteps_positive problem
  let short := composedWorkSteps problem - 1
  have hSucc : short + 1 = composedWorkSteps problem := by
    dsimp [short]
    omega
  have hExact := composed_workRunExact problem
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last composedMachine short
      (composedEntryConfiguration problem)
      (composedFinalConfiguration problem) hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun composedMachine short
      (composedEntryConfiguration problem) = before :=
    workRun_eq_of_workRunExact composedMachine short
      (composedEntryConfiguration problem) before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some composedMachine before
    (composedFinalConfiguration problem) hLast

def mirrorTape (tape : WorkTape) : WorkTape :=
  { left := tape.right
    head := tape.head
    right := tape.left }

def dispatchOutsideLeft {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (classifierPrefix problem).reverse ++ [requestSymbol]

theorem composedFinal_tape_eq_mirrored_dispatch_entry {language : Language}
    (problem : VerifierTableauProblem language) :
    (composedFinalConfiguration problem).tape =
      mirrorTape
        (BuilderPhysicalOptionalTokenDispatch.entryConfiguration
          problem.input (dispatchOutsideLeft problem) (output problem)
          (some .finish)).tape := by
  rfl

/-! ## Uniform polynomial bound -/

def orientationSizePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderFullScheduleCursorController.firstBodySlotPolynomial verifier)
    (.add (BuilderFullScheduleCursorController.bodySlotCountPolynomial verifier)
      (.add (formulaClauseTokenPolynomial verifier) (.constant 1)))

def orientationRawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (.constant 84) (orientationSizePolynomial verifier)

private theorem formulaClauseTokenPolynomial_eval_eq_width
    {language : Language} (problem : VerifierTableauProblem language) :
    (formulaClauseTokenPolynomial problem.verifier).eval problem.input.length =
      BuilderPhysicalClassifierPipeline.width problem := by
  have hTokens := problem.formulaClauseTokenPolynomial_eval
  simp only [BitString.size] at hTokens
  simpa [BuilderPhysicalClassifierPipeline.width,
    VerifierTableauProblem.formulaTokensPerClause,
    VerifierTableauProblem.formulaVariableSlotBound, BitString.size] using
      hTokens

theorem orientationRawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (orientationRawTimeBound problem.verifier).eval problem.input.length =
      84 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1) := by
  change
    84 *
      ((BuilderFullScheduleCursorController.firstBodySlotPolynomial
          problem.verifier).eval problem.input.length +
        ((BuilderFullScheduleCursorController.bodySlotCountPolynomial
            problem.verifier).eval problem.input.length +
          ((formulaClauseTokenPolynomial problem.verifier).eval
            problem.input.length + 1))) = _
  rw [formulaClauseTokenPolynomial_eval_eq_width]
  unfold BuilderPhysicalClassifierPipeline.firstBodySlot
    BuilderFullScheduleCursorController.firstBodySlot
    BuilderFullScheduleCursorController.bodySlotCount
  omega

theorem orientCompiledSteps_le_orientationRawTimeBound
    {language : Language} (problem : VerifierTableauProblem language) :
    6 * orientWorkSteps (classifierPrefix problem) ≤
      (orientationRawTimeBound problem.verifier).eval
        problem.input.length := by
  have hPrefix := classifierPrefix_length_le problem
  rw [orientationRawTimeBound_eval]
  unfold orientWorkSteps
  omega

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPhysicalClassifierFinishRequest.rawTimeBound verifier)
    (.add (.constant 6) (orientationRawTimeBound verifier))

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPhysicalClassifierFinishRequest.rawTimeBound
          problem.verifier).eval problem.input.length +
        (6 + (orientationRawTimeBound problem.verifier).eval
          problem.input.length) := by
  rfl

theorem composedCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * composedWorkSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier :=
    BuilderPhysicalClassifierFinishRequest.compiledSteps_le_rawTimeBound
      problem
  have hOrient := orientCompiledSteps_le_orientationRawTimeBound problem
  rw [rawTimeBound_eval]
  unfold composedWorkSteps
  omega

def FinishWorkspaceOrientationHolds {language : Language}
    (problem : VerifierTableauProblem language) : Prop :=
  BuilderPhysicalClassifierFinishRequest.ClassifierFinishRequestHolds problem
      (classifierWorkspace problem) /\
    WorkSymbol.blank ∉ classifierPrefix problem /\
    (classifierPrefix problem).length ≤
      12 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1) /\
    workRunExact? composedMachine (composedWorkSteps problem)
        (composedEntryConfiguration problem) =
      some (composedFinalConfiguration problem) /\
    run (compileWorkMachine composedMachine) (6 * composedWorkSteps problem)
        (encodeWorkConfiguration (composedEntryConfiguration problem)) =
      encodeWorkConfiguration (composedFinalConfiguration problem) /\
    composedMachine.isHalted
      (workRun composedMachine (composedWorkSteps problem - 1)
        (composedEntryConfiguration problem)) = false /\
    (composedFinalConfiguration problem).tape =
      mirrorTape
        (BuilderPhysicalOptionalTokenDispatch.entryConfiguration
          problem.input (dispatchOutsideLeft problem) (output problem)
          (some .finish)).tape

theorem finishWorkspaceOrientationHolds {language : Language}
    (problem : VerifierTableauProblem language) :
    FinishWorkspaceOrientationHolds problem := by
  exact ⟨BuilderPhysicalClassifierFinishRequest.classifierFinishRequestHolds
      problem (classifierWorkspace problem),
    blank_not_mem_classifierPrefix problem,
    classifierPrefix_length_le problem,
    composed_workRunExact problem,
    composed_run_compile_exact problem,
    composed_one_step_short_not_halted problem,
    composedFinal_tape_eq_mirrored_dispatch_entry problem⟩

/-- M222 gives the complete M220/M221 classifier's unique Finish path a
fixed blank-sentinel workspace orienter.  The resulting literal 740-rule
machine halts with a tape that is exactly the spatial mirror of M217's
canonical Finish-dispatch entry, under a uniform polynomial bound.  It does
not yet execute a mirrored dispatcher, derive body-token or padding requests,
iterate the physical schedule, establish builder `RawRefinement`, or package
the Cook--Levin reduction. -/
theorem cook_levin_builder_physical_classifier_finish_workspace_orientation_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    scheduleEntry problem (finishIndex problem) = some .finish /\
    composedMachine.rules.length = 740 /\
    composedMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) /\
    composedMachine.acceptState ≠ composedMachine.rejectState /\
    FinishWorkspaceOrientationHolds problem /\
    6 * composedWorkSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  exact ⟨BuilderPhysicalClassifierFinishRequest.finishIndex_scheduleEntry problem,
    composedRules_length, composedRules_pairwise_query_distinct,
    composedMachine_acceptState_ne_rejectState,
    finishWorkspaceOrientationHolds problem,
    composedCompiledSteps_le_rawTimeBound problem⟩

end BuilderPhysicalClassifierFinishWorkspaceOrientation

end PNP.Concrete.CookLevin
