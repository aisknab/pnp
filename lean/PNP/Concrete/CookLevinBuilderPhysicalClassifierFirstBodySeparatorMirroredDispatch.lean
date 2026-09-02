import PNP.Concrete.CookLevinBuilderPhysicalClassifierFinishMirroredDispatch

namespace PNP.Concrete.CookLevin

namespace BuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch

open PipelineStateNamespace
open BuilderPostDividerSelectedTokenLaunch

def firstBodyIndex {language : Language}
    (problem : VerifierTableauProblem language) :
    Fin (BuilderFullScheduleCursorController.bodySlotCount problem) :=
  ⟨0, by
    rw [BuilderFullScheduleCursorController.bodySlotCount_eq]
    omega⟩

theorem clauseCount_positive {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < BuilderPhysicalClassifierPipeline.clauseCount problem := by
  have hConstraints :
      0 < problem.formulaConstraintSlotCount := by
    unfold VerifierTableauProblem.formulaConstraintSlotCount
    rw [problem.formulaConstraintCountPolynomial_eval]
    omega
  have hPerConstraint :
      0 < problem.formulaClauseSlotsPerConstraint := by
    unfold VerifierTableauProblem.formulaClauseSlotsPerConstraint
    omega
  unfold BuilderPhysicalClassifierPipeline.clauseCount
    VerifierTableauProblem.formulaClauseSlotCount
  exact Nat.mul_pos hConstraints hPerConstraint

theorem firstBodyIndex_scheduleEntry {language : Language}
    (problem : VerifierTableauProblem language) :
    scheduleEntry problem (firstBodyIndex problem) = some .sep := by
  have hSelected := selectedEntry?_eq_some_getElem problem
    (firstBodyIndex problem)
  have hDirect := selectedEntry?_eq_formulaTokenSlotDirect problem
    (firstBodyIndex problem)
  have hSep := BuilderBodyStartPrefix.firstBodyTokenSlotDirect_eq_separator
    problem
  have hCoordinate :
      (scheduleCoordinate problem (firstBodyIndex problem)).val =
        problem.formulaVariableSlotBound + 1 := by
    simp [scheduleCoordinate, firstBodyIndex,
      BuilderFullScheduleCursorController.firstBodySlot_eq]
  rw [hCoordinate, hSep] at hDirect
  rw [hSelected] at hDirect
  exact Option.some.inj hDirect

theorem classifierFinal_state {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (BuilderPhysicalClassifierPipeline.finalConfiguration problem
      (firstBodyIndex problem) workspace).state =
      BuilderPhysicalClassifierPipeline.machine.acceptState := by
  have hState := BuilderPhysicalClassifierPipeline.finalConfiguration_state
    problem (firstBodyIndex problem) workspace
  have hAccept :=
    (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration_accept_iff
      0 (BuilderPhysicalClassifierPipeline.clauseCount problem)).2
      (clauseCount_positive problem)
  have hQuotient :
      (firstBodyIndex problem).val /
          BuilderPhysicalClassifierPipeline.width problem = 0 := by
    simp [firstBodyIndex]
  rw [hQuotient] at hState
  rw [hState]
  simpa [BuilderPhysicalClassifierPipeline.machine,
    WorkMachineChain.machine] using
    congrArg WorkMachineChain.secondState hAccept

abbrev unitSymbol : WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.unitSymbol

abbrev endSymbol : WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.endSymbol

private theorem blank_ne_raw_separator :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.separatorSymbol := by decide

private theorem blank_ne_raw_left_boundary :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.leftBoundary := by decide

private theorem blank_ne_unit :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.unitSymbol := by decide

private theorem blank_ne_separator :
    WorkSymbol.blank ≠
      BuilderPostDividerRawRouteClassifier.separatorSymbol := by decide

private theorem blank_ne_left_boundary :
    WorkSymbol.blank ≠
      BuilderPostDividerRawRouteClassifier.leftBoundary := by decide

private theorem blank_ne_copied_width :
    WorkSymbol.blank ≠ BuilderPostHeaderRawTapeBridge.copiedWidthMark := by decide

private theorem blank_ne_end :
    WorkSymbol.blank ≠ BuilderPostDividerRawRouteClassifier.endSymbol := by decide

private theorem blank_ne_boundary :
    WorkSymbol.blank ≠
      BuilderArbitrarySlotHeaderRouter.RawRouter.boundaryMark := by decide

private theorem blank_ne_coordinate :
    WorkSymbol.blank ≠
      BuilderPostDividerRawRouteClassifier.coordinateMark := by decide

def classifierFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPhysicalClassifierPipeline.finalConfiguration problem
    (firstBodyIndex problem) workspace

def classifierPrefix {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (classifierFinalConfiguration problem []).tape.left

theorem classifierFinal_left_append {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem workspace).tape.left =
      classifierPrefix problem ++ workspace := by
  have hCount := clauseCount_positive problem
  cases hCountEq : BuilderPhysicalClassifierPipeline.clauseCount problem with
  | zero => omega
  | succ remaining =>
      simp [classifierFinalConfiguration, classifierPrefix, firstBodyIndex,
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
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        hCountEq, renameConfiguration, List.append_assoc]

theorem classifierFinal_head {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem workspace).tape.head = unitSymbol := by
  have hCount := clauseCount_positive problem
  cases hCountEq : BuilderPhysicalClassifierPipeline.clauseCount problem with
  | zero => omega
  | succ remaining =>
      simp [classifierFinalConfiguration, firstBodyIndex,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        hCountEq, unitSymbol, renameConfiguration]

theorem classifierFinal_right {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem workspace).tape.right =
      List.replicate
          (BuilderPhysicalClassifierPipeline.clauseCount problem - 1)
          unitSymbol ++ [endSymbol] := by
  have hCount := clauseCount_positive problem
  cases hCountEq : BuilderPhysicalClassifierPipeline.clauseCount problem with
  | zero => omega
  | succ remaining =>
      simp [classifierFinalConfiguration, firstBodyIndex,
        BuilderPhysicalClassifierPipeline.finalConfiguration,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        hCountEq, unitSymbol, endSymbol, renameConfiguration]

theorem blank_not_mem_classifierPrefix {language : Language}
    (problem : VerifierTableauProblem language) :
    WorkSymbol.blank ∉ classifierPrefix problem := by
  have hCount := clauseCount_positive problem
  cases hCountEq : BuilderPhysicalClassifierPipeline.clauseCount problem with
  | zero => omega
  | succ remaining =>
      simp [classifierPrefix, classifierFinalConfiguration, firstBodyIndex,
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
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        hCountEq, renameConfiguration, blank_ne_raw_separator,
        blank_ne_raw_left_boundary, blank_ne_unit,
        blank_ne_left_boundary, blank_ne_copied_width, blank_ne_end,
        blank_ne_boundary, blank_ne_coordinate]

theorem classifierPrefix_length_le {language : Language}
    (problem : VerifierTableauProblem language) :
    (classifierPrefix problem).length ≤
      12 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1) := by
  have hCount := clauseCount_positive problem
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
  cases hCountEq : BuilderPhysicalClassifierPipeline.clauseCount problem with
  | zero => omega
  | succ remaining =>
      have hRemainingLe : remaining ≤
          BuilderFullScheduleCursorController.bodySlotCount problem := by
        omega
      simp [classifierPrefix, classifierFinalConfiguration, firstBodyIndex,
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
        BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
        BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
        BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
        hCountEq, renameConfiguration] at *
      omega

/-! ## Fixed first-body right-boundary request writer -/

abbrev requestSymbol : WorkSymbol :=
  BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .sep)

def writerStartState : Nat := 0
def writerAcceptState : Nat := 1
def writerRejectState : Nat := 2

def writerUnitRule : WorkRule :=
  { sourceState := writerStartState
    readSymbol := unitSymbol
    targetState := writerStartState
    writeSymbol := unitSymbol
    move := .right }

def writerEndRule : WorkRule :=
  { sourceState := writerStartState
    readSymbol := endSymbol
    targetState := writerAcceptState
    writeSymbol := requestSymbol
    move := .stay }

def writerRules : List WorkRule := [writerUnitRule, writerEndRule]

def writerMachine : WorkMachine :=
  { rules := writerRules
    startState := writerStartState
    acceptState := writerAcceptState
    rejectState := writerRejectState }

theorem writerRules_length : writerRules.length = 2 := by rfl

theorem writerRules_pairwise_query_distinct :
    writerRules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem writerMachine_acceptState_ne_rejectState :
    writerMachine.acceptState ≠ writerMachine.rejectState := by decide

private def rightPathTape (leftSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: right => { left := leftSide, head := head, right := right }

@[simp] private theorem rightPathTape_moveRight_cons
    (leftSide : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) :
    (rightPathTape leftSide (head :: right)).moveRight =
      rightPathTape (head :: leftSide) right := by
  cases right <;> rfl

private theorem writerRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? writerMachine start = some next) :
    workRunExact? writerMachine 1 start = some next := by
  change
    (match workStep? writerMachine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

theorem writerUnit_workStep (left right : List WorkSymbol) :
    workStep? writerMachine
        { state := writerStartState
          tape := { left := left, head := unitSymbol, right := right } } =
      some
        { state := writerStartState
          tape :=
            ({ left := left, head := unitSymbol, right := right } :
              WorkTape).moveRight } := by
  rfl

theorem writerEnd_workStep (left : List WorkSymbol) :
    workStep? writerMachine
        { state := writerStartState
          tape := { left := left, head := endSymbol, right := [] } } =
      some
        { state := writerAcceptState
          tape := { left := left, head := requestSymbol, right := [] } } := by
  rfl

private theorem writerScan_exact :
    ∀ (scanWord left : List WorkSymbol),
      (∀ symbol ∈ scanWord, symbol = unitSymbol) →
      workRunExact? writerMachine (scanWord.length + 1)
          { state := writerStartState
            tape := rightPathTape left (scanWord ++ [endSymbol]) } =
        some
          { state := writerAcceptState
            tape :=
              { left := scanWord.reverse ++ left
                head := requestSymbol
                right := [] } } := by
  intro scanWord
  induction scanWord with
  | nil =>
      intro left _hScan
      simpa using writerRunExact_one
        { state := writerStartState
          tape := rightPathTape left [endSymbol] }
        { state := writerAcceptState
          tape := { left := left, head := requestSymbol, right := [] } }
        (writerEnd_workStep left)
  | cons first rest ih =>
      intro left hScan
      have hFirst : first = unitSymbol :=
        hScan first (List.Mem.head rest)
      have hRest : ∀ symbol ∈ rest, symbol = unitSymbol := by
        intro symbol hSymbol
        exact hScan symbol (List.Mem.tail first hSymbol)
      subst first
      have hOne := writerRunExact_one
        { state := writerStartState
          tape := rightPathTape left
            (unitSymbol :: (rest ++ [endSymbol])) }
        { state := writerStartState
          tape := rightPathTape (unitSymbol :: left)
            (rest ++ [endSymbol]) } (by
          cases rest <;> rfl)
      have hTail := ih (unitSymbol :: left) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose writerMachine
        1 (rest.length + 1) _ _ _ hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_comm] using hAll

def writerEntryConfiguration (count : Nat)
    (left : List WorkSymbol) : WorkConfiguration :=
  { state := writerMachine.startState
    tape := rightPathTape left
      (List.replicate count unitSymbol ++ [endSymbol]) }

def writerFinalConfiguration (count : Nat)
    (left : List WorkSymbol) : WorkConfiguration :=
  { state := writerMachine.acceptState
    tape :=
      { left := (List.replicate count unitSymbol).reverse ++ left
        head := requestSymbol
        right := [] } }

def writerWorkSteps (count : Nat) : Nat := count + 1

theorem writer_workRunExact (count : Nat) (left : List WorkSymbol) :
    workRunExact? writerMachine (writerWorkSteps count)
        (writerEntryConfiguration count left) =
      some (writerFinalConfiguration count left) := by
  simpa [writerWorkSteps, writerEntryConfiguration,
    writerFinalConfiguration, writerMachine] using
    writerScan_exact (List.replicate count unitSymbol) left
      (by intro symbol hSymbol
          exact List.eq_of_mem_replicate hSymbol)

theorem classifierFinal_tape_eq_writerEntry {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (classifierFinalConfiguration problem workspace).tape =
      (writerEntryConfiguration
        (BuilderPhysicalClassifierPipeline.clauseCount problem)
        (classifierFinalConfiguration problem workspace).tape.left).tape := by
  have hCount := clauseCount_positive problem
  cases hCountEq : BuilderPhysicalClassifierPipeline.clauseCount problem with
  | zero => omega
  | succ remaining =>
      cases hTape : (classifierFinalConfiguration problem workspace).tape with
      | mk left head right =>
          have hHead := classifierFinal_head problem workspace
          have hRight := classifierFinal_right problem workspace
          rw [hTape] at hHead hRight
          change head = unitSymbol at hHead
          change right =
            List.replicate
                (BuilderPhysicalClassifierPipeline.clauseCount problem - 1)
                unitSymbol ++ [endSymbol] at hRight
          subst head
          rw [hRight]
          simp [writerEntryConfiguration, rightPathTape, hCountEq,
            List.replicate_succ]

/-! ## Full classifier followed by the first-body request writer -/

abbrev classifierMachine : WorkMachine :=
  BuilderPhysicalClassifierPipeline.machine

def classifierEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPhysicalClassifierPipeline.entryConfiguration problem
    (firstBodyIndex problem) workspace

theorem classifier_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    workRunExact? classifierMachine
        (BuilderPhysicalClassifierPipeline.workSteps problem
          (firstBodyIndex problem))
        (classifierEntryConfiguration problem workspace) =
      some (classifierFinalConfiguration problem workspace) := by
  exact BuilderPhysicalClassifierPipeline.workRunExact problem
    (firstBodyIndex problem) workspace

def bodyWriterFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  writerFinalConfiguration
    (BuilderPhysicalClassifierPipeline.clauseCount problem)
    (classifierFinalConfiguration problem workspace).tape.left

theorem bodyWriter_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    workRunExact? writerMachine
        (writerWorkSteps
          (BuilderPhysicalClassifierPipeline.clauseCount problem))
        { state := writerMachine.startState
          tape := (classifierFinalConfiguration problem workspace).tape } =
      some (bodyWriterFinalConfiguration problem workspace) := by
  rw [classifierFinal_tape_eq_writerEntry problem workspace]
  exact writer_workRunExact
    (BuilderPhysicalClassifierPipeline.clauseCount problem)
    (classifierFinalConfiguration problem workspace).tape.left

def classifierWriterMachine : WorkMachine :=
  WorkMachineChain.machine classifierMachine writerMachine

def classifierWriterEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (classifierEntryConfiguration problem workspace)

def classifierWriterFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (bodyWriterFinalConfiguration problem workspace)

def classifierWriterWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderPhysicalClassifierPipeline.workSteps problem
      (firstBodyIndex problem) + 1 +
    writerWorkSteps (BuilderPhysicalClassifierPipeline.clauseCount problem)

theorem classifierWriter_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    workRunExact? classifierWriterMachine
        (classifierWriterWorkSteps problem)
        (classifierWriterEntryConfiguration problem workspace) =
      some (classifierWriterFinalConfiguration problem workspace) := by
  have hFirst := classifier_workRunExact problem workspace
  have hFirstAccept := classifierFinal_state problem workspace
  have hSecond := bodyWriter_workRunExact problem workspace
  have hAll := WorkMachineChain.workRunExact classifierMachine writerMachine
    (BuilderPhysicalClassifierPipeline.workSteps problem
      (firstBodyIndex problem))
    (writerWorkSteps (BuilderPhysicalClassifierPipeline.clauseCount problem))
    (classifierEntryConfiguration problem workspace)
    (classifierFinalConfiguration problem workspace)
    (bodyWriterFinalConfiguration problem workspace)
    hFirst hFirstAccept hSecond
  simpa [classifierWriterMachine, classifierWriterWorkSteps,
    classifierWriterEntryConfiguration,
    classifierWriterFinalConfiguration] using hAll

set_option maxRecDepth 1000000 in
theorem classifierWriterRules_length :
    classifierWriterMachine.rules.length = 722 := by
  rfl

set_option maxRecDepth 1000000 in
private theorem classifier_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept classifierMachine := by
  intro rule hRule
  change rule ∈ BuilderPhysicalClassifierPipeline.machine.rules at hRule
  change rule.sourceState ≠
    BuilderPhysicalClassifierPipeline.machine.acceptState
  decide +revert

theorem classifierWriterRules_pairwise_query_distinct :
    classifierWriterMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    classifierMachine writerMachine
    BuilderPhysicalClassifierPipeline.rules_pairwise_query_distinct
    writerRules_pairwise_query_distinct classifier_noRuleAtAccept

theorem classifierWriterMachine_acceptState_ne_rejectState :
    classifierWriterMachine.acceptState ≠
      classifierWriterMachine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    classifierMachine writerMachine writerMachine_acceptState_ne_rejectState

theorem classifierWriter_run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    run (compileWorkMachine classifierWriterMachine)
        (6 * classifierWriterWorkSteps problem)
        (encodeWorkConfiguration
          (classifierWriterEntryConfiguration problem workspace)) =
      encodeWorkConfiguration
        (classifierWriterFinalConfiguration problem workspace) := by
  exact run_compileWorkMachine_mul_of_workRunExact classifierWriterMachine
    (classifierWriterWorkSteps problem)
    (classifierWriterEntryConfiguration problem workspace)
    (classifierWriterFinalConfiguration problem workspace)
    (classifierWriter_workRunExact problem workspace)

def writerPrefix {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (bodyWriterFinalConfiguration problem []).tape.left

theorem bodyWriterFinal_left_append {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (bodyWriterFinalConfiguration problem workspace).tape.left =
      writerPrefix problem ++ workspace := by
  simp [bodyWriterFinalConfiguration, writerFinalConfiguration,
    writerPrefix, classifierFinal_left_append, List.append_assoc]

theorem bodyWriterFinal_head {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (bodyWriterFinalConfiguration problem workspace).tape.head =
      requestSymbol := by
  rfl

theorem bodyWriterFinal_right_nil {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    (bodyWriterFinalConfiguration problem workspace).tape.right = [] := by
  rfl

theorem blank_not_mem_writerPrefix {language : Language}
    (problem : VerifierTableauProblem language) :
    WorkSymbol.blank ∉ writerPrefix problem := by
  have hClassifier :
      WorkSymbol.blank ∉
        (classifierFinalConfiguration problem []).tape.left := by
    simpa [classifierPrefix] using blank_not_mem_classifierPrefix problem
  simp [writerPrefix, bodyWriterFinalConfiguration,
    writerFinalConfiguration, blank_ne_unit, hClassifier]

theorem writerPrefix_length_le {language : Language}
    (problem : VerifierTableauProblem language) :
    (writerPrefix problem).length ≤
      13 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1) := by
  have hClassifier := classifierPrefix_length_le problem
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
  simp [writerPrefix, bodyWriterFinalConfiguration,
    writerFinalConfiguration, classifierPrefix] at *
  omega

/-! ## Fixed separator-request workspace orienter -/

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

theorem orientRules_length : orientRules.length = 10 := by rfl

theorem orientRules_pairwise_query_distinct :
    orientRules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem orientMachine_acceptState_ne_rejectState :
    orientMachine.acceptState ≠ orientMachine.rejectState := by decide

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

private theorem orientRunExact_one (start next : WorkConfiguration)
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
      simpa using orientRunExact_one
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
      have hOne := orientRunExact_one
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
  have hStart := orientRunExact_one
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

/-! ## Canonical classifier/writer/orienter composition -/

def output {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  emittedPrefix problem (firstBodyIndex problem).val

def builderWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  let workspace := BuilderTokenAppender.workspaceTape problem.input []
    (output problem)
  workspace.head :: workspace.right

def classifierWorkspace {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  WorkSymbol.blank :: builderWord problem

def canonicalClassifierWriterEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  classifierWriterEntryConfiguration problem (classifierWorkspace problem)

def canonicalClassifierWriterFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  classifierWriterFinalConfiguration problem (classifierWorkspace problem)

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

theorem classifierWriterFinal_tape_eq_orientEntry {language : Language}
    (problem : VerifierTableauProblem language) :
    (canonicalClassifierWriterFinalConfiguration problem).tape =
      (orientEntryConfiguration (writerPrefix problem)
        (builderWord problem)).tape := by
  apply workTape_ext
  · simpa [canonicalClassifierWriterFinalConfiguration,
      classifierWriterFinalConfiguration, orientEntryConfiguration,
      classifierWorkspace, renameConfiguration] using
      bodyWriterFinal_left_append problem (classifierWorkspace problem)
  · exact bodyWriterFinal_head problem (classifierWorkspace problem)
  · exact bodyWriterFinal_right_nil problem (classifierWorkspace problem)

theorem canonicalClassifierWriterFinal_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (canonicalClassifierWriterFinalConfiguration problem).state =
      classifierWriterMachine.acceptState := by
  rfl

def orientedMachine : WorkMachine :=
  WorkMachineChain.machine classifierWriterMachine orientMachine

def orientedEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (canonicalClassifierWriterEntryConfiguration problem)

def orientedFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (orientFinalConfiguration (writerPrefix problem) (builderWord problem))

def orientedWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  classifierWriterWorkSteps problem + 1 +
    orientWorkSteps (writerPrefix problem)

theorem oriented_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? orientedMachine (orientedWorkSteps problem)
        (orientedEntryConfiguration problem) =
      some (orientedFinalConfiguration problem) := by
  have hFirst := classifierWriter_workRunExact problem
    (classifierWorkspace problem)
  have hSecond : workRunExact? orientMachine
      (orientWorkSteps (writerPrefix problem))
      { state := orientMachine.startState
        tape := (canonicalClassifierWriterFinalConfiguration problem).tape } =
      some (orientFinalConfiguration (writerPrefix problem)
        (builderWord problem)) := by
    rw [classifierWriterFinal_tape_eq_orientEntry problem]
    exact orient_workRunExact (writerPrefix problem) (builderWord problem)
      (fun symbol hSymbol hBlank =>
        blank_not_mem_writerPrefix problem (hBlank ▸ hSymbol))
  have hAll := WorkMachineChain.workRunExact classifierWriterMachine
    orientMachine (classifierWriterWorkSteps problem)
    (orientWorkSteps (writerPrefix problem))
    (canonicalClassifierWriterEntryConfiguration problem)
    (canonicalClassifierWriterFinalConfiguration problem)
    (orientFinalConfiguration (writerPrefix problem) (builderWord problem))
    (by simpa [canonicalClassifierWriterEntryConfiguration,
      canonicalClassifierWriterFinalConfiguration] using hFirst)
    (canonicalClassifierWriterFinal_state problem) hSecond
  simpa [orientedMachine, orientedWorkSteps,
    orientedEntryConfiguration, orientedFinalConfiguration] using hAll

set_option maxRecDepth 1000000 in
theorem orientedRules_length : orientedMachine.rules.length = 741 := by rfl

private theorem writer_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept writerMachine := by
  intro rule hRule
  change rule ∈ writerRules at hRule
  change rule.sourceState ≠ writerAcceptState
  decide +revert

private theorem classifierWriter_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept classifierWriterMachine := by
  exact WorkMachineChain.noRuleAtAccept classifierMachine writerMachine
    writer_noRuleAtAccept

theorem orientedRules_pairwise_query_distinct :
    orientedMachine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    classifierWriterMachine orientMachine
    classifierWriterRules_pairwise_query_distinct
    orientRules_pairwise_query_distinct classifierWriter_noRuleAtAccept

theorem orientedMachine_acceptState_ne_rejectState :
    orientedMachine.acceptState ≠ orientedMachine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    classifierWriterMachine orientMachine
    orientMachine_acceptState_ne_rejectState

theorem oriented_run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine orientedMachine) (6 * orientedWorkSteps problem)
        (encodeWorkConfiguration (orientedEntryConfiguration problem)) =
      encodeWorkConfiguration (orientedFinalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact orientedMachine
    (orientedWorkSteps problem) (orientedEntryConfiguration problem)
    (orientedFinalConfiguration problem) (oriented_workRunExact problem)

/-! ## Reflected first-body separator dispatch -/

abbrev sourceDispatchMachine : WorkMachine :=
  BuilderPhysicalOptionalTokenDispatch.machine

def dispatchMachine : WorkMachine :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorMachine
    sourceDispatchMachine

def dispatchOutsideLeft {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (writerPrefix problem).reverse ++ [requestSymbol]

def dispatchEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
    (BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
      (dispatchOutsideLeft problem) (output problem) (some .sep))

def dispatchFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
    (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
      (BuilderTokenAppender.finalConfiguration problem.input
        (dispatchOutsideLeft problem)
        (emittedPrefix problem ((firstBodyIndex problem).val + 1))))

def dispatchWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem
    (firstBodyIndex problem)

theorem dispatch_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? dispatchMachine (dispatchWorkSteps problem)
        (dispatchEntryConfiguration problem) =
      some (dispatchFinalConfiguration problem) := by
  have hRun := BuilderPhysicalOptionalTokenDispatch.canonical_workRunExact
    problem (firstBodyIndex problem) (dispatchOutsideLeft problem)
  have hRequest := firstBodyIndex_scheduleEntry problem
  simp only [BuilderPhysicalOptionalTokenDispatch.canonicalRequest,
    hRequest] at hRun
  exact
    BuilderPhysicalClassifierFinishMirroredDispatch.workRunExact?_mirror_of_some
      sourceDispatchMachine (dispatchWorkSteps problem)
      (BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
        (dispatchOutsideLeft problem) (output problem) (some .sep))
      (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
        (BuilderTokenAppender.finalConfiguration problem.input
          (dispatchOutsideLeft problem)
          (emittedPrefix problem ((firstBodyIndex problem).val + 1)))) (by
        simpa [dispatchWorkSteps, output,
          BuilderPhysicalOptionalTokenDispatch.canonicalRequest] using hRun)

theorem dispatch_run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine dispatchMachine) (6 * dispatchWorkSteps problem)
        (encodeWorkConfiguration (dispatchEntryConfiguration problem)) =
      encodeWorkConfiguration (dispatchFinalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact dispatchMachine
    (dispatchWorkSteps problem) (dispatchEntryConfiguration problem)
    (dispatchFinalConfiguration problem) (dispatch_workRunExact problem)

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

theorem orientedFinal_tape_eq_dispatchEntry {language : Language}
    (problem : VerifierTableauProblem language) :
    (orientedFinalConfiguration problem).tape =
      (dispatchEntryConfiguration problem).tape := by
  rfl

/-! ## Full first-body classifier/writer/orienter/dispatcher composition -/

def machine : WorkMachine :=
  WorkMachineChain.machine orientedMachine dispatchMachine

def entryConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (orientedEntryConfiguration problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (dispatchFinalConfiguration problem)

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  orientedWorkSteps problem + 1 + dispatchWorkSteps problem

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? machine (workSteps problem) (entryConfiguration problem) =
      some (finalConfiguration problem) := by
  have hFirst := oriented_workRunExact problem
  have hEntry :
      ({ state := dispatchMachine.startState
         tape := (orientedFinalConfiguration problem).tape } :
        WorkConfiguration) = dispatchEntryConfiguration problem := by
    apply workConfiguration_ext
    · rfl
    · exact orientedFinal_tape_eq_dispatchEntry problem
  have hSecond : workRunExact? dispatchMachine
      (dispatchWorkSteps problem)
      { state := dispatchMachine.startState
        tape := (orientedFinalConfiguration problem).tape } =
      some (dispatchFinalConfiguration problem) := by
    rw [hEntry]
    exact dispatch_workRunExact problem
  have hAll := WorkMachineChain.workRunExact orientedMachine dispatchMachine
    (orientedWorkSteps problem) (dispatchWorkSteps problem)
    (orientedEntryConfiguration problem) (orientedFinalConfiguration problem)
    (dispatchFinalConfiguration problem) hFirst rfl hSecond
  simpa [machine, workSteps, entryConfiguration, finalConfiguration] using hAll

set_option maxRecDepth 1000000 in
theorem rules_length : machine.rules.length = 814 := by rfl

private theorem orient_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept orientMachine := by
  intro rule hRule
  change rule ∈ orientRules at hRule
  change rule.sourceState ≠ orientAcceptState
  decide +revert

private theorem oriented_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept orientedMachine := by
  exact WorkMachineChain.noRuleAtAccept classifierWriterMachine orientMachine
    orient_noRuleAtAccept

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineChain.rules_pairwise_query_distinct
    orientedMachine dispatchMachine orientedRules_pairwise_query_distinct
    dispatchRules_pairwise_query_distinct oriented_noRuleAtAccept

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  exact WorkMachineChain.machine_acceptState_ne_rejectState
    orientedMachine dispatchMachine dispatchMachine_acceptState_ne_rejectState

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine machine) (6 * workSteps problem)
        (encodeWorkConfiguration (entryConfiguration problem)) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps problem) (entryConfiguration problem)
    (finalConfiguration problem) (workRunExact problem)

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
               | some result =>
                  workRunExact? selectedMachine (steps + 1) result) =
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

theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < workSteps problem := by
  unfold workSteps
  omega

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language) :
    machine.isHalted
      (workRun machine (workSteps problem - 1) (entryConfiguration problem)) =
        false := by
  let short := workSteps problem - 1
  have hSucc : short + 1 = workSteps problem := by
    have hPositive := workSteps_positive problem
    dsimp [short]
    omega
  have hExact := workRunExact problem
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last machine short
      (entryConfiguration problem) (finalConfiguration problem) hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short (entryConfiguration problem) = before :=
    workRun_eq_of_workRunExact machine short (entryConfiguration problem)
      before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine before
    (finalConfiguration problem) hLast

theorem firstBody_nextPrefix {language : Language}
    (problem : VerifierTableauProblem language) :
    emittedPrefix problem ((firstBodyIndex problem).val + 1) =
      output problem ++ [.sep] := by
  have hPrefix := emittedPrefix_succ problem (firstBodyIndex problem)
  rw [firstBodyIndex_scheduleEntry problem] at hPrefix
  simpa [output] using hPrefix

theorem final_output_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    (finalConfiguration problem).tape =
      (BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
        (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
          (BuilderTokenAppender.finalConfiguration problem.input
            (dispatchOutsideLeft problem)
            (output problem ++ [.sep])))).tape := by
  rw [← firstBody_nextPrefix problem]
  rfl

/-! ## Uniform source-input-size polynomial bound -/

def sizePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  BuilderPhysicalClassifierFinishWorkspaceOrientation.orientationSizePolynomial
    verifier

theorem sizePolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (sizePolynomial problem.verifier).eval problem.input.length =
      BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        BuilderPhysicalClassifierPipeline.width problem + 1 := by
  have h :=
    BuilderPhysicalClassifierFinishWorkspaceOrientation.orientationRawTimeBound_eval
      problem
  unfold BuilderPhysicalClassifierFinishWorkspaceOrientation.orientationRawTimeBound at h
  simp only [NatPolynomial.eval_mul, NatPolynomial.eval_constant] at h
  unfold sizePolynomial
  omega

def middleRawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (.constant 168) (sizePolynomial verifier)

theorem middleRawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (middleRawTimeBound problem.verifier).eval problem.input.length =
      168 *
        (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
          BuilderFullScheduleCursorController.bodySlotCount problem +
          BuilderPhysicalClassifierPipeline.width problem + 1) := by
  unfold middleRawTimeBound
  simp only [NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  rw [sizePolynomial_eval]

theorem middleCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    6 *
        (writerWorkSteps
            (BuilderPhysicalClassifierPipeline.clauseCount problem) +
          orientWorkSteps (writerPrefix problem) + 3) ≤
      (middleRawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := writerPrefix_length_le problem
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
  rw [middleRawTimeBound_eval]
  unfold writerWorkSteps orientWorkSteps
  omega

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPhysicalClassifierPipeline.rawTimeBound verifier)
    (.add (middleRawTimeBound verifier)
      (BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier))

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPhysicalClassifierPipeline.rawTimeBound
          problem.verifier).eval problem.input.length +
        ((middleRawTimeBound problem.verifier).eval problem.input.length +
          (BuilderPhysicalOptionalTokenDispatch.rawTimeBound
            problem.verifier).eval problem.input.length) := by
  rfl

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier :=
    BuilderPhysicalClassifierPipeline.compiledSteps_le_rawTimeBound problem
      (firstBodyIndex problem)
  have hMiddle := middleCompiledSteps_le_rawTimeBound problem
  have hDispatch :=
    BuilderPhysicalOptionalTokenDispatch.canonicalCompiledSteps_le_rawTimeBound
      problem (firstBodyIndex problem)
  rw [rawTimeBound_eval]
  unfold workSteps orientedWorkSteps classifierWriterWorkSteps
    dispatchWorkSteps
  omega

def FirstBodySeparatorMirroredDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language) : Prop :=
  scheduleEntry problem (firstBodyIndex problem) = some .sep ∧
    (classifierFinalConfiguration problem (classifierWorkspace problem)).state =
      classifierMachine.acceptState ∧
    workRunExact? writerMachine
        (writerWorkSteps
          (BuilderPhysicalClassifierPipeline.clauseCount problem))
        { state := writerMachine.startState
          tape :=
            (classifierFinalConfiguration problem
              (classifierWorkspace problem)).tape } =
      some
        (bodyWriterFinalConfiguration problem (classifierWorkspace problem)) ∧
    workRunExact? orientMachine (orientWorkSteps (writerPrefix problem))
        (orientEntryConfiguration (writerPrefix problem)
          (builderWord problem)) =
      some
        (orientFinalConfiguration (writerPrefix problem)
          (builderWord problem)) ∧
    workRunExact? dispatchMachine (dispatchWorkSteps problem)
        (dispatchEntryConfiguration problem) =
      some (dispatchFinalConfiguration problem) ∧
    workRunExact? machine (workSteps problem) (entryConfiguration problem) =
      some (finalConfiguration problem) ∧
    run (compileWorkMachine machine) (6 * workSteps problem)
        (encodeWorkConfiguration (entryConfiguration problem)) =
      encodeWorkConfiguration (finalConfiguration problem) ∧
    machine.isHalted
      (workRun machine (workSteps problem - 1) (entryConfiguration problem)) =
        false ∧
    (finalConfiguration problem).tape =
      (BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
        (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
          (BuilderTokenAppender.finalConfiguration problem.input
            (dispatchOutsideLeft problem)
            (output problem ++ [.sep])))).tape ∧
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length

theorem firstBodySeparatorMirroredDispatchHolds {language : Language}
    (problem : VerifierTableauProblem language) :
    FirstBodySeparatorMirroredDispatchHolds problem := by
  exact ⟨firstBodyIndex_scheduleEntry problem,
    classifierFinal_state problem (classifierWorkspace problem),
    bodyWriter_workRunExact problem (classifierWorkspace problem),
    orient_workRunExact (writerPrefix problem) (builderWord problem)
      (fun symbol hSymbol hBlank =>
        blank_not_mem_writerPrefix problem (hBlank ▸ hSymbol)),
    dispatch_workRunExact problem, workRunExact problem,
    run_compile_exact problem, one_step_short_not_halted problem,
    final_output_exact problem, compiledSteps_le_rawTimeBound problem⟩

/-- M224 derives the first post-header coordinate and its separator request,
runs M220's complete classifier through the body terminal, crosses the exact
positive clause-count suffix with a fixed two-rule scanner, writes the physical
separator request, reorients the canonical builder workspace, and executes
M223's reflected M217 dispatcher. One collision-free 814-rule machine reaches
the exact next canonical emitted prefix with exact work, compiled,
one-step-short and source-size polynomial evidence. This closes only the first
populated body coordinate; arbitrary body-token and padding request selection,
all-route connection, one repeated physical loop, builder `RawRefinement` and
the packaged Cook--Levin reduction remain open. -/
theorem cook_levin_builder_physical_classifier_first_body_separator_mirrored_dispatch_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    (firstBodyIndex problem).val = 0 ∧
    0 < BuilderPhysicalClassifierPipeline.clauseCount problem ∧
    writerMachine.rules.length = 2 ∧
    orientMachine.rules.length = 10 ∧
    dispatchMachine.rules.length = 64 ∧
    machine.rules.length = 814 ∧
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) ∧
    machine.acceptState ≠ machine.rejectState ∧
    FirstBodySeparatorMirroredDispatchHolds problem := by
  exact ⟨rfl, clauseCount_positive problem, writerRules_length,
    orientRules_length, dispatchRules_length, rules_length,
    rules_pairwise_query_distinct, machine_acceptState_ne_rejectState,
    firstBodySeparatorMirroredDispatchHolds problem⟩

end BuilderPhysicalClassifierFirstBodySeparatorMirroredDispatch
end PNP.Concrete.CookLevin
