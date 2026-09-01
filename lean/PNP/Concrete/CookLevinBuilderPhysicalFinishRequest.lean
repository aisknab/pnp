/-
Copyright (c) 2026 PNP Labs.

A literal handoff from the unique equal terminal of M214's physical
post-divider classifier to M217's tape-resident `Finish` request.

The canonical builder workspace is protected as a suffix beyond the
comparator's end marker.  One fixed writer changes that marker into the
physical `Finish` symbol, and one fixed composed machine then runs M217's
dispatcher to append the final token.  The body-token and padding request
selector, the preceding suffix-preserving classifier handoff, one repeated
physical schedule loop, builder `RawRefinement`, and the packaged Cook--Levin
reduction remain open.
-/

import PNP.Concrete.CookLevinBuilderPhysicalDispatchSchedule
import PNP.Concrete.WorkMachineChain

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPhysicalFinishRequest

open PipelineTape PipelineStateNamespace
open BuilderPostDividerSelectedTokenLaunch


abbrev comparatorMachine : WorkMachine := BuilderPostDividerRawRouteClassifier.comparatorMachine
abbrev dispatchMachine : WorkMachine := BuilderPhysicalOptionalTokenDispatch.machine
abbrev endSymbol : WorkSymbol := BuilderPostDividerRawRouteClassifier.endSymbol

/-! ## A right-protected comparator suffix -/

/-- Append cells beyond the comparator's protected right end marker. -/
def appendRightExteriorTape (tape : WorkTape)
    (exterior : List WorkSymbol) : WorkTape :=
  { left := tape.left
    head := tape.head
    right := tape.right ++ exterior }

def appendRightExteriorConfiguration (configuration : WorkConfiguration)
    (exterior : List WorkSymbol) : WorkConfiguration :=
  { state := configuration.state
    tape := appendRightExteriorTape configuration.tape exterior }

private def ComparatorRightBoundaryProtected (tape : WorkTape) : Prop :=
  (∃ rightPrefix, tape.right = rightPrefix ++ [endSymbol]) ∨
    (tape.right = [] ∧ tape.head = endSymbol)

private def comparatorRightBoundaryRuleSafe (rule : WorkRule) : Bool :=
  if rule.readSymbol == endSymbol then
    (rule.writeSymbol == endSymbol) && !(rule.move == .right)
  else
    true

private theorem comparator_rules_right_boundary_safe :
    comparatorMachine.rules.all comparatorRightBoundaryRuleSafe = true := by
  decide

private theorem findWorkRule_some_mem {rules : List WorkRule}
    {state : Nat} {symbol : WorkSymbol} {selected : WorkRule}
    (hFind : findWorkRule rules state symbol = some selected) :
    selected ∈ rules := by
  induction rules with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hMatches :
          first.sourceState = state ∧ first.readSymbol = symbol
      · have hHead := findWorkRule_cons_of_matches first rest state symbol
          hMatches
        have hEqual : first = selected :=
          Option.some.inj (hHead.symm.trans hFind)
        subst selected
        exact List.Mem.head rest
      · have hTail := findWorkRule_cons_of_not_matches first rest state symbol
          hMatches
        exact List.Mem.tail first (ih (hTail.symm.trans hFind))

private theorem comparator_rule_safe_at_right_boundary (rule : WorkRule)
    (hRule : rule ∈ comparatorMachine.rules)
    (hRead : rule.readSymbol = endSymbol) :
    rule.writeSymbol = endSymbol ∧ rule.move ≠ .right := by
  have hSafe :=
    (List.all_eq_true.mp comparator_rules_right_boundary_safe) rule hRule
  simp [comparatorRightBoundaryRuleSafe, hRead] at hSafe
  refine And.intro hSafe.1 ?_
  cases hMove : rule.move with
  | left =>
      intro hImpossible
      cases hImpossible
  | stay =>
      intro hImpossible
      cases hImpossible
  | right =>
      intro _
      rw [hMove] at hSafe
      have hFalse : (true : Bool) = false := hSafe.2
      exact Bool.noConfusion hFalse

private theorem comparatorRightBoundaryProtected_head_of_right_nil
    (tape : WorkTape) (hProtected : ComparatorRightBoundaryProtected tape)
    (hRight : tape.right = []) : tape.head = endSymbol := by
  rcases hProtected with ⟨rightPrefix, hPrefix⟩ | hAtBoundary
  ·
    have hImpossible : ([] : List WorkSymbol) =
        rightPrefix ++ [endSymbol] := hRight.symm.trans hPrefix
    cases rightPrefix with
    | nil => cases hImpossible
    | cons _ _ => cases hImpossible
  · exact hAtBoundary.2

private theorem appendRightExteriorTape_write (tape : WorkTape)
    (symbol : WorkSymbol) (exterior : List WorkSymbol) :
    appendRightExteriorTape (tape.write symbol) exterior =
      (appendRightExteriorTape tape exterior).write symbol := by
  rfl

private theorem appendRightExteriorTape_moveLeft (tape : WorkTape)
    (exterior : List WorkSymbol) :
    appendRightExteriorTape tape.moveLeft exterior =
      (appendRightExteriorTape tape exterior).moveLeft := by
  rcases tape with ⟨left, head, right⟩
  cases left <;> rfl

private theorem appendRightExteriorTape_moveRight (tape : WorkTape)
    (exterior : List WorkSymbol) (hRight : tape.right ≠ []) :
    appendRightExteriorTape tape.moveRight exterior =
      (appendRightExteriorTape tape exterior).moveRight := by
  cases hTape : tape.right with
  | nil => contradiction
  | cons symbol rest =>
      simp [appendRightExteriorTape, WorkTape.moveRight, hTape]

private theorem comparatorRightBoundaryProtected_apply
    (configuration : WorkConfiguration) (rule : WorkRule)
    (hProtected : ComparatorRightBoundaryProtected configuration.tape)
    (hBoundary : configuration.tape.head = endSymbol →
      rule.writeSymbol = endSymbol ∧ rule.move ≠ .right) :
    ComparatorRightBoundaryProtected (applyWorkRule rule configuration).tape := by
  rcases hProtected with ⟨rightPrefix, hPrefix⟩ | hAtBoundary
  ·
    cases hMove : rule.move with
    | stay =>
        exact Or.inl ⟨rightPrefix, by
          simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove, hPrefix]⟩
    | left =>
        exact Or.inl ⟨rule.writeSymbol :: rightPrefix, by
          cases hLeft : configuration.tape.left <;>
            simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
              WorkTape.moveLeft, hPrefix, hLeft]⟩
    | right =>
        cases rightPrefix with
        | nil =>
            exact Or.inr (by
              simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
                WorkTape.moveRight, hPrefix])
        | cons symbol rest =>
            exact Or.inl ⟨rest, by
              simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
                WorkTape.moveRight, hPrefix]⟩
  · have hSafe := hBoundary hAtBoundary.2
    cases hMove : rule.move with
    | right => exact False.elim (hSafe.2 hMove)
    | stay =>
        exact Or.inr (by
          simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
            hAtBoundary, hSafe.1])
    | left =>
        exact Or.inl ⟨[], by
          cases hLeft : configuration.tape.left <;>
            simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
              WorkTape.moveLeft, hAtBoundary, hSafe.1, hLeft]⟩

private theorem comparator_step_transport
    (configuration next : WorkConfiguration)
    (exterior : List WorkSymbol)
    (hProtected : ComparatorRightBoundaryProtected configuration.tape)
    (hStep : workStep? comparatorMachine configuration = some next) :
    ComparatorRightBoundaryProtected next.tape ∧
      workStep? comparatorMachine
          (appendRightExteriorConfiguration configuration exterior) =
        some (appendRightExteriorConfiguration next exterior) := by
  rcases workStep?_some_exists comparatorMachine configuration next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hRule := findWorkRule_some_mem hFind
  have hMatches := findWorkRule_some_matches hFind
  have hBoundary : configuration.tape.head = endSymbol →
      rule.writeSymbol = endSymbol ∧ rule.move ≠ .right := by
    intro hHead
    exact comparator_rule_safe_at_right_boundary rule hRule
      (hMatches.2.trans hHead)
  have hNextProtected : ComparatorRightBoundaryProtected next.tape := by
    rw [hNext]
    exact comparatorRightBoundaryProtected_apply configuration rule hProtected
      hBoundary
  have hRightNonempty : rule.move = .right →
      configuration.tape.right ≠ [] := by
    intro hMove hRight
    have hHead := comparatorRightBoundaryProtected_head_of_right_nil
      configuration.tape hProtected hRight
    exact (hBoundary hHead).2 hMove
  have hTapeCommute :
      appendRightExteriorTape
          ((configuration.tape.write rule.writeSymbol).move rule.move)
          exterior =
        ((appendRightExteriorTape configuration.tape exterior).write
          rule.writeSymbol).move rule.move := by
    cases hMove : rule.move with
    | stay => rfl
    | left =>
        simpa [WorkTape.move, hMove, appendRightExteriorTape_write] using
          appendRightExteriorTape_moveLeft
            (configuration.tape.write rule.writeSymbol) exterior
    | right =>
        have hNonempty :
            (configuration.tape.write rule.writeSymbol).right ≠ [] := by
          simpa [WorkTape.write] using hRightNonempty hMove
        simpa [WorkTape.move, hMove, appendRightExteriorTape_write] using
          appendRightExteriorTape_moveRight
            (configuration.tape.write rule.writeSymbol) exterior hNonempty
  have hHaltedExterior :
      comparatorMachine.isHalted
          (appendRightExteriorConfiguration configuration exterior) = false := by
    simpa [WorkMachine.isHalted, appendRightExteriorConfiguration,
      appendRightExteriorTape] using hHalted
  have hFindExterior :
      findWorkRule comparatorMachine.rules
          (appendRightExteriorConfiguration configuration exterior).state
          (appendRightExteriorConfiguration configuration exterior).tape.head =
        some rule := by
    simpa [appendRightExteriorConfiguration,
      appendRightExteriorTape] using hFind
  have hExteriorStep := workStep?_eq_apply_of_find comparatorMachine
    (appendRightExteriorConfiguration configuration exterior) rule
    hHaltedExterior hFindExterior
  refine And.intro hNextProtected ?_
  rw [hExteriorStep]
  apply congrArg Option.some
  rw [hNext]
  cases configuration
  simp only [appendRightExteriorConfiguration, applyWorkRule]
  exact congrArg (fun tape => WorkConfiguration.mk rule.targetState tape)
    hTapeCommute.symm

private theorem comparator_workRunExact_transport :
    forall (steps : Nat) (initial final : WorkConfiguration)
      (exterior : List WorkSymbol),
      ComparatorRightBoundaryProtected initial.tape →
      workRunExact? comparatorMachine steps initial = some final →
      workRunExact? comparatorMachine steps
          (appendRightExteriorConfiguration initial exterior) =
        some (appendRightExteriorConfiguration final exterior) := by
  intro steps
  induction steps with
  | zero =>
      intro initial final exterior _hProtected hRun
      have hEqual : initial = final := Option.some.inj hRun
      subst final
      rfl
  | succ steps ih =>
      intro initial final exterior hProtected hRun
      cases hStep : workStep? comparatorMachine initial with
      | none =>
          change
            (match workStep? comparatorMachine initial with
             | none => none
             | some next => workRunExact? comparatorMachine steps next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? comparatorMachine steps next =
              some final := by
            change
              (match workStep? comparatorMachine initial with
               | none => none
               | some result => workRunExact? comparatorMachine steps result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          have hTransport := comparator_step_transport initial next exterior
            hProtected hStep
          change
            (match workStep? comparatorMachine
                (appendRightExteriorConfiguration initial exterior) with
             | none => none
             | some result => workRunExact? comparatorMachine steps result) =
              some (appendRightExteriorConfiguration final exterior)
          rw [hTransport.2]
          exact ih next final exterior hTransport.1 hTail

private theorem shieldedComparatorStart_right_boundary_protected
    (coordinate boundary : Nat) (leftExterior : List WorkSymbol) :
    ComparatorRightBoundaryProtected
      (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration coordinate boundary
        leftExterior).tape := by
  cases coordinate with
  | zero =>
      refine Or.inl ⟨
        List.replicate boundary
          BuilderArbitrarySlotHeaderRouter.RawRouter.unitSymbol, ?_⟩
      rfl
  | succ coordinate =>
      refine Or.inl ⟨
        List.replicate coordinate
            BuilderArbitrarySlotHeaderRouter.RawRouter.unitSymbol ++
          BuilderArbitrarySlotHeaderRouter.RawRouter.separatorSymbol ::
            List.replicate boundary
              BuilderArbitrarySlotHeaderRouter.RawRouter.unitSymbol, ?_⟩
      change
        List.replicate coordinate
              BuilderArbitrarySlotHeaderRouter.RawRouter.unitSymbol ++
            BuilderArbitrarySlotHeaderRouter.RawRouter.separatorSymbol ::
              (List.replicate boundary
                BuilderArbitrarySlotHeaderRouter.RawRouter.unitSymbol ++
                  [endSymbol]) =
          (List.replicate coordinate
                BuilderArbitrarySlotHeaderRouter.RawRouter.unitSymbol ++
              BuilderArbitrarySlotHeaderRouter.RawRouter.separatorSymbol ::
                List.replicate boundary
                  BuilderArbitrarySlotHeaderRouter.RawRouter.unitSymbol) ++
            [endSymbol]
      simp [List.append_assoc]

theorem shielded_comparator_workRunExact_with_right_exterior
    (coordinate boundary : Nat) (leftExterior rightExterior : List WorkSymbol) :
    workRunExact? comparatorMachine
        (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate boundary)
        (appendRightExteriorConfiguration
          (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
            coordinate boundary leftExterior) rightExterior) =
      some
        (appendRightExteriorConfiguration
          (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration
            coordinate boundary leftExterior) rightExterior) := by
  exact comparator_workRunExact_transport
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate boundary)
    (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
      coordinate boundary leftExterior)
    (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration
      coordinate boundary leftExterior)
    rightExterior
    (shieldedComparatorStart_right_boundary_protected coordinate boundary
      leftExterior)
    (BuilderPostDividerRawRouteClassifier.shielded_comparator_workRunExact coordinate boundary
      leftExterior)

/-! ## Verdict swap and the literal Finish writer -/

/-- The canonical equal comparator terminal becomes the accepting endpoint.
The rule table and halted-state set are unchanged. -/
def finishClassifierMachine : WorkMachine :=
  { comparatorMachine with
    acceptState := comparatorMachine.rejectState
    rejectState := comparatorMachine.acceptState }

theorem finishClassifierMachine_isHalted (configuration : WorkConfiguration) :
    finishClassifierMachine.isHalted configuration =
      comparatorMachine.isHalted configuration := by
  simp [finishClassifierMachine, WorkMachine.isHalted, Bool.or_comm]

theorem finishClassifierMachine_workStep (configuration : WorkConfiguration) :
    workStep? finishClassifierMachine configuration =
      workStep? comparatorMachine configuration := by
  unfold workStep?
  rw [finishClassifierMachine_isHalted]
  rfl

theorem finishClassifierMachine_workRunExact (steps : Nat)
    (configuration : WorkConfiguration) :
    workRunExact? finishClassifierMachine steps configuration =
      workRunExact? comparatorMachine steps configuration := by
  induction steps generalizing configuration with
  | zero => rfl
  | succ steps ih =>
      simp only [workRunExact?]
      rw [finishClassifierMachine_workStep]
      cases hStep : workStep? comparatorMachine configuration with
      | none => rfl
      | some next => exact ih next

def writerStartState : Nat := 0
def writerAcceptState : Nat := 1
def writerRejectState : Nat := 2

def writerRule : WorkRule :=
  { sourceState := writerStartState
    readSymbol := endSymbol
    targetState := writerAcceptState
    writeSymbol := BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)
    move := .stay }

def writerMachine : WorkMachine :=
  { rules := [writerRule]
    startState := writerStartState
    acceptState := writerAcceptState
    rejectState := writerRejectState }

def writerInputConfiguration (tape : WorkTape) : WorkConfiguration :=
  { state := writerMachine.startState, tape := tape }

def writerFinalConfiguration (tape : WorkTape) : WorkConfiguration :=
  { state := writerMachine.acceptState
    tape := tape.write (BuilderPhysicalOptionalTokenDispatch.requestSymbol (some .finish)) }

theorem writer_workRunExact (tape : WorkTape)
    (hHead : tape.head = endSymbol) :
    workRunExact? writerMachine 1 (writerInputConfiguration tape) =
      some (writerFinalConfiguration tape) := by
  rcases tape with ⟨left, head, right⟩
  simp only at hHead
  subst head
  let initial := writerInputConfiguration
    ({ left := left, head := endSymbol, right := right } : WorkTape)
  have hHalted : writerMachine.isHalted initial = false := by
    rfl
  have hFind : findWorkRule writerMachine.rules initial.state
      initial.tape.head = some writerRule := by
    apply findWorkRule_cons_of_matches
    exact ⟨rfl, rfl⟩
  have hStep := workStep?_eq_apply_of_find writerMachine initial writerRule
    hHalted hFind
  change
    (match workStep? writerMachine initial with
     | none => none
     | some next => some next) = _
  rw [hStep]
  rfl

/-! ## Canonical Finish coordinate and composed machine -/

def finishIndex {language : Language}
    (problem : VerifierTableauProblem language) :
    Fin (BuilderFullScheduleCursorController.bodySlotCount problem) :=
  ⟨problem.formulaClauseSlotCount * problem.formulaTokensPerClause, by
    rw [BuilderFullScheduleCursorController.bodySlotCount_eq]
    omega⟩

theorem finishIndex_postHeaderRoute {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem
        (finishIndex problem).val = .finish := by
  apply (BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_eq_finish_iff
    problem (finishIndex problem).val).2
  rfl

theorem finishIndex_scheduleEntry {language : Language}
    (problem : VerifierTableauProblem language) :
    scheduleEntry problem (finishIndex problem) = some .finish := by
  have hSelected := selectedEntry?_eq_some_getElem problem
    (finishIndex problem)
  have hFinish := selectedEntry?_finish problem (finishIndex problem).val
    (finishIndex_postHeaderRoute problem)
  rw [hFinish] at hSelected
  exact Option.some.inj hSelected.symm

theorem finishIndex_classifier_holds {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds problem
      (scheduleCoordinate problem (finishIndex problem)) workspace := by
  exact BuilderPostDividerRawRouteClassifier.inRangeRouteClassifierHolds problem
    (scheduleCoordinate problem (finishIndex problem)) workspace

def finishOutsideLeft (count : Nat) (classifierExterior : List WorkSymbol) :
    List WorkSymbol :=
  (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration count count
    classifierExterior).tape.left

def builderSuffix (input : BitString) (output : List CNFToken)
    (count : Nat) (classifierExterior : List WorkSymbol) : List WorkSymbol :=
  let workspace := BuilderTokenAppender.workspaceTape input
    (finishOutsideLeft count classifierExterior) output
  workspace.head :: workspace.right

def classifierInitialConfiguration (input : BitString)
    (output : List CNFToken) (count : Nat)
    (classifierExterior : List WorkSymbol) : WorkConfiguration :=
  appendRightExteriorConfiguration
    (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration count count
      classifierExterior)
    (builderSuffix input output count classifierExterior)

def classifierFinalConfiguration (input : BitString)
    (output : List CNFToken) (count : Nat)
    (classifierExterior : List WorkSymbol) : WorkConfiguration :=
  appendRightExteriorConfiguration
    (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration count count
      classifierExterior)
    (builderSuffix input output count classifierExterior)

theorem classifierFinal_head (input : BitString) (output : List CNFToken)
    (count : Nat) (classifierExterior : List WorkSymbol) :
    (classifierFinalConfiguration input output count classifierExterior).tape.head =
      endSymbol := by
  simp [classifierFinalConfiguration, appendRightExteriorConfiguration,
    appendRightExteriorTape,
    BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
    BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration, BuilderPostDividerRawRouteClassifier.appendExteriorTape,
    BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration, BuilderPostDividerRawRouteClassifier.compareResult_self,
    BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration]

theorem classifierFinal_state (input : BitString) (output : List CNFToken)
    (count : Nat) (classifierExterior : List WorkSymbol) :
    (classifierFinalConfiguration input output count classifierExterior).state =
      finishClassifierMachine.acceptState := by
  simp [classifierFinalConfiguration, appendRightExteriorConfiguration,
    finishClassifierMachine,
    BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
    BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration, BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
    BuilderPostDividerRawRouteClassifier.compareResult_self, BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration]

theorem classifier_workRunExact (input : BitString)
    (output : List CNFToken) (count : Nat)
    (classifierExterior : List WorkSymbol) :
    workRunExact? finishClassifierMachine (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps count count)
        (classifierInitialConfiguration input output count classifierExterior) =
      some (classifierFinalConfiguration input output count
        classifierExterior) := by
  rw [finishClassifierMachine_workRunExact]
  exact shielded_comparator_workRunExact_with_right_exterior count count
    classifierExterior (builderSuffix input output count classifierExterior)

theorem writerFinal_tape_eq_dispatch_entry (input : BitString)
    (output : List CNFToken) (count : Nat)
    (classifierExterior : List WorkSymbol) :
    (writerFinalConfiguration
      (classifierFinalConfiguration input output count
        classifierExterior).tape).tape =
      (BuilderPhysicalOptionalTokenDispatch.entryConfiguration input
        (finishOutsideLeft count classifierExterior) output
        (some .finish)).tape := by
  simp [writerFinalConfiguration, WorkTape.write,
    classifierFinalConfiguration,
    appendRightExteriorConfiguration, appendRightExteriorTape, builderSuffix,
    finishOutsideLeft, BuilderPhysicalOptionalTokenDispatch.entryConfiguration,
    BuilderPhysicalOptionalTokenDispatch.requestTape,
    BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
    BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration, BuilderPostDividerRawRouteClassifier.appendExteriorTape,
    BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration, BuilderPostDividerRawRouteClassifier.compareResult_self,
    BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration]

def classifierWriterMachine : WorkMachine :=
  PNP.Concrete.WorkMachineChain.machine finishClassifierMachine writerMachine

/-- One fixed machine containing the equal comparator, literal Finish writer,
and M217 dispatcher. -/
def machine : WorkMachine :=
  PNP.Concrete.WorkMachineChain.machine classifierWriterMachine dispatchMachine

theorem rules_length : machine.rules.length = 137 := by
  rfl

set_option maxRecDepth 1000000 in
theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  decide

def output {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  emittedPrefix problem (finishIndex problem).val

def entryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration PNP.Concrete.WorkMachineChain.firstState
    (renameConfiguration PNP.Concrete.WorkMachineChain.firstState
      (classifierInitialConfiguration problem.input (output problem)
        problem.formulaClauseSlotCount classifierExterior))

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration PNP.Concrete.WorkMachineChain.secondState
    (BuilderPhysicalOptionalTokenDispatch.finalConfiguration problem.input
      (finishOutsideLeft problem.formulaClauseSlotCount classifierExterior)
      (output problem) (some .finish))

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps problem.formulaClauseSlotCount
      problem.formulaClauseSlotCount +
    3 + BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem (finishIndex problem)

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) :
    workRunExact? machine (workSteps problem)
        (entryConfiguration problem classifierExterior) =
      some (finalConfiguration problem classifierExterior) := by
  let count := problem.formulaClauseSlotCount
  let emitted := output problem
  let classifierInitial := classifierInitialConfiguration problem.input emitted
    count classifierExterior
  let classifierFinal := classifierFinalConfiguration problem.input emitted
    count classifierExterior
  let writerInitial := writerInputConfiguration classifierFinal.tape
  let writerFinal := writerFinalConfiguration classifierFinal.tape
  let innerInitial := renameConfiguration PNP.Concrete.WorkMachineChain.firstState
    classifierInitial
  let innerFinal := renameConfiguration PNP.Concrete.WorkMachineChain.secondState
    writerFinal
  let dispatchInitial := BuilderPhysicalOptionalTokenDispatch.entryConfiguration problem.input
    (finishOutsideLeft count classifierExterior) emitted (some .finish)
  let dispatchFinal := BuilderPhysicalOptionalTokenDispatch.finalConfiguration problem.input
    (finishOutsideLeft count classifierExterior) emitted (some .finish)
  have hClassifier : workRunExact? finishClassifierMachine
      (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps count count) classifierInitial =
        some classifierFinal := by
    simpa [classifierInitial, classifierFinal, count, emitted] using
      classifier_workRunExact problem.input emitted count classifierExterior
  have hClassifierAccept : classifierFinal.state =
      finishClassifierMachine.acceptState := by
    simpa [classifierFinal, count, emitted] using
      classifierFinal_state problem.input emitted count classifierExterior
  have hWriter : workRunExact? writerMachine 1 writerInitial =
      some writerFinal := by
    apply writer_workRunExact
    simpa [writerInitial, classifierFinal, count, emitted] using
      classifierFinal_head problem.input emitted count classifierExterior
  have hInner := PNP.Concrete.WorkMachineChain.workRunExact finishClassifierMachine writerMachine
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps count count) 1 classifierInitial classifierFinal
    writerFinal hClassifier hClassifierAccept (by
      simpa [writerInitial, writerInputConfiguration] using hWriter)
  have hInnerAccept : innerFinal.state = classifierWriterMachine.acceptState := by
    rfl
  have hDispatchTape : writerFinal.tape = dispatchInitial.tape := by
    simpa [writerFinal, classifierFinal, dispatchInitial, count, emitted] using
      writerFinal_tape_eq_dispatch_entry problem.input emitted count
        classifierExterior
  have hDispatch : workRunExact? dispatchMachine
      (BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem (finishIndex problem))
      { state := dispatchMachine.startState, tape := innerFinal.tape } =
        some dispatchFinal := by
    have hCanonical := BuilderPhysicalOptionalTokenDispatch.workRunExact
      problem.input (finishOutsideLeft count classifierExterior) emitted
      (some .finish)
    have hRequest := finishIndex_scheduleEntry problem
    have hSteps :
        BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem
            (finishIndex problem) =
          BuilderPhysicalOptionalTokenDispatch.workSteps problem.input emitted
            (some .finish) := by
      simp [BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps,
        BuilderPhysicalOptionalTokenDispatch.canonicalRequest, hRequest,
        emitted, output]
    have hInitial :
        ({ state := dispatchMachine.startState, tape := innerFinal.tape } :
          WorkConfiguration) = dispatchInitial := by
      have hTape : innerFinal.tape = dispatchInitial.tape := by
        simpa [innerFinal, renameConfiguration] using hDispatchTape
      rw [hTape]
      rfl
    rw [hSteps, hInitial]
    exact hCanonical
  have hOuter := PNP.Concrete.WorkMachineChain.workRunExact classifierWriterMachine
    dispatchMachine
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps count count + 1 + 1)
    (BuilderPhysicalOptionalTokenDispatch.canonicalWorkSteps problem (finishIndex problem))
    innerInitial innerFinal dispatchFinal
    (by simpa [classifierWriterMachine, innerInitial, innerFinal] using hInner)
    hInnerAccept hDispatch
  simpa [machine, workSteps, entryConfiguration, finalConfiguration,
    innerInitial, innerFinal, classifierInitial, classifierFinal,
    dispatchFinal, count, emitted, Nat.add_assoc] using hOuter

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps problem)
        (encodeWorkConfiguration (entryConfiguration problem
          classifierExterior)) =
      encodeWorkConfiguration (finalConfiguration problem
        classifierExterior) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps problem) (entryConfiguration problem classifierExterior)
    (finalConfiguration problem classifierExterior)
    (workRunExact problem classifierExterior)

private theorem workRunExact_succ_split_last (selectedMachine : WorkMachine) :
    forall (steps : Nat) (initial final : WorkConfiguration),
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

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) :
    machine.isHalted
      (workRun machine (workSteps problem - 1)
        (entryConfiguration problem classifierExterior)) = false := by
  have hPositive : 0 < workSteps problem := by
    unfold workSteps
    omega
  let short := workSteps problem - 1
  have hSucc : short + 1 = workSteps problem := by
    dsimp [short]
    omega
  have hExact := workRunExact problem classifierExterior
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last machine short
      (entryConfiguration problem classifierExterior)
      (finalConfiguration problem classifierExterior) hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short
      (entryConfiguration problem classifierExterior) = before :=
    workRun_eq_of_workRunExact machine short
      (entryConfiguration problem classifierExterior) before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine before
    (finalConfiguration problem classifierExterior) hLast

def countPlusOnePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (formulaClauseCountPolynomial verifier) (.constant 1)

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add
    (.mul (.constant 36)
      (.mul (countPlusOnePolynomial verifier)
        (countPlusOnePolynomial verifier)))
    (.add (.constant 18) (BuilderPhysicalOptionalTokenDispatch.rawTimeBound verifier))

private theorem formulaClauseCountPolynomial_eval_eq_slotCount
    {language : Language} (problem : VerifierTableauProblem language) :
    (formulaClauseCountPolynomial problem.verifier).eval problem.input.length =
      problem.formulaClauseSlotCount := by
  have hCount := problem.formulaClauseCountPolynomial_eval
  simp only [BitString.size] at hCount
  simpa [VerifierTableauProblem.formulaClauseSlotCount,
    VerifierTableauProblem.formulaConstraintSlotCount,
    VerifierTableauProblem.formulaClauseSlotsPerConstraint,
    VerifierTableauProblem.formulaVariableSlotBound, BitString.size] using hCount

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      36 * ((problem.formulaClauseSlotCount + 1) *
        (problem.formulaClauseSlotCount + 1)) +
      (18 + (BuilderPhysicalOptionalTokenDispatch.rawTimeBound problem.verifier).eval
        problem.input.length) := by
  change
    36 * (((formulaClauseCountPolynomial problem.verifier).eval
      problem.input.length + 1) *
      ((formulaClauseCountPolynomial problem.verifier).eval
        problem.input.length + 1)) +
      (18 + (BuilderPhysicalOptionalTokenDispatch.rawTimeBound problem.verifier).eval
        problem.input.length) = _
  rw [formulaClauseCountPolynomial_eval_eq_slotCount]

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier := BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps_le
    problem.formulaClauseSlotCount problem.formulaClauseSlotCount
  have hClassifierScaled := Nat.mul_le_mul_left 6 hClassifier
  have hClassifierCompiled :
      6 * BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
          problem.formulaClauseSlotCount problem.formulaClauseSlotCount ≤
        36 * ((problem.formulaClauseSlotCount + 1) *
          (problem.formulaClauseSlotCount + 1)) := by
    simpa only [← Nat.mul_assoc] using hClassifierScaled
  have hDispatch := BuilderPhysicalOptionalTokenDispatch.canonicalCompiledSteps_le_rawTimeBound
    problem (finishIndex problem)
  rw [rawTimeBound_eval]
  unfold workSteps
  omega

def FinishRequestHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) : Prop :=
  workRunExact? machine (workSteps problem)
      (entryConfiguration problem classifierExterior) =
        some (finalConfiguration problem classifierExterior) ∧
    run (compileWorkMachine machine) (6 * workSteps problem)
      (encodeWorkConfiguration (entryConfiguration problem
        classifierExterior)) =
        encodeWorkConfiguration (finalConfiguration problem
          classifierExterior) ∧
    machine.isHalted
      (workRun machine (workSteps problem - 1)
        (entryConfiguration problem classifierExterior)) = false

theorem finishRequestHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (classifierExterior : List WorkSymbol) :
    FinishRequestHolds problem classifierExterior := by
  exact And.intro (workRunExact problem classifierExterior)
    (And.intro (run_compile_exact problem classifierExterior)
      (one_step_short_not_halted problem classifierExterior))

/-- M219 physically derives and dispatches the unique canonical `Finish`
request from M214's equal comparator terminal.  Body-token and padding request
generation and the complete literal schedule loop remain open. -/
theorem cook_levin_builder_physical_finish_request_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    scheduleEntry problem (finishIndex problem) = some .finish ∧
    (forall classifierWorkspace,
      BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds problem
        (scheduleCoordinate problem (finishIndex problem))
        classifierWorkspace) ∧
    machine.rules.length = 137 ∧
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) ∧
    (forall classifierExterior,
      FinishRequestHolds problem classifierExterior) ∧
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  exact And.intro (finishIndex_scheduleEntry problem)
    (And.intro (finishIndex_classifier_holds problem)
      (And.intro rules_length
        (And.intro rules_pairwise_query_distinct
          (And.intro (finishRequestHolds problem)
            (compiledSteps_le_rawTimeBound problem)))))

end BuilderPhysicalFinishRequest

end CookLevin

end PNP.Concrete
