/-
Copyright (c) 2026 PNP Labs.

One width-dependent successor transition after the first literal of the
second canonical Cook--Levin constraint.

The literal work table in this file evaluates the represented tableau width,
uses the existing unary-root controller to distinguish width one from a wider
tableau, and enters the already-audited token appender at either its `Finish`
or `T` state.  It emits exactly one token and then materializes the following
formula coordinate.  Both branches are present in one finite table and are
selected by the represented unary width; no host-side schedule lookup or
caller-supplied branch certificate is used.

This does not emit the following padding or unary token, complete another
literal, traverse the second constraint, implement a general schedule cursor,
complete the formula builder, or establish P = NP.
-/

import PNP.Concrete.CookLevinBuilderSecondConstraintFirstLiteralTerminatorStep

namespace PNP.Concrete

namespace CookLevin

namespace BuilderSecondConstraintFirstLiteralSuccessorTokenStep

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Width and retained-coordinate polynomials -/

def widthPolynomial {language : Language}
    (problem : VerifierTableauProblem language) : NatPolynomial :=
  formulaTapeWidthPolynomial problem.verifier

def width {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (widthPolynomial problem).eval problem.input.length

theorem width_eq_tapeWidth {language : Language}
    (problem : VerifierTableauProblem language) :
    width problem =
      problem.dimensions.tapeWidth problem.tableauInputMode := by
  simpa [width, widthPolynomial, BitString.size] using
    problem.formulaTapeWidthPolynomial_eval

theorem width_positive {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < width problem := by
  rw [width_eq_tapeWidth]
  exact problem.dimensions.tapeWidth_positive problem.tableauInputMode

def successorTokenSlotPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add
    (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial verifier)
    (.constant 7)

def successorTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (successorTokenSlotPolynomial problem.verifier).eval problem.input.length

theorem successorTokenSlot_eq_secondConstraintStart_add_seven
    {language : Language} (problem : VerifierTableauProblem language) :
    successorTokenSlot problem =
      problem.formulaVariableSlotBound + 1 +
        problem.formulaClauseSlotsPerConstraint *
          problem.formulaTokensPerClause + 7 := by
  unfold successorTokenSlot successorTokenSlotPolynomial
  rw [NatPolynomial.eval_add, NatPolynomial.eval_constant]
  change BuilderFirstConstraintPaddingRun.secondConstraintStart problem + 7 = _
  rw [BuilderFirstConstraintPaddingRun.secondConstraintStart_eq]

/-! ### One controller with two entries into one literal appender -/

namespace WidthBranchAppender

open BuilderFirstClausePrefix

def doneBridge : List WorkRule :=
  launchRules
    (WorkChain.firstState
      BuilderCompleteHeader.HeaderController.doneExitState)
    (WorkChain.secondState
      (BuilderTokenAppender.seekInputState .finish))

/-- The ordinary `WorkChain` bridge handles the wider `T` branch.  This
additional bridge handles the width-one `Finish` branch; both enter the same
literal 59-rule appender table at different states. -/
def rules : List WorkRule :=
  doneBridge ++
    WorkChain.rules BuilderCompleteHeader.HeaderController.machine
      BuilderTokenAppender.machine

def machine : WorkMachine :=
  { rules := rules
    startState := WorkChain.firstState
      BuilderCompleteHeader.HeaderController.machine.startState
    acceptState := WorkChain.secondState
      BuilderTokenAppender.machine.acceptState
    rejectState := WorkChain.secondState
      BuilderTokenAppender.machine.rejectState }

theorem rules_length : rules.length = 93 := by rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  exact WorkChain.machine_acceptState_ne_rejectState
    BuilderCompleteHeader.HeaderController.machine
    BuilderTokenAppender.machine
    BuilderTokenAppender.machine_acceptState_ne_rejectState

private theorem appender_rule_source_ne_accept (rule : WorkRule)
    (hMem : rule ∈ BuilderTokenAppender.machine.rules) :
    rule.sourceState ≠ BuilderTokenAppender.machine.acceptState := by
  decide +revert

theorem rule_source_ne_acceptState (rule : WorkRule)
    (hRule : rule ∈ machine.rules) :
    rule.sourceState ≠ machine.acceptState := by
  have hBase : WorkChain.NoRuleAtAccept
      (WorkChain.machine BuilderCompleteHeader.HeaderController.machine
        BuilderTokenAppender.machine) :=
    WorkChain.noRuleAtAccept
      BuilderCompleteHeader.HeaderController.machine
      BuilderTokenAppender.machine appender_rule_source_ne_accept
  change rule ∈ rules at hRule
  simp only [rules, List.mem_append] at hRule
  rcases hRule with hDone | hBaseRule
  · rcases List.mem_map.mp hDone with ⟨symbol, _hSymbol, hEqual⟩
    rw [← hEqual]
    exact WorkChain.firstState_ne_secondState _ _
  · exact hBase rule hBaseRule

private theorem state_ne_reject_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.rejectState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  rw [(nat_beq_true_iff _ _).mpr rfl] at hHalted
  cases hAccept : (source.rejectState == source.acceptState) <;>
    rw [hAccept] at hHalted <;> contradiction

private theorem state_ne_accept_of_not_halted
    (source : WorkMachine) (config : WorkConfiguration)
    (hHalted : source.isHalted config = false) :
    config.state ≠ source.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState] at hHalted
  rw [(nat_beq_true_iff _ _).mpr rfl] at hHalted
  cases hReject : (source.acceptState == source.rejectState) <;>
    rw [hReject] at hHalted <;> contradiction

private theorem workStep_eq_base_first
    (config : WorkConfiguration)
    (hDone :
      config.state ≠ BuilderCompleteHeader.HeaderController.doneExitState) :
    workStep? machine
        (renameConfiguration WorkChain.firstState config) =
      workStep?
        (WorkChain.machine BuilderCompleteHeader.HeaderController.machine
          BuilderTokenAppender.machine)
        (renameConfiguration WorkChain.firstState config) := by
  have hBridge : findWorkRule doneBridge
      (WorkChain.firstState config.state) config.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hDone (WorkChain.firstState_injective h).symm
  unfold workStep?
  rw [show machine.isHalted
      (renameConfiguration WorkChain.firstState config) =
        (WorkChain.machine BuilderCompleteHeader.HeaderController.machine
          BuilderTokenAppender.machine).isHalted
          (renameConfiguration WorkChain.firstState config) by rfl]
  change
    (if
        (WorkChain.machine BuilderCompleteHeader.HeaderController.machine
          BuilderTokenAppender.machine).isHalted
            (renameConfiguration WorkChain.firstState config) = true then
      none
    else
      match findWorkRule
          (doneBridge ++
            (WorkChain.machine
              BuilderCompleteHeader.HeaderController.machine
              BuilderTokenAppender.machine).rules)
          (WorkChain.firstState config.state) config.tape.head with
      | none => none
      | some rule =>
          some (applyWorkRule rule
            (renameConfiguration WorkChain.firstState config))) = _
  rw [findWorkRule_append_of_none _ _ _ _ hBridge]
  rfl

private theorem workStep_eq_base_second
    (config : WorkConfiguration) :
    workStep? machine
        (renameConfiguration WorkChain.secondState config) =
      workStep?
        (WorkChain.machine BuilderCompleteHeader.HeaderController.machine
          BuilderTokenAppender.machine)
        (renameConfiguration WorkChain.secondState config) := by
  have hBridge : findWorkRule doneBridge
      (WorkChain.secondState config.state) config.tape.head = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact WorkChain.firstState_ne_secondState _ _
  unfold workStep?
  rw [show machine.isHalted
      (renameConfiguration WorkChain.secondState config) =
        (WorkChain.machine BuilderCompleteHeader.HeaderController.machine
          BuilderTokenAppender.machine).isHalted
          (renameConfiguration WorkChain.secondState config) by rfl]
  change
    (if
        (WorkChain.machine BuilderCompleteHeader.HeaderController.machine
          BuilderTokenAppender.machine).isHalted
            (renameConfiguration WorkChain.secondState config) = true then
      none
    else
      match findWorkRule
          (doneBridge ++
            (WorkChain.machine
              BuilderCompleteHeader.HeaderController.machine
              BuilderTokenAppender.machine).rules)
          (WorkChain.secondState config.state) config.tape.head with
      | none => none
      | some rule =>
          some (applyWorkRule rule
            (renameConfiguration WorkChain.secondState config))) = _
  rw [findWorkRule_append_of_none _ _ _ _ hBridge]
  rfl

theorem controller_workStep_of_some
    (config next : WorkConfiguration)
    (hStep :
      workStep? BuilderCompleteHeader.HeaderController.machine config =
        some next) :
    workStep? machine
        (renameConfiguration WorkChain.firstState config) =
      some (renameConfiguration WorkChain.firstState next) := by
  have hHalted :
      BuilderCompleteHeader.HeaderController.machine.isHalted config =
        false := by
    cases hLocal :
        BuilderCompleteHeader.HeaderController.machine.isHalted config with
    | false => rfl
    | true =>
        unfold workStep? at hStep
        rw [hLocal] at hStep
        contradiction
  have hDone : config.state ≠
      BuilderCompleteHeader.HeaderController.doneExitState := by
    exact state_ne_reject_of_not_halted
      BuilderCompleteHeader.HeaderController.machine config hHalted
  have hMore : config.state ≠
      BuilderCompleteHeader.HeaderController.moreExitState := by
    exact state_ne_accept_of_not_halted
      BuilderCompleteHeader.HeaderController.machine config hHalted
  rw [workStep_eq_base_first config hDone]
  unfold workStep? at hStep
  rw [hHalted] at hStep
  cases hFind : findWorkRule
      BuilderCompleteHeader.HeaderController.machine.rules
      config.state config.tape.head with
  | none =>
      rw [hFind] at hStep
      contradiction
  | some rule =>
      rw [hFind] at hStep
      have hNext : applyWorkRule rule config = next :=
        Option.some.inj hStep
      have hGlobalHalted :=
        WorkChain.machine_isHalted_first_false
          BuilderCompleteHeader.HeaderController.machine
          BuilderTokenAppender.machine config
      have hGlobalFind := WorkChain.findWorkRule_first_of_some
        BuilderCompleteHeader.HeaderController.machine
        BuilderTokenAppender.machine config.state config.tape.head rule
        hMore hFind
      have hGlobalStep := workStep?_eq_apply_of_find
        (WorkChain.machine BuilderCompleteHeader.HeaderController.machine
          BuilderTokenAppender.machine)
        (renameConfiguration WorkChain.firstState config)
        (renameRule WorkChain.firstState rule)
        hGlobalHalted hGlobalFind
      calc
        workStep?
            (WorkChain.machine
              BuilderCompleteHeader.HeaderController.machine
              BuilderTokenAppender.machine)
            (renameConfiguration WorkChain.firstState config) =
          some (applyWorkRule (renameRule WorkChain.firstState rule)
            (renameConfiguration WorkChain.firstState config)) :=
              hGlobalStep
        _ = some (renameConfiguration WorkChain.firstState
            (applyWorkRule rule config)) :=
              congrArg Option.some
                (applyWorkRule_rename WorkChain.firstState rule config)
        _ = some (renameConfiguration WorkChain.firstState next) :=
              congrArg
                (fun value =>
                  some (renameConfiguration WorkChain.firstState value))
                hNext

theorem appender_workStep_of_some
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderTokenAppender.machine config = some next) :
    workStep? machine
        (renameConfiguration WorkChain.secondState config) =
      some (renameConfiguration WorkChain.secondState next) := by
  rw [workStep_eq_base_second config]
  exact WorkChain.second_workStep_of_some
    BuilderCompleteHeader.HeaderController.machine
    BuilderTokenAppender.machine config next hStep

theorem controller_more_launch_workStep (tape : WorkTape) :
    workStep? machine
        (renameConfiguration WorkChain.firstState
          { state := BuilderCompleteHeader.HeaderController.moreExitState
            tape := tape }) =
      some
        (renameConfiguration WorkChain.secondState
          (BuilderTokenAppender.entryConfiguration .t tape)) := by
  have hDone :
      BuilderCompleteHeader.HeaderController.moreExitState ≠
        BuilderCompleteHeader.HeaderController.doneExitState := by decide
  rw [workStep_eq_base_first _ hDone]
  simpa [BuilderCompleteHeader.HeaderController.machine,
    BuilderTokenAppender.machine,
    BuilderTokenAppender.entryConfiguration] using
    WorkChain.launch_workStep
      BuilderCompleteHeader.HeaderController.machine
      BuilderTokenAppender.machine tape

theorem controller_done_launch_workStep (tape : WorkTape) :
    workStep? machine
        (renameConfiguration WorkChain.firstState
          { state := BuilderCompleteHeader.HeaderController.doneExitState
            tape := tape }) =
      some
        (renameConfiguration WorkChain.secondState
          (BuilderTokenAppender.entryConfiguration .finish tape)) := by
  let start : WorkConfiguration :=
    renameConfiguration WorkChain.firstState
      { state := BuilderCompleteHeader.HeaderController.doneExitState
        tape := tape }
  let target : WorkConfiguration :=
    renameConfiguration WorkChain.secondState
      (BuilderTokenAppender.entryConfiguration .finish tape)
  have hHalted : machine.isHalted start = false := by
    simp [machine, start, WorkMachine.isHalted, renameConfiguration,
      WorkChain.firstState_ne_secondState]
  have hBridge := findWorkRule_launchRules
    (WorkChain.firstState
      BuilderCompleteHeader.HeaderController.doneExitState)
    (WorkChain.secondState
      (BuilderTokenAppender.seekInputState .finish)) tape.head
  have hFind : findWorkRule machine.rules start.state start.tape.head =
      some (launchRule
        (WorkChain.firstState
          BuilderCompleteHeader.HeaderController.doneExitState)
        (WorkChain.secondState
          (BuilderTokenAppender.seekInputState .finish)) tape.head) := by
    change findWorkRule rules
      (WorkChain.firstState
        BuilderCompleteHeader.HeaderController.doneExitState)
      tape.head = _
    unfold rules
    exact findWorkRule_append_of_some _ _ _ _ _ hBridge
  have hStep := workStep?_eq_apply_of_find machine start
    (launchRule
      (WorkChain.firstState
        BuilderCompleteHeader.HeaderController.doneExitState)
      (WorkChain.secondState
        (BuilderTokenAppender.seekInputState .finish)) tape.head)
    hHalted hFind
  simpa [start, target, BuilderTokenAppender.entryConfiguration,
    renameConfiguration, launchRule, applyWorkRule, WorkTape.move] using hStep

theorem controller_workRunExact (steps : Nat)
    (start final : WorkConfiguration)
    (hRun :
      workRunExact? BuilderCompleteHeader.HeaderController.machine
        steps start = some final) :
    workRunExact? machine steps
        (renameConfiguration WorkChain.firstState start) =
      some (renameConfiguration WorkChain.firstState final) := by
  exact workRunExact?_transport
    BuilderCompleteHeader.HeaderController.machine machine
    WorkChain.firstState controller_workStep_of_some steps start final hRun

theorem appender_workRunExact (steps : Nat)
    (start final : WorkConfiguration)
    (hRun : workRunExact? BuilderTokenAppender.machine
      steps start = some final) :
    workRunExact? machine steps
        (renameConfiguration WorkChain.secondState start) =
      some (renameConfiguration WorkChain.secondState final) := by
  exact workRunExact?_transport BuilderTokenAppender.machine machine
    WorkChain.secondState appender_workStep_of_some steps start final hRun

private theorem workRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

theorem workRunExact (input : BitString)
    (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) (output : List CNFToken)
    (hPrefix : ∀ symbol ∈ wordPrefix,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol) :
    let request := if remaining = 0 then CNFToken.finish else CNFToken.t
    workRunExact? machine
        (BuilderCompleteHeader.HeaderController.steps
            wordPrefix.length remaining +
          1 + BuilderTokenAppender.workSteps input output)
        (renameConfiguration WorkChain.firstState
          (BuilderCompleteHeader.HeaderController.initialConfiguration
            input wordPrefix remaining tail output)) =
      some
        (renameConfiguration WorkChain.secondState
          (BuilderTokenAppender.finalConfiguration input
            (BuilderCompleteHeader.HeaderController.outsideAfter
              wordPrefix remaining tail)
            (output ++ [request]))) := by
  dsimp
  let controllerInitial :=
    BuilderCompleteHeader.HeaderController.initialConfiguration
      input wordPrefix remaining tail output
  let controllerFinal :=
    BuilderCompleteHeader.HeaderController.finalConfiguration
      input wordPrefix remaining tail output
  have hControllerLocal :=
    BuilderCompleteHeader.HeaderController.workRunExact_of_unit_or_separator
      input wordPrefix remaining tail output hPrefix
  have hController : workRunExact? machine
      (BuilderCompleteHeader.HeaderController.steps
        wordPrefix.length remaining)
      (renameConfiguration WorkChain.firstState controllerInitial) =
        some (renameConfiguration WorkChain.firstState controllerFinal) := by
    exact controller_workRunExact _ _ _ hControllerLocal
  by_cases hZero : remaining = 0
  · subst remaining
    let appenderInitial :=
      BuilderTokenAppender.entryConfiguration .finish
        (BuilderTokenAppender.workspaceTape input
          (BuilderCompleteHeader.HeaderController.outsideAfter
            wordPrefix 0 tail) output)
    let appenderFinal :=
      BuilderTokenAppender.finalConfiguration input
        (BuilderCompleteHeader.HeaderController.outsideAfter
          wordPrefix 0 tail) (output ++ [.finish])
    have hLaunch : workRunExact? machine 1
        (renameConfiguration WorkChain.firstState controllerFinal) =
          some (renameConfiguration WorkChain.secondState
            appenderInitial) := by
      apply workRunExact_one
      simpa [controllerFinal,
        BuilderCompleteHeader.HeaderController.finalConfiguration,
        appenderInitial] using controller_done_launch_workStep
          (BuilderTokenAppender.workspaceTape input
            (BuilderCompleteHeader.HeaderController.outsideAfter
              wordPrefix 0 tail) output)
    have hAppenderLocal :=
      BuilderTokenAppender.appendToken_workRunExact input
        (BuilderCompleteHeader.HeaderController.outsideAfter
          wordPrefix 0 tail) output .finish
    have hAppender : workRunExact? machine
        (BuilderTokenAppender.workSteps input output)
        (renameConfiguration WorkChain.secondState appenderInitial) =
          some (renameConfiguration WorkChain.secondState appenderFinal) := by
      exact appender_workRunExact _ _ _ hAppenderLocal
    have h01 := PipelineMachineSimulation.workRunExact?_compose machine
      (BuilderCompleteHeader.HeaderController.steps wordPrefix.length 0)
      1 _ _ _ hController hLaunch
    have h02 := PipelineMachineSimulation.workRunExact?_compose machine
      (BuilderCompleteHeader.HeaderController.steps wordPrefix.length 0 + 1)
      (BuilderTokenAppender.workSteps input output)
      _ _ _ h01 hAppender
    simpa [controllerInitial, controllerFinal, appenderInitial,
      appenderFinal, Nat.add_assoc] using h02
  · cases remaining with
    | zero => contradiction
    | succ rest =>
      let appenderInitial :=
        BuilderTokenAppender.entryConfiguration .t
          (BuilderTokenAppender.workspaceTape input
            (BuilderCompleteHeader.HeaderController.outsideAfter
              wordPrefix (rest + 1) tail) output)
      let appenderFinal :=
        BuilderTokenAppender.finalConfiguration input
          (BuilderCompleteHeader.HeaderController.outsideAfter
            wordPrefix (rest + 1) tail) (output ++ [.t])
      have hLaunch : workRunExact? machine 1
          (renameConfiguration WorkChain.firstState controllerFinal) =
            some (renameConfiguration WorkChain.secondState
              appenderInitial) := by
        apply workRunExact_one
        simpa [controllerFinal,
          BuilderCompleteHeader.HeaderController.finalConfiguration,
          appenderInitial] using controller_more_launch_workStep
            (BuilderTokenAppender.workspaceTape input
              (BuilderCompleteHeader.HeaderController.outsideAfter
                wordPrefix (rest + 1) tail) output)
      have hAppenderLocal :=
        BuilderTokenAppender.appendToken_workRunExact input
          (BuilderCompleteHeader.HeaderController.outsideAfter
            wordPrefix (rest + 1) tail) output .t
      have hAppender : workRunExact? machine
          (BuilderTokenAppender.workSteps input output)
          (renameConfiguration WorkChain.secondState appenderInitial) =
            some (renameConfiguration WorkChain.secondState appenderFinal) := by
        exact appender_workRunExact _ _ _ hAppenderLocal
      have h01 := PipelineMachineSimulation.workRunExact?_compose machine
        (BuilderCompleteHeader.HeaderController.steps
          wordPrefix.length (rest + 1))
        1 _ _ _ hController hLaunch
      have h02 := PipelineMachineSimulation.workRunExact?_compose machine
        (BuilderCompleteHeader.HeaderController.steps
          wordPrefix.length (rest + 1) + 1)
        (BuilderTokenAppender.workSteps input output)
        _ _ _ h01 hAppender
      simpa [controllerInitial, controllerFinal, appenderInitial,
        appenderFinal, hZero, Nat.add_assoc] using h02

end WidthBranchAppender

/-! ### Sequential evaluator/branch/evaluator composition -/

def widthEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine (widthPolynomial problem)

def targetEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (successorTokenSlotPolynomial problem.verifier)

def widthBranchMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (widthEvaluator problem) WidthBranchAppender.machine

def suffixMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (widthBranchMachine problem) (targetEvaluator problem)

def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
    (suffixMachine problem)

private theorem predecessor_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem) := by
  exact
    BuilderSecondConstraintFirstLiteralTerminatorStep.rule_source_ne_acceptState
      problem

private theorem widthEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (widthEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt
    (BuilderUnaryPolynomial.rule_source_lt_acceptState
      (widthPolynomial problem) rule hRule)

private theorem branch_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      WidthBranchAppender.machine :=
  WidthBranchAppender.rule_source_ne_acceptState

private theorem targetEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (targetEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt
    (BuilderUnaryPolynomial.rule_source_lt_acceptState
      (successorTokenSlotPolynomial problem.verifier) rule hRule)

private theorem widthBranch_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (widthBranchMachine problem) := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (widthEvaluator problem) WidthBranchAppender.machine
    branch_noRuleAtAccept

private theorem suffix_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (suffixMachine problem) := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (widthBranchMachine problem) (targetEvaluator problem)
    (targetEvaluator_noRuleAtAccept problem)

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      5284 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstLiteralPrefix.nextTokenSlotPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstClausePrefix.nextTokenSlotPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstClausePaddingRun.remainingPaddingPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstClausePaddingRun.secondClauseStartPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondClausePaddingRun.remainingPaddingPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondClausePaddingRun.thirdClauseStartPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderThirdClausePaddingRun.remainingPaddingPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderThirdClausePaddingRun.fourthClauseStartPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFourthClausePaddingRun.remainingPaddingPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFourthClausePaddingRun.fifthClauseSlotStartPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFifthClausePaddingRun.paddingPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFifthClausePaddingRun.sixthClauseSlotStartPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstConstraintPaddingRun.paddingPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount (widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (successorTokenSlotPolynomial problem.verifier) := by
  have hPredecessor :=
    BuilderSecondConstraintFirstLiteralTerminatorStep.rules_length problem
  have hWidth := BuilderUnaryPolynomial.rules_length (widthPolynomial problem)
  have hTarget := BuilderUnaryPolynomial.rules_length
    (successorTokenSlotPolynomial problem.verifier)
  have hBranch := WidthBranchAppender.rules_length
  have hLaunch : ∀ source target,
      (launchRules source target).length = 9 := by
    intro source target
    rfl
  unfold machine suffixMachine widthBranchMachine
    BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
    BuilderFirstClausePrefix.WorkChain.bridgeRules
  simp only [List.length_append, List.length_map, widthEvaluator,
    targetEvaluator, WidthBranchAppender.machine,
    BuilderUnaryPolynomial.machine]
  rw [hPredecessor, hWidth, hTarget, hBranch,
    hLaunch, hLaunch, hLaunch]
  omega

theorem rules_pairwise_query_distinct {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  have hWidthBranch :=
    BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
      (widthEvaluator problem) WidthBranchAppender.machine
      (BuilderUnaryPolynomial.rules_pairwise_query_distinct
        (widthPolynomial problem))
      WidthBranchAppender.rules_pairwise_query_distinct
      (widthEvaluator_noRuleAtAccept problem)
  have hSuffix :=
    BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
      (widthBranchMachine problem) (targetEvaluator problem)
      hWidthBranch
      (BuilderUnaryPolynomial.rules_pairwise_query_distinct
        (successorTokenSlotPolynomial problem.verifier))
      (widthBranch_noRuleAtAccept problem)
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
    (suffixMachine problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.rules_pairwise_query_distinct
      problem)
    hSuffix (predecessor_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
    (suffixMachine problem)
    (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
      (widthBranchMachine problem) (targetEvaluator problem)
      (BuilderUnaryPolynomial.machine_acceptState_ne_rejectState
        (successorTokenSlotPolynomial problem.verifier)))

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
    (suffixMachine problem) (suffix_noRuleAtAccept problem) rule hRule

/-! ### Exact workspace geometry -/

def successorToken {language : Language}
    (problem : VerifierTableauProblem language) : CNFToken :=
  if width problem = 1 then .finish else .t

def secondConstraintFirstLiteralSuccessorTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
      problem ++
    [successorToken problem]

def widthWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.scratchWord
    (widthPolynomial problem) problem.input.length

def widthRootPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (BuilderUnaryPolynomial.rootPrefixPolynomial
    (widthPolynomial problem)).eval problem.input.length

def widthControllerPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  widthRootPrefixLength problem - 1

def widthOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (widthPolynomial problem) problem.input
    (BuilderSecondConstraintFirstLiteralTerminatorStep.finalOutside problem)

def widthTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (widthOutside problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
      problem)

def controllerFinalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (widthWord problem).take (widthRootPrefixLength problem) ++
    List.replicate (width problem - 1)
      BuilderUnaryPolynomial.unitSymbol ++
    [BuilderUnaryPolynomial.scratchEndSymbol,
     BuilderUnaryPolynomial.scratchEndSymbol] ++
    (BuilderSecondConstraintFirstLiteralTerminatorStep.finalOutside problem).drop
      ((widthWord problem).length + 1)

def branchFinalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (controllerFinalOutside problem)
    (secondConstraintFirstLiteralSuccessorTokens problem)

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (successorTokenSlotPolynomial problem.verifier) problem.input
    (controllerFinalOutside problem)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (secondConstraintFirstLiteralSuccessorTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def widthWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderUnaryPolynomial.workSteps
    (widthPolynomial problem) problem.input

def controllerWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderCompleteHeader.HeaderController.steps
    (widthControllerPrefixLength problem) (width problem - 1)

def appenderWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderTokenAppender.workSteps problem.input
    (BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
      problem)

def branchWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  controllerWorkSteps problem + 1 + appenderWorkSteps problem

def targetWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderUnaryPolynomial.workSteps
    (successorTokenSlotPolynomial problem.verifier) problem.input

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderSecondConstraintFirstLiteralTerminatorStep.workSteps problem + 1 +
    widthWorkSteps problem + 1 +
    branchWorkSteps problem + 1 +
    targetWorkSteps problem

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem)
    (secondConstraintFirstLiteralSuccessorTokens problem)

theorem widthEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (widthEvaluator problem) (widthWorkSteps problem)
        (BuilderUnaryPolynomial.initialConfiguration
          (widthPolynomial problem) problem.input
          (BuilderSecondConstraintFirstLiteralTerminatorStep.finalOutside
            problem)
          (BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
            problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (widthPolynomial problem) problem.input
          (BuilderSecondConstraintFirstLiteralTerminatorStep.finalOutside
            problem)
          (BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
            problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (widthPolynomial problem) problem.input
    (BuilderSecondConstraintFirstLiteralTerminatorStep.finalOutside problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
      problem)

private theorem take_prefix_separator
    (wordPrefix suffix : List WorkSymbol) :
    (wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol :: suffix).take
        (wordPrefix.length + 1) =
      wordPrefix ++ [BuilderUnaryPolynomial.separatorSymbol] := by
  induction wordPrefix with
  | nil => rfl
  | cons first rest ih => simp [ih]

private theorem replicate_succ_append (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change item :: List.replicate (count + 1) item =
        (item :: List.replicate count item) ++ [item]
      rw [ih]
      simp only [List.cons_append]

theorem branchAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? WidthBranchAppender.machine (branchWorkSteps problem)
        (workStartConfiguration WidthBranchAppender.machine
          (widthTape problem)) =
      some
        { state := WidthBranchAppender.machine.acceptState
          tape := branchFinalTape problem } := by
  let polynomial := widthPolynomial problem
  let scratch := widthWord problem
  let outside :=
    BuilderSecondConstraintFirstLiteralTerminatorStep.finalOutside problem
  let output :=
    BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
      problem
  rcases BuilderUnaryPolynomial.root_register_length polynomial
      problem.input.length with ⟨wordPrefix, hScratch, hPrefixLength⟩
  have hWidthEval : polynomial.eval problem.input.length = width problem := rfl
  rw [hWidthEval] at hScratch
  have hPrefixLength' : wordPrefix.length + 1 =
      widthRootPrefixLength problem := by
    simpa [polynomial, widthRootPrefixLength] using hPrefixLength
  have hScratch' : scratch =
      wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
        List.replicate (width problem)
          BuilderUnaryPolynomial.unitSymbol := by
    simpa [scratch, widthWord, polynomial] using hScratch
  have hPositive := width_positive problem
  cases hWidth : width problem with
  | zero =>
      rw [hWidth] at hPositive
      exact False.elim (Nat.not_lt_zero 0 hPositive)
  | succ remaining =>
      have hScratchLength : scratch.length + 1 =
          wordPrefix.length + (remaining + 1 + 1) + 1 := by
        rw [hScratch']
        simp [hWidth]
      let tail :=
        outside.drop (wordPrefix.length + (remaining + 1 + 1) + 1)
      have hWidthOutside : widthOutside problem =
          BuilderCompleteHeader.HeaderController.outsideBefore
            wordPrefix remaining tail := by
        change scratch ++ BuilderUnaryPolynomial.scratchEndSymbol ::
            outside.drop (scratch.length + 1) = _
        rw [hScratchLength, hScratch']
        simp [BuilderCompleteHeader.HeaderController.outsideBefore,
          tail, hWidth, replicate_succ_append,
          List.append_assoc]
      have hPrefixSymbols : ∀ symbol ∈ wordPrefix,
          symbol = BuilderUnaryPolynomial.unitSymbol ∨
          symbol = BuilderUnaryPolynomial.separatorSymbol := by
        intro symbol hMem
        have hInScratch : symbol ∈ scratch := by
          rw [hScratch']
          exact List.mem_append_left _ hMem
        exact BuilderUnaryPolynomial.scratchWord_symbol polynomial
          problem.input.length symbol (by
            simpa [scratch, widthWord, polynomial] using hInScratch)
      have hRun := WidthBranchAppender.workRunExact problem.input
        wordPrefix remaining tail output hPrefixSymbols
      have hFinalOutside : controllerFinalOutside problem =
          BuilderCompleteHeader.HeaderController.outsideAfter
            wordPrefix remaining tail := by
        change scratch.take (widthRootPrefixLength problem) ++
            List.replicate (width problem - 1)
              BuilderUnaryPolynomial.unitSymbol ++
            [BuilderUnaryPolynomial.scratchEndSymbol,
             BuilderUnaryPolynomial.scratchEndSymbol] ++
            outside.drop (scratch.length + 1) = _
        rw [hScratchLength, hScratch', ← hPrefixLength', hWidth]
        rw [take_prefix_separator]
        simp [BuilderCompleteHeader.HeaderController.outsideAfter,
          tail, List.append_assoc]
      have hToken : successorToken problem =
          (if remaining = 0 then CNFToken.finish else CNFToken.t) := by
        unfold successorToken
        rw [hWidth]
        cases remaining <;> rfl
      simpa [branchWorkSteps, controllerWorkSteps,
        widthControllerPrefixLength, ← hPrefixLength', hWidth,
        appenderWorkSteps, widthTape, branchFinalTape,
        secondConstraintFirstLiteralSuccessorTokens,
        hWidthOutside, hFinalOutside, hToken,
        WidthBranchAppender.machine,
        BuilderCompleteHeader.HeaderController.machine,
        BuilderTokenAppender.finalConfiguration, output,
        BuilderCompleteHeader.HeaderController.initialConfiguration,
        workStartConfiguration, renameConfiguration] using hRun

theorem targetEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (targetEvaluator problem) (targetWorkSteps problem)
        (BuilderUnaryPolynomial.initialConfiguration
          (successorTokenSlotPolynomial problem.verifier) problem.input
          (controllerFinalOutside problem)
          (secondConstraintFirstLiteralSuccessorTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (successorTokenSlotPolynomial problem.verifier) problem.input
          (controllerFinalOutside problem)
          (secondConstraintFirstLiteralSuccessorTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (successorTokenSlotPolynomial problem.verifier) problem.input
    (controllerFinalOutside problem)
    (secondConstraintFirstLiteralSuccessorTokens problem)

private theorem widthBranch_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (widthBranchMachine problem)
        (widthWorkSteps problem + 1 + branchWorkSteps problem)
        (workStartConfiguration (widthBranchMachine problem)
          (BuilderSecondConstraintFirstLiteralTerminatorStep.finalTape
            problem)) =
      some
        { state := (widthBranchMachine problem).acceptState
          tape := branchFinalTape problem } := by
  let widthInitial := BuilderUnaryPolynomial.initialConfiguration
    (widthPolynomial problem) problem.input
    (BuilderSecondConstraintFirstLiteralTerminatorStep.finalOutside problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
      problem)
  let widthFinal := BuilderUnaryPolynomial.finalConfiguration
    (widthPolynomial problem) problem.input
    (BuilderSecondConstraintFirstLiteralTerminatorStep.finalOutside problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
      problem)
  let branchInitial := workStartConfiguration WidthBranchAppender.machine
    (widthTape problem)
  let branchFinal : WorkConfiguration :=
    { state := WidthBranchAppender.machine.acceptState
      tape := branchFinalTape problem }
  have hWidth : workRunExact? (widthEvaluator problem)
      (widthWorkSteps problem) widthInitial = some widthFinal := by
    simpa [widthInitial, widthFinal] using
      widthEvaluator_workRunExact problem
  have hBranch : workRunExact? WidthBranchAppender.machine
      (branchWorkSteps problem) branchInitial = some branchFinal := by
    simpa [branchInitial, branchFinal] using
      branchAppender_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (widthEvaluator problem) WidthBranchAppender.machine
    (widthWorkSteps problem) (branchWorkSteps problem)
    widthInitial widthFinal branchFinal hWidth (by rfl)
    hBranch
  simpa [widthBranchMachine, widthInitial, branchFinal,
    widthEvaluator, BuilderUnaryPolynomial.initialConfiguration,
    BuilderSecondConstraintFirstLiteralTerminatorStep.finalTape,
    BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

theorem suffix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (suffixMachine problem)
        (widthWorkSteps problem + 1 + branchWorkSteps problem + 1 +
          targetWorkSteps problem)
        (workStartConfiguration (suffixMachine problem)
          (BuilderSecondConstraintFirstLiteralTerminatorStep.finalTape
            problem)) =
      some
        { state := (suffixMachine problem).acceptState
          tape := finalTape problem } := by
  let widthBranchInitial := workStartConfiguration
    (widthBranchMachine problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.finalTape problem)
  let widthBranchFinal : WorkConfiguration :=
    { state := (widthBranchMachine problem).acceptState
      tape := branchFinalTape problem }
  let targetInitial := BuilderUnaryPolynomial.initialConfiguration
    (successorTokenSlotPolynomial problem.verifier) problem.input
    (controllerFinalOutside problem)
    (secondConstraintFirstLiteralSuccessorTokens problem)
  let targetFinal := BuilderUnaryPolynomial.finalConfiguration
    (successorTokenSlotPolynomial problem.verifier) problem.input
    (controllerFinalOutside problem)
    (secondConstraintFirstLiteralSuccessorTokens problem)
  have hWidthBranch : workRunExact? (widthBranchMachine problem)
      (widthWorkSteps problem + 1 + branchWorkSteps problem)
      widthBranchInitial = some widthBranchFinal := by
    simpa [widthBranchInitial, widthBranchFinal] using
      widthBranch_workRunExact problem
  have hTarget : workRunExact? (targetEvaluator problem)
      (targetWorkSteps problem) targetInitial = some targetFinal := by
    simpa [targetInitial, targetFinal] using
      targetEvaluator_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (widthBranchMachine problem) (targetEvaluator problem)
    (widthWorkSteps problem + 1 + branchWorkSteps problem)
    (targetWorkSteps problem)
    widthBranchInitial widthBranchFinal targetFinal hWidthBranch rfl
    hTarget
  simpa [suffixMachine, widthBranchInitial, targetFinal, finalTape,
    finalOutside, targetEvaluator,
    BuilderUnaryPolynomial.finalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration, Nat.add_assoc] using hCombined

set_option maxHeartbeats 1000000 in
theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderSecondConstraintFirstLiteralTerminatorStep.workSteps problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (workStartConfiguration
            (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
            (rawInputWorkTape problem.input))) =
      some
        (renameConfiguration
          BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondConstraintFirstLiteralTerminatorStep.finalConfiguration
            problem)) := by
  have hTransport := workRunExact?_transport
    (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
    (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
      (suffixMachine problem))
  have hRun := hTransport
    (BuilderSecondConstraintFirstLiteralTerminatorStep.workSteps problem)
    (workStartConfiguration
      (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderSecondConstraintFirstLiteralTerminatorStep.finalConfiguration
      problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.workRunExact problem)
  exact hRun

theorem prefixSuffix_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondConstraintFirstLiteralTerminatorStep.finalConfiguration
            problem)) =
      some
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (workStartConfiguration (suffixMachine problem)
            (BuilderSecondConstraintFirstLiteralTerminatorStep.finalTape
              problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
    (suffixMachine problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.finalTape problem)
  simpa [machine,
    BuilderSecondConstraintFirstLiteralTerminatorStep.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let prefixInitial := workStartConfiguration
    (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal :=
    BuilderSecondConstraintFirstLiteralTerminatorStep.finalConfiguration problem
  let suffixFinal : WorkConfiguration :=
    { state := (suffixMachine problem).acceptState
      tape := finalTape problem }
  have hPrefix : workRunExact?
      (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
      (BuilderSecondConstraintFirstLiteralTerminatorStep.workSteps problem)
      prefixInitial = some prefixFinal := by
    simpa [prefixInitial, prefixFinal] using
      BuilderSecondConstraintFirstLiteralTerminatorStep.workRunExact problem
  have hSuffix : workRunExact? (suffixMachine problem)
      (widthWorkSteps problem + 1 + branchWorkSteps problem + 1 +
        targetWorkSteps problem)
      { state := (suffixMachine problem).startState
        tape := prefixFinal.tape } = some suffixFinal := by
    simpa [prefixFinal, suffixFinal,
      BuilderSecondConstraintFirstLiteralTerminatorStep.finalConfiguration,
      workStartConfiguration] using suffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
    (suffixMachine problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.workSteps problem)
    (widthWorkSteps problem + 1 + branchWorkSteps problem + 1 +
      targetWorkSteps problem)
    prefixInitial prefixFinal suffixFinal hPrefix rfl hSuffix
  simpa [machine, workSteps, prefixInitial, suffixFinal,
    finalConfiguration, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration, Nat.add_assoc] using hCombined

/-! ### Exact schedule boundary -/

theorem successorToken_eq_finish_or_t {language : Language}
    (problem : VerifierTableauProblem language) :
    successorToken problem =
      if problem.dimensions.tapeWidth problem.tableauInputMode = 1
        then CNFToken.finish else CNFToken.t := by
  unfold successorToken
  rw [width_eq_tapeWidth]

theorem successorToken_eq_finish_iff {language : Language}
    (problem : VerifierTableauProblem language) :
    successorToken problem = CNFToken.finish ↔
      problem.dimensions.tapeWidth problem.tableauInputMode = 1 := by
  rw [successorToken_eq_finish_or_t]
  by_cases hWidth :
      problem.dimensions.tapeWidth problem.tableauInputMode = 1
  · simp [hWidth]
  · simp [hWidth]

theorem successorToken_eq_t_iff {language : Language}
    (problem : VerifierTableauProblem language) :
    successorToken problem = CNFToken.t ↔
      problem.dimensions.tapeWidth problem.tableauInputMode ≠ 1 := by
  rw [successorToken_eq_finish_or_t]
  by_cases hWidth :
      problem.dimensions.tapeWidth problem.tableauInputMode = 1
  · simp [hWidth]
  · simp [hWidth]

theorem specification_successor_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderSecondConstraintFirstLiteralTerminatorStep.finalTokenSlot
          problem⟩ =
      some (some (successorToken problem),
        ⟨BuilderSecondConstraintFirstLiteralTerminatorStep.finalTokenSlot
          problem + 1⟩) := by
  rw [successorToken_eq_finish_or_t]
  exact
    BuilderSecondConstraintFirstLiteralTerminatorStep.specification_next_step
      problem

/-- The finite output is exactly the canonical token prefix through the
width-selected successor of the second constraint's first literal. -/
theorem secondConstraintFirstLiteralSuccessorTokens_eq_canonical_formula_prefix
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest, encodeCNFTokens problem.formula =
      secondConstraintFirstLiteralSuccessorTokens problem ++ rest := by
  rcases
      BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor
        problem with
    ⟨rest, hTokens⟩
  refine ⟨rest, ?_⟩
  unfold secondConstraintFirstLiteralSuccessorTokens
  rw [successorToken_eq_finish_or_t]
  exact hTokens

private theorem encodeTokenPairs_append_local
    (left right : List CNFToken) :
    encodeTokenPairs (left ++ right) =
      encodeTokenPairs left ++ encodeTokenPairs right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        simp [encodeTokenPairs, ih, List.append_assoc]

def finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  successorTokenSlot problem

theorem finalTokenSlot_eq_predecessor_add_one {language : Language}
    (problem : VerifierTableauProblem language) :
    finalTokenSlot problem =
      BuilderSecondConstraintFirstLiteralTerminatorStep.finalTokenSlot problem +
        1 := by
  rw [finalTokenSlot, successorTokenSlot_eq_secondConstraintStart_add_seven,
    BuilderSecondConstraintFirstLiteralTerminatorStep.finalTokenSlot_eq_secondConstraintStart_add_six]

theorem finalTokenSlot_eq_secondConstraintStart_add_seven
    {language : Language} (problem : VerifierTableauProblem language) :
    finalTokenSlot problem =
      problem.formulaVariableSlotBound + 1 +
        problem.formulaClauseSlotsPerConstraint *
          problem.formulaTokensPerClause + 7 := by
  exact successorTokenSlot_eq_secondConstraintStart_add_seven problem

/-- The retained coordinate identifies the opportunity following the emitted
successor: padding at width one, otherwise the next unary `T`. -/
theorem followingTokenSlot_direct_eq_padding_or_t {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect (finalTokenSlot problem) =
      some
        (if problem.dimensions.tapeWidth problem.tableauInputMode = 1
          then none else some CNFToken.t) := by
  rw [finalTokenSlot_eq_predecessor_add_one]
  exact
    BuilderSecondConstraintFirstLiteralTerminatorStep.followingTokenSlot_direct_eq_padding_or_t
      problem

theorem specification_following_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨finalTokenSlot problem⟩ =
      some
        ((if problem.dimensions.tapeWidth problem.tableauInputMode = 1
          then none else some CNFToken.t),
        ⟨finalTokenSlot problem + 1⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [followingTokenSlot_direct_eq_padding_or_t]

theorem finalOutside_contains_finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  let polynomial := successorTokenSlotPolynomial problem.verifier
  let scratch :=
    BuilderUnaryPolynomial.scratchWord polynomial problem.input.length
  rcases BuilderUnaryPolynomial.scratchWord_eq_root polynomial
      problem.input.length with ⟨wordPrefix, hScratch⟩
  have hScratch' :
      scratch =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (successorTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol := by
    simpa [scratch, polynomial, successorTokenSlot] using hScratch
  refine ⟨wordPrefix,
    (controllerFinalOutside problem).drop (scratch.length + 1), ?_⟩
  unfold finalOutside BuilderUnaryPolynomial.finalOutsideLeft
    BuilderUnaryPolynomial.overlayScratch
  change scratch ++ BuilderUnaryPolynomial.scratchEndSymbol ::
      (controllerFinalOutside problem).drop (scratch.length + 1) = _
  rw [hScratch']
  simp only [finalTokenSlot]

theorem finalConfiguration_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (finalConfiguration problem).state = (machine problem).acceptState := rfl

private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
  unfold WorkMachine.isHalted
  rw [finalConfiguration_state, (nat_beq_true_iff _ _).mpr rfl]
  rfl

/-! ### External compiled-time polynomial -/

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let widthPolynomial := formulaTapeWidthPolynomial verifier
  let targetPolynomial := successorTokenSlotPolynomial verifier
  .add
    (BuilderSecondConstraintFirstLiteralTerminatorStep.rawTimeBound verifier)
    (.add (.constant 600)
      (.add (scalePolynomial 24 .variable)
        (.add (scalePolynomial 12 (formulaWidthPolynomial verifier))
          (.add (scalePolynomial 12 widthPolynomial)
            (.add
              (scalePolynomial 12
                (BuilderUnaryPolynomial.rootPrefixPolynomial widthPolynomial))
              (.add
                (scalePolynomial 6
                  (BuilderUnaryPolynomial.workTimePolynomial
                    widthPolynomial))
                (scalePolynomial 6
                  (BuilderUnaryPolynomial.workTimePolynomial
                    targetPolynomial))))))))

private theorem predecessorTokens_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens
      problem).length = problem.FormulaWidth + 42 := by
  rw [BuilderSecondConstraintFirstLiteralTerminatorStep.secondConstraintFirstLiteralTerminatorTokens,
    List.length_append]
  have hPrevious :
      (BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.secondConstraintFirstLiteralThirdUnaryTokens
        problem).length = problem.FormulaWidth + 41 := by
    simp [BuilderSecondConstraintFirstLiteralThirdUnaryUnitStep.secondConstraintFirstLiteralThirdUnaryTokens,
      BuilderSecondConstraintFirstLiteralSecondUnaryUnitStep.secondConstraintFirstLiteralSecondUnaryTokens,
      BuilderSecondConstraintFirstLiteralFirstUnaryUnitStep.secondConstraintFirstLiteralFirstUnaryTokens,
      BuilderSecondConstraintFirstLiteralSignStep.secondConstraintFirstLiteralSignTokens,
      BuilderSecondConstraintSeparatorStep.secondConstraintStartTokens,
      BuilderFourthClausePrefix.fourthClauseTokens,
      BuilderFourthClauseSecondLiteralPrefix.fourthClauseSecondLiteralTokens,
      BuilderFourthClauseSecondLiteralPrefix.secondUnaryTokenOutput,
      BuilderFourthClauseSecondLiteralPrefix.firstUnaryTokenOutput,
      BuilderFourthClauseSecondLiteralPrefix.signTokenOutput,
      BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens,
      BuilderFourthClauseFirstLiteralPrefix.unaryTokenOutput,
      BuilderFourthClauseFirstLiteralPrefix.signTokenOutput,
      BuilderFourthClauseSeparatorStep.fourthClauseStartTokens,
      BuilderThirdClausePrefix.thirdClauseTokens,
      BuilderThirdClauseSecondLiteralPrefix.thirdClauseSecondLiteralTokens,
      BuilderThirdClauseSecondLiteralPrefix.secondUnaryTokenOutput,
      BuilderThirdClauseSecondLiteralPrefix.firstUnaryTokenOutput,
      BuilderThirdClauseSecondLiteralPrefix.signTokenOutput,
      BuilderThirdClauseFirstLiteralPrefix.thirdClauseFirstLiteralTokens,
      BuilderThirdClauseFirstLiteralPrefix.firstTokenOutput,
      BuilderThirdClauseSeparatorStep.thirdClauseStartTokens,
      BuilderSecondClausePrefix.secondClauseTokens,
      BuilderSecondClauseSecondLiteralPrefix.secondClauseSecondLiteralTokens,
      BuilderSecondClauseSecondLiteralPrefix.unaryTokenOutput,
      BuilderSecondClauseSecondLiteralPrefix.signTokenOutput,
      BuilderSecondClauseFirstLiteralPrefix.secondClauseFirstLiteralTokens,
      BuilderSecondClauseFirstLiteralPrefix.firstTokenOutput,
      BuilderSecondClauseSeparatorStep.secondClauseStartTokens,
      BuilderFirstClausePrefix.firstClauseTokens_eq_canonical_prefix,
      encodeUnaryTokens_length]
  rw [hPrevious]
  simp

/-- The emitted work-tape bits are exactly the canonical formula prefix
through the width-selected successor token. -/
theorem finalTokenBits_eq_encodedFormula_secondConstraintFirstLiteralSuccessor
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (secondConstraintFirstLiteralSuccessorTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 43)) := by
  rcases
      secondConstraintFirstLiteralSuccessorTokens_eq_canonical_formula_prefix
        problem with
    ⟨rest, hTokens⟩
  have hLength :
      (encodeTokenPairs
        (secondConstraintFirstLiteralSuccessorTokens problem)).length =
        2 * (problem.FormulaWidth + 43) := by
    rw [encodeTokenPairs_length,
      secondConstraintFirstLiteralSuccessorTokens, List.length_append,
      predecessorTokens_length]
    simp
  let suffix := encodeTokenPairs rest ++ [false]
  have hShape : problem.encodedFormula =
      encodeTokenPairs (secondConstraintFirstLiteralSuccessorTokens problem) ++
        suffix := by
    simp only [VerifierTableauProblem.encodedFormula, encodeCNF]
    rw [hTokens, encodeTokenPairs_append_local]
    simp [suffix, List.append_assoc]
  rw [hShape, ← hLength]
  exact List.take_left.symm

private theorem appenderWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    appenderWorkSteps problem ≤
      4 * problem.input.length + 2 * problem.FormulaWidth + 92 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  unfold appenderWorkSteps BuilderTokenAppender.workSteps
    BuilderTokenAppender.halfSteps
  rw [predecessorTokens_length]
  omega

private theorem controllerWorkSteps_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    controllerWorkSteps problem =
      2 * widthRootPrefixLength problem + 2 * width problem + 4 := by
  have hWidth := width_positive problem
  have hRoot :
      0 < widthRootPrefixLength problem := by
    rcases BuilderUnaryPolynomial.root_register_length
      (widthPolynomial problem) problem.input.length with
      ⟨wordPrefix, _hScratch, hLength⟩
    unfold widthRootPrefixLength
    rw [← hLength]
    omega
  unfold controllerWorkSteps
    BuilderCompleteHeader.HeaderController.steps
    widthControllerPrefixLength
  omega

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderSecondConstraintFirstLiteralTerminatorStep.rawTimeBound
        problem.verifier).eval problem.input.length +
      600 + 24 * problem.input.length + 12 * problem.FormulaWidth +
      12 * width problem + 12 * widthRootPrefixLength problem +
      6 * widthWorkSteps problem + 6 * targetWorkSteps problem := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, NatPolynomial.eval_variable, scalePolynomial,
    BuilderUnaryPolynomial.workTimePolynomial_eval]
  have hFormulaWidth :
      (formulaWidthPolynomial problem.verifier).eval problem.input.length =
        problem.FormulaWidth := by
    simpa [BitString.size] using problem.formulaWidthPolynomial_eval
  rw [hFormulaWidth]
  unfold width widthPolynomial widthRootPrefixLength widthWorkSteps
    targetWorkSteps
  simp only
    [BuilderSecondConstraintFirstLiteralSuccessorTokenStep.widthPolynomial]
  omega

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix :=
    BuilderSecondConstraintFirstLiteralTerminatorStep.rawTimeBound_le problem
  have hAppender := appenderWorkSteps_le problem
  rw [rawTimeBound_eval]
  unfold workSteps branchWorkSteps
  rw [controllerWorkSteps_eq]
  omega

/-! ### Compiled execution -/

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem)) (6 * workSteps problem)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    (machine problem) (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)

theorem run_compile_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    (machine problem) (workSteps problem)
    ((rawTimeBound problem.verifier).eval problem.input.length)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)
    (finalConfiguration_isHalted problem) (rawTimeBound_le problem)

theorem run_compile_rawTimeBound_blankEquivalent {language : Language}
    (problem : VerifierTableauProblem language) :
    Configuration.BlankEquivalent
      (run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (startConfig (compileWorkMachine (machine problem)) problem.input))
      (encodeWorkConfiguration (finalConfiguration problem)) := by
  have hStart := startConfig_compileWorkMachine_blankEquivalent
    (machine problem) problem.input
  have hRun := run_blankEquivalent (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length) hStart
  rw [run_compile_rawTimeBound problem] at hRun
  exact hRun

private theorem blankEquivalent_state {first second : Configuration}
    (hEquivalent : Configuration.BlankEquivalent first second) :
    first.state = second.state :=
  hEquivalent.1

private theorem blankEquivalent_accept_of_encoded
    (localMachine : WorkMachine) (first : Configuration)
    (final : WorkConfiguration)
    (hEquivalent : Configuration.BlankEquivalent first
      (encodeWorkConfiguration final))
    (hFinal : final.state = localMachine.acceptState) :
    first.state = (compileWorkMachine localMachine).acceptState := by
  have hState := blankEquivalent_state hEquivalent
  have hEncoded := (encodeWorkConfiguration_accept_iff
    localMachine final).mpr hFinal
  exact hState.trans hEncoded

set_option maxRecDepth 100000 in
theorem boundedDecide_compile_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input = .accept := by
  apply (boundedDecide_accept_iff_final
    (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length)
    problem.input).mpr
  exact blankEquivalent_accept_of_encoded (machine problem) _
    (finalConfiguration problem)
    (run_compile_rawTimeBound_blankEquivalent problem)
    (finalConfiguration_state problem)

theorem boundedDecide_compile_ne_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input ≠ .timeout := by
  rw [boundedDecide_compile_accept]
  intro impossible
  contradiction

theorem workBoundedDecide_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem)
      (rawInputWorkTape problem.input) = .accept := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem) (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)]
  dsimp only
  rw [finalConfiguration_state]
  rw [(nat_beq_true_iff _ _).mpr rfl]
  rfl

/-! ### Fail-closed trace boundary -/

private theorem verdict_timeout_of_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hHalted : (machine problem).isHalted config = false) :
    (if config.state == (machine problem).acceptState then WorkVerdict.accept
     else if config.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  unfold WorkMachine.isHalted at hHalted
  cases hAccept : (config.state == (machine problem).acceptState) with
  | true =>
      rw [hAccept] at hHalted
      contradiction
  | false =>
      cases hReject : (config.state == (machine problem).rejectState) with
      | true =>
          rw [hAccept, hReject] at hHalted
          contradiction
      | false => rfl

private theorem machine_isHalted_predecessor_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          config) = false := by
  have hHalted :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
      (suffixMachine problem) config
  simpa [machine] using hHalted

/-- The complete predecessor endpoint is still globally nonhalting until the
outer bridge launches the width-dependent successor suffix. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    (let initial := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (workStartConfiguration
          (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
          (rawInputWorkTape problem.input))
     let result := workRun (machine problem)
       (BuilderSecondConstraintFirstLiteralTerminatorStep.workSteps problem)
       initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = .timeout := by
  dsimp only
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderSecondConstraintFirstLiteralTerminatorStep.workSteps problem)
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (workStartConfiguration
        (BuilderSecondConstraintFirstLiteralTerminatorStep.machine problem)
        (rawInputWorkTape problem.input)))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (BuilderSecondConstraintFirstLiteralTerminatorStep.finalConfiguration
        problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_predecessor_false problem
      (BuilderSecondConstraintFirstLiteralTerminatorStep.finalConfiguration
        problem))

private theorem workRunExact_succ_split_last {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? (machine problem) (steps + 1) initial = some final →
      ∃ before,
        workRunExact? (machine problem) steps initial = some before ∧
        workStep? (machine problem) before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next =>
                 workRunExact? (machine problem) (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? (machine problem) (steps + 1) next =
              some final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result =>
                   workRunExact? (machine problem) (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some result =>
                 workRunExact? (machine problem) steps result) = some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? (machine problem) config = some next) :
    (machine problem).isHalted config = false := by
  cases hHalted : (machine problem).isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) : 0 < workSteps problem := by
  unfold workSteps
  omega

/-- Removing the final successful target-evaluator transition leaves a
nonhalting state, so the exact composed trace cannot accept one work step
early. -/
theorem work_one_step_short_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem - 1)
        (rawInputWorkTape problem.input) = .timeout := by
  let short := workSteps problem - 1
  let initial := workStartConfiguration (machine problem)
    (rawInputWorkTape problem.input)
  let final := finalConfiguration problem
  have hSucc : short + 1 = workSteps problem := by
    dsimp [short]
    have hPositive := workSteps_positive problem
    omega
  have hExact := workRunExact problem
  change workRunExact? (machine problem) (workSteps problem) initial =
    some final at hExact
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last problem short initial final hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun (machine problem) short initial = before :=
    workRun_eq_of_workRunExact (machine problem) short initial before hPrefix
  have hNotHalted := isHalted_false_of_workStep_some
    problem before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun (machine problem) short initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  exact verdict_timeout_of_not_halted problem before hNotHalted

end BuilderSecondConstraintFirstLiteralSuccessorTokenStep

end CookLevin

end PNP.Concrete
