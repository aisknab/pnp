/-
Copyright (c) 2026 PNP Labs.

Input-dependent traversal of the remaining padding rectangle after the first
canonical Cook--Levin clause.

The predecessor has already consumed the first padding opportunity and
retains token coordinate `V + 13`.  This module evaluates the exact remaining
padding count `(V - 1) * (V + 6)`, consumes that unary counter with one literal
loop, and then materializes the first coordinate of the second clause.  No
formula token is emitted by this milestone.
-/

import PNP.Concrete.CookLevinBuilderDynamicTokenCursorStep

namespace PNP.Concrete

namespace CookLevin

namespace BuilderFirstClausePaddingRun

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Exact external coordinates -/

/-- The formula-variable bound with its final, syntactically explicit unit
removed.  This remains a natural polynomial and evaluates to `V - 1`. -/
def formulaVariablePredecessorPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let time := formulaTimeCountPolynomial verifier
  let tape := formulaTapeWidthPolynomial verifier
  let states := formulaStateCountPolynomial verifier
  let certificate := verifier.certificateBound
  .add
    (.add
      (.add
        (.add
          (.mul (.mul (.constant 3) time) tape)
          (.mul time tape))
        (.mul time states))
      certificate)
    certificate

theorem formulaVariablePredecessorPolynomial_eval_add_one
    {language : Language} (problem : VerifierTableauProblem language) :
    (formulaVariablePredecessorPolynomial problem.verifier).eval
        problem.input.length + 1 = problem.formulaVariableSlotBound := by
  unfold formulaVariablePredecessorPolynomial
    VerifierTableauProblem.formulaVariableSlotBound
    formulaVariableCountPolynomial BitString.size
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant]
  omega

theorem formulaVariableSlotBound_at_least_three {language : Language}
    (problem : VerifierTableauProblem language) :
    3 ≤ problem.formulaVariableSlotBound := by
  have hTime : 1 ≤ problem.dimensions.timeCount :=
    Nat.succ_le_iff.mpr problem.dimensions.timeCount_positive
  have hTape : 1 ≤
      problem.dimensions.tapeWidth problem.tableauInputMode :=
    Nat.succ_le_iff.mpr
      (problem.dimensions.tapeWidth_positive problem.tableauInputMode)
  have hThreeTime : 3 ≤ 3 * problem.dimensions.timeCount := by
    have h := Nat.mul_le_mul_left 3 hTime
    simpa using h
  have hSymbol : 3 ≤
      (3 * problem.dimensions.timeCount) *
        problem.dimensions.tapeWidth problem.tableauInputMode := by
    have hGrow := Nat.mul_le_mul_left
      (3 * problem.dimensions.timeCount) hTape
    have hBase : 3 * problem.dimensions.timeCount ≤
        (3 * problem.dimensions.timeCount) *
          problem.dimensions.tapeWidth problem.tableauInputMode := by
      simpa using hGrow
    exact Nat.le_trans hThreeTime hBase
  unfold VerifierTableauProblem.formulaVariableSlotBound
  rw [problem.formulaVariableCountPolynomial_eval]
  omega

theorem formulaVariablePredecessorPolynomial_eval
    {language : Language} (problem : VerifierTableauProblem language) :
    (formulaVariablePredecessorPolynomial problem.verifier).eval
        problem.input.length = problem.formulaVariableSlotBound - 1 := by
  have hRelation := formulaVariablePredecessorPolynomial_eval_add_one problem
  omega

/-- Number of padding opportunities strictly after `V + 12` and before the
second clause rectangle. -/
def remainingPaddingPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (formulaVariablePredecessorPolynomial verifier)
    (.add (formulaVariableCountPolynomial verifier) (.constant 6))

def remainingPaddingCount {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (remainingPaddingPolynomial problem.verifier).eval problem.input.length

theorem remainingPaddingCount_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    remainingPaddingCount problem =
      (problem.formulaVariableSlotBound - 1) *
        (problem.formulaVariableSlotBound + 6) := by
  unfold remainingPaddingCount remainingPaddingPolynomial
  simp only [NatPolynomial.eval_mul, NatPolynomial.eval_add,
    NatPolynomial.eval_constant]
  rw [formulaVariablePredecessorPolynomial_eval problem]
  unfold VerifierTableauProblem.formulaVariableSlotBound
  rfl

theorem remainingPaddingCount_eq_formulaTokensPerClause_sub_twelve
    {language : Language} (problem : VerifierTableauProblem language) :
    remainingPaddingCount problem = problem.formulaTokensPerClause - 12 := by
  rw [remainingPaddingCount_eq]
  have hBound := formulaVariableSlotBound_at_least_three problem
  let predecessor := problem.formulaVariableSlotBound - 1
  have hVariable : problem.formulaVariableSlotBound = predecessor + 1 := by
    unfold predecessor
    omega
  unfold VerifierTableauProblem.formulaTokensPerClause
  rw [hVariable]
  simp only [Nat.add_assoc]
  simp [Nat.add_mul, Nat.mul_add]
  omega

theorem remainingPaddingCount_positive {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < remainingPaddingCount problem := by
  rw [remainingPaddingCount_eq]
  have hBound := formulaVariableSlotBound_at_least_three problem
  exact Nat.mul_pos (by omega) (by omega)

/-- Absolute token coordinate of the first opportunity in the second clause
rectangle. -/
def secondClauseStartPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (formulaVariableCountPolynomial verifier) (.constant 1))
    (formulaClauseTokenPolynomial verifier)

def secondClauseStart {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (secondClauseStartPolynomial problem.verifier).eval problem.input.length

theorem secondClauseStart_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    secondClauseStart problem =
      problem.formulaVariableSlotBound + 1 +
        problem.formulaTokensPerClause := by
  unfold secondClauseStart secondClauseStartPolynomial
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant]
  change
    (formulaVariableCountPolynomial problem.verifier).eval
          (BitString.size problem.input) + 1 +
        (formulaClauseTokenPolynomial problem.verifier).eval
          (BitString.size problem.input) = _
  rw [problem.formulaClauseTokenPolynomial_eval]
  unfold VerifierTableauProblem.formulaVariableSlotBound
    VerifierTableauProblem.formulaTokensPerClause
  rfl

theorem predecessorSlot_add_remainingPaddingCount
    {language : Language} (problem : VerifierTableauProblem language) :
    BuilderDynamicTokenCursorStep.finalTokenSlot problem +
        remainingPaddingCount problem = secondClauseStart problem := by
  rw [BuilderDynamicTokenCursorStep.finalTokenSlot_eq_formulaVariableSlotBound_add_thirteen,
    remainingPaddingCount_eq_formulaTokensPerClause_sub_twelve,
    secondClauseStart_eq]
  have hWidth : 12 ≤ problem.formulaTokensPerClause := by
    have hBound := formulaVariableSlotBound_at_least_three problem
    unfold VerifierTableauProblem.formulaTokensPerClause
    have hProduct : 10 ≤
        (problem.formulaVariableSlotBound + 4) *
          (problem.formulaVariableSlotBound + 1) := by
      exact Nat.le_trans (by decide : 10 ≤ 7 * 4)
        (Nat.mul_le_mul (by omega) (by omega))
    omega
  omega

/-! ### Literal unary countdown loop -/

namespace PaddingCountdown

def loopbackRules : List WorkRule :=
  launchRules BuilderCompleteHeader.HeaderController.moreExitState
    BuilderCompleteHeader.HeaderController.startState

def rules : List WorkRule :=
  BuilderCompleteHeader.HeaderController.rules ++ loopbackRules

/-- The former `done` exit is the only successful halt.  The `more` exit is
total over all work symbols and loops back to the controller start. -/
def machine : WorkMachine :=
  { rules := rules
    startState := BuilderCompleteHeader.HeaderController.startState
    acceptState := BuilderCompleteHeader.HeaderController.doneExitState
    rejectState := BuilderCompleteHeader.HeaderController.rejectState }

theorem rules_length : rules.length = 25 := by rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by decide

theorem rule_source_ne_acceptState (rule : WorkRule)
    (hRule : rule ∈ machine.rules) :
    rule.sourceState ≠ machine.acceptState := by
  simp only [machine, rules, loopbackRules, List.mem_append] at hRule
  rcases hRule with hController | hLoopback
  · have hSources : rule.sourceState ≤
        BuilderCompleteHeader.HeaderController.doneRewindState := by
      simp [BuilderCompleteHeader.HeaderController.rules] at hController
      rcases hController with h | h | h | h | h | h | h | h | h | h | h |
          h | h | h | h | h <;> subst rule <;> decide
    change rule.sourceState ≤ 6 at hSources
    change rule.sourceState ≠ 8
    omega
  · rcases List.mem_map.mp hLoopback with ⟨symbol, _hSymbol, hRule⟩
    subst rule
    simp [launchRule, machine,
      BuilderCompleteHeader.HeaderController.moreExitState,
      BuilderCompleteHeader.HeaderController.doneExitState]

/-- Exact loop cost for a positive unary root. -/
def loopSteps (prefixLength : Nat) : Nat → Nat
  | 0 => 0
  | 1 => BuilderCompleteHeader.HeaderController.steps prefixLength 0
  | remaining + 2 =>
      BuilderCompleteHeader.HeaderController.steps prefixLength
          (remaining + 1) + 1 +
        loopSteps prefixLength (remaining + 1)

def initialConfiguration (input : BitString)
    (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) (output : List CNFToken) :
    WorkConfiguration :=
  BuilderCompleteHeader.HeaderController.initialConfiguration input wordPrefix
    remaining tail output

def finalOutside (wordPrefix : List WorkSymbol) (count : Nat)
    (tail : List WorkSymbol) : List WorkSymbol :=
  wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
    List.replicate (count + 1)
      BuilderUnaryPolynomial.scratchEndSymbol ++ tail

def finalConfiguration (input : BitString)
    (wordPrefix : List WorkSymbol) (count : Nat)
    (tail : List WorkSymbol) (output : List CNFToken) : WorkConfiguration :=
  { state := machine.acceptState
    tape := BuilderTokenAppender.workspaceTape input
      (finalOutside wordPrefix count tail) output }

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
        have hEqual : first = selected := Option.some.inj (hHead.symm.trans hFind)
        subst selected
        exact List.Mem.head rest
      · have hTail := findWorkRule_cons_of_not_matches first rest state symbol
          hMatches
        exact List.Mem.tail first (ih (hTail.symm.trans hFind))

private theorem controller_rule_source_lt_done
    (rule : WorkRule)
    (hRule : rule ∈ BuilderCompleteHeader.HeaderController.rules) :
    rule.sourceState < BuilderCompleteHeader.HeaderController.doneExitState := by
  simp [BuilderCompleteHeader.HeaderController.rules] at hRule
  rcases hRule with h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h <;> subst rule <;> decide

private theorem nat_beq_false_of_ne (left right : Nat)
    (h : left ≠ right) : (left == right) = false := by
  cases hBool : (left == right) with
  | false => rfl
  | true =>
      exact False.elim (h ((nat_beq_true_iff left right).mp hBool))

private theorem controller_workStep_of_some
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderCompleteHeader.HeaderController.machine config =
      some next) :
    workStep? machine config = some next := by
  rcases workStep?_some_exists
      BuilderCompleteHeader.HeaderController.machine config next hStep with
    ⟨rule, _hLocalHalted, hFind, hNext⟩
  have hMem := findWorkRule_some_mem hFind
  have hSource := controller_rule_source_lt_done rule hMem
  have hMatches := findWorkRule_some_matches hFind
  have hStateLt : config.state <
      BuilderCompleteHeader.HeaderController.doneExitState := by
    rw [← hMatches.1]
    exact hSource
  have hStateLtEight : config.state < 8 := by
    simpa [BuilderCompleteHeader.HeaderController.doneExitState] using hStateLt
  have hStateDone : config.state ≠ machine.acceptState := by
    change config.state ≠ 8
    omega
  have hStateReject : config.state ≠ machine.rejectState := by
    change config.state ≠ 9
    omega
  have hGlobalHalted : machine.isHalted config = false := by
    unfold WorkMachine.isHalted
    rw [nat_beq_false_of_ne _ _ hStateDone,
      nat_beq_false_of_ne _ _ hStateReject]
    rfl
  have hGlobalFind : findWorkRule machine.rules config.state config.tape.head =
      some rule := by
    unfold machine rules
    exact findWorkRule_append_of_some _ _ _ _ _ hFind
  have hGlobalStep := workStep?_eq_apply_of_find machine config rule
    hGlobalHalted hGlobalFind
  rw [hGlobalStep]
  exact congrArg Option.some hNext.symm

theorem loopback_workStep (tape : WorkTape) :
    workStep? machine
        { state := BuilderCompleteHeader.HeaderController.moreExitState,
          tape := tape } =
      some
        { state := BuilderCompleteHeader.HeaderController.startState,
          tape := tape } := by
  have hHalted : machine.isHalted
      { state := BuilderCompleteHeader.HeaderController.moreExitState,
        tape := tape } = false := by
    rfl
  have hController : findWorkRule
      BuilderCompleteHeader.HeaderController.rules
      BuilderCompleteHeader.HeaderController.moreExitState tape.head = none := by
    rfl
  have hLaunch := findWorkRule_launchRules
    BuilderCompleteHeader.HeaderController.moreExitState
    BuilderCompleteHeader.HeaderController.startState tape.head
  have hFind : findWorkRule machine.rules
      BuilderCompleteHeader.HeaderController.moreExitState tape.head =
        some (launchRule
          BuilderCompleteHeader.HeaderController.moreExitState
          BuilderCompleteHeader.HeaderController.startState tape.head) := by
    unfold machine rules loopbackRules
    rw [findWorkRule_append_of_none _ _ _ _ hController]
    exact hLaunch
  have hStep := workStep?_eq_apply_of_find machine
    { state := BuilderCompleteHeader.HeaderController.moreExitState,
      tape := tape }
    (launchRule BuilderCompleteHeader.HeaderController.moreExitState
      BuilderCompleteHeader.HeaderController.startState tape.head)
    hHalted hFind
  have hStay : tape.move .stay = tape := by
    cases tape
    rfl
  simpa [launchRule, applyWorkRule, hStay] using hStep

private theorem controller_workRunExact (steps : Nat)
    (start final : WorkConfiguration)
    (hRun : workRunExact? BuilderCompleteHeader.HeaderController.machine
      steps start = some final) :
    workRunExact? machine steps start = some final := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    BuilderCompleteHeader.HeaderController.machine machine id
    (fun config next hStep => controller_workStep_of_some config next hStep)
    steps start final hRun
  simpa [renameConfiguration] using hTransport

private theorem workRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem replicate_succ_append {alpha : Type}
    (count : Nat) (item : alpha) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change item :: List.replicate (count + 1) item =
        (item :: List.replicate count item) ++ [item]
      rw [ih]
      simp only [List.cons_append]

/-- The literal 25-rule table consumes every unit in one positive root
register, looping once per remaining padding opportunity and preserving the
represented input and formula output exactly. -/
theorem loop_workRunExact (input : BitString)
    (wordPrefix : List WorkSymbol) (remaining : Nat)
    (tail : List WorkSymbol) (output : List CNFToken)
    (hPrefix : ∀ symbol ∈ wordPrefix,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol) :
    workRunExact? machine (loopSteps wordPrefix.length (remaining + 1))
        (initialConfiguration input wordPrefix remaining tail output) =
      some (finalConfiguration input wordPrefix (remaining + 1) tail output) := by
  induction remaining generalizing tail with
  | zero =>
      have hLocal :=
        BuilderCompleteHeader.HeaderController.workRunExact_of_unit_or_separator
          input wordPrefix 0 tail output hPrefix
      have hGlobal := controller_workRunExact
        (BuilderCompleteHeader.HeaderController.steps wordPrefix.length 0)
        (BuilderCompleteHeader.HeaderController.initialConfiguration input
          wordPrefix 0 tail output)
        (BuilderCompleteHeader.HeaderController.finalConfiguration input
          wordPrefix 0 tail output) hLocal
      simpa [loopSteps, initialConfiguration, finalConfiguration, finalOutside,
        BuilderCompleteHeader.HeaderController.finalConfiguration,
        BuilderCompleteHeader.HeaderController.outsideAfter,
        machine] using hGlobal
  | succ rest ih =>
      let nextTail := BuilderUnaryPolynomial.scratchEndSymbol :: tail
      let c0 := initialConfiguration input wordPrefix (rest + 1) tail output
      let cMore := BuilderCompleteHeader.HeaderController.finalConfiguration
        input wordPrefix (rest + 1) tail output
      let cNext := initialConfiguration input wordPrefix rest nextTail output
      let final := finalConfiguration input wordPrefix (rest + 2) tail output
      have hLocal :=
        BuilderCompleteHeader.HeaderController.workRunExact_of_unit_or_separator
          input wordPrefix (rest + 1) tail output hPrefix
      have hController : workRunExact? machine
          (BuilderCompleteHeader.HeaderController.steps wordPrefix.length
            (rest + 1)) c0 = some cMore := by
        simpa [c0, cMore, initialConfiguration] using
          controller_workRunExact
            (BuilderCompleteHeader.HeaderController.steps wordPrefix.length
              (rest + 1))
            (BuilderCompleteHeader.HeaderController.initialConfiguration input
              wordPrefix (rest + 1) tail output)
            (BuilderCompleteHeader.HeaderController.finalConfiguration input
              wordPrefix (rest + 1) tail output) hLocal
      have hBackStep := loopback_workStep cMore.tape
      have hBack : workRunExact? machine 1 cMore = some cNext := by
        apply workRunExact_one
        simpa [cMore, cNext, nextTail, initialConfiguration,
          BuilderCompleteHeader.HeaderController.finalConfiguration,
          BuilderCompleteHeader.HeaderController.initialConfiguration,
          BuilderCompleteHeader.HeaderController.outsideAfter,
          BuilderCompleteHeader.HeaderController.outsideBefore,
          replicate_succ_append, List.append_assoc] using hBackStep
      have hTail := ih nextTail
      have hTailExact : workRunExact? machine
          (loopSteps wordPrefix.length (rest + 1)) cNext = some final := by
        have hEnds := replicate_succ_append (rest + 2)
          BuilderUnaryPolynomial.scratchEndSymbol
        simpa [cNext, final, nextTail, finalConfiguration, finalOutside,
          hEnds, List.replicate_succ, List.append_assoc] using hTail
      have hCombined := PipelineMachineSimulation.workRunExact?_compose machine
        (BuilderCompleteHeader.HeaderController.steps wordPrefix.length
          (rest + 1)) 1 c0 cMore cNext hController hBack
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (BuilderCompleteHeader.HeaderController.steps wordPrefix.length
          (rest + 1) + 1)
        (loopSteps wordPrefix.length (rest + 1))
        c0 cNext final hCombined hTailExact
      simpa [loopSteps, c0, final, Nat.add_assoc] using hAll

theorem loopSteps_le (prefixLength count : Nat) :
    loopSteps prefixLength count ≤
      count * (2 * (prefixLength + 1) + 8) + count * count := by
  induction count with
  | zero => simp [loopSteps]
  | succ count ih =>
      cases count with
      | zero =>
          simp [loopSteps, BuilderCompleteHeader.HeaderController.steps]
          omega
      | succ rest =>
          rw [loopSteps]
          have hTail := ih
          unfold BuilderCompleteHeader.HeaderController.steps
          simp [Nat.add_mul, Nat.mul_add] at hTail ⊢
          omega

end PaddingCountdown

/-! ### Evaluator-loop-evaluator composition -/

def countEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (remainingPaddingPolynomial problem.verifier)

def targetEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (secondClauseStartPolynomial problem.verifier)

def countdownTargetMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine PaddingCountdown.machine
    (targetEvaluator problem)

def paddingSuffixMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine (countEvaluator problem)
    (countdownTargetMachine problem)

/-- One literal finite rule table from raw input through the complete first
clause and across its entire remaining padding block. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderDynamicTokenCursorStep.machine problem)
    (paddingSuffixMachine problem)

private theorem predecessor_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderDynamicTokenCursorStep.machine problem) := by
  exact BuilderDynamicTokenCursorStep.rule_source_ne_acceptState problem

private theorem countEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (countEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt (BuilderUnaryPolynomial.rule_source_lt_acceptState
    (remainingPaddingPolynomial problem.verifier) rule hRule)

private theorem countdown_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      PaddingCountdown.machine := by
  exact PaddingCountdown.rule_source_ne_acceptState

private theorem targetEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (targetEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt (BuilderUnaryPolynomial.rule_source_lt_acceptState
    (secondClauseStartPolynomial problem.verifier) rule hRule)

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      1244 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstLiteralPrefix.nextTokenSlotPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstClausePrefix.nextTokenSlotPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (remainingPaddingPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (secondClauseStartPolynomial problem.verifier) := by
  have hPredecessor := BuilderDynamicTokenCursorStep.rules_length problem
  have hCount := BuilderUnaryPolynomial.rules_length
    (remainingPaddingPolynomial problem.verifier)
  have hTarget := BuilderUnaryPolynomial.rules_length
    (secondClauseStartPolynomial problem.verifier)
  have hCountdown := PaddingCountdown.rules_length
  have hCountMachine :
      (BuilderUnaryPolynomial.machine
        (remainingPaddingPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (remainingPaddingPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hCount
  have hTargetMachine :
      (BuilderUnaryPolynomial.machine
        (secondClauseStartPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (secondClauseStartPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hTarget
  have hCountdownMachine : PaddingCountdown.machine.rules.length = 25 := by
    simpa [PaddingCountdown.machine] using hCountdown
  have hLaunch : ∀ source target,
      (launchRules source target).length = 9 := by
    intro source target
    rfl
  unfold machine paddingSuffixMachine countdownTargetMachine countEvaluator
    targetEvaluator BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
    BuilderFirstClausePrefix.WorkChain.bridgeRules
  simp only [List.length_append, List.length_map]
  rw [hPredecessor, hCountMachine, hTargetMachine, hCountdownMachine,
    hLaunch, hLaunch, hLaunch]
  omega

theorem rules_pairwise_query_distinct {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  have hCountdownTarget :=
    BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    PaddingCountdown.machine (targetEvaluator problem)
    PaddingCountdown.rules_pairwise_query_distinct
    (BuilderUnaryPolynomial.rules_pairwise_query_distinct
      (secondClauseStartPolynomial problem.verifier))
    countdown_noRuleAtAccept
  have hSuffix := BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (countEvaluator problem) (countdownTargetMachine problem)
    (BuilderUnaryPolynomial.rules_pairwise_query_distinct
      (remainingPaddingPolynomial problem.verifier))
    hCountdownTarget (countEvaluator_noRuleAtAccept problem)
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (BuilderDynamicTokenCursorStep.machine problem)
    (paddingSuffixMachine problem)
    (BuilderDynamicTokenCursorStep.rules_pairwise_query_distinct problem)
    hSuffix (predecessor_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderDynamicTokenCursorStep.machine problem)
    (paddingSuffixMachine problem)
    (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
      (countEvaluator problem) (countdownTargetMachine problem)
      (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
        PaddingCountdown.machine (targetEvaluator problem)
        (BuilderUnaryPolynomial.machine_acceptState_ne_rejectState
          (secondClauseStartPolynomial problem.verifier))))

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderDynamicTokenCursorStep.machine problem)
    (paddingSuffixMachine problem)
    (BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
      (countEvaluator problem) (countdownTargetMachine problem)
      (BuilderFirstClausePrefix.WorkChain.noRuleAtAccept PaddingCountdown.machine
        (targetEvaluator problem) (targetEvaluator_noRuleAtAccept problem)))
    rule hRule

/-! ### Exact endpoint geometry -/

def countWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.scratchWord
    (remainingPaddingPolynomial problem.verifier) problem.input.length

def countRootPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (BuilderUnaryPolynomial.rootPrefixPolynomial
    (remainingPaddingPolynomial problem.verifier)).eval problem.input.length

def countControllerPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  countRootPrefixLength problem - 1

def countOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (remainingPaddingPolynomial problem.verifier) problem.input
    (BuilderDynamicTokenCursorStep.finalOutside problem)

def countTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (countOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)

def countdownFinalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (countWord problem).take (countRootPrefixLength problem) ++
    List.replicate (remainingPaddingCount problem + 1)
      BuilderUnaryPolynomial.scratchEndSymbol ++
    (BuilderDynamicTokenCursorStep.finalOutside problem).drop
      ((countWord problem).length + 1)

def countdownFinalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (countdownFinalOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (secondClauseStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def countdownWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  PaddingCountdown.loopSteps (countControllerPrefixLength problem)
    (remainingPaddingCount problem)

def suffixWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderUnaryPolynomial.workSteps
      (remainingPaddingPolynomial problem.verifier) problem.input + 1 +
    countdownWorkSteps problem + 1 +
    BuilderUnaryPolynomial.workSteps
      (secondClauseStartPolynomial problem.verifier) problem.input

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderDynamicTokenCursorStep.workSteps problem + 1 +
    suffixWorkSteps problem

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (BuilderFirstClausePrefix.firstClauseTokens problem)

theorem countEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (countEvaluator problem)
        (BuilderUnaryPolynomial.workSteps
          (remainingPaddingPolynomial problem.verifier) problem.input)
        (BuilderUnaryPolynomial.initialConfiguration
          (remainingPaddingPolynomial problem.verifier) problem.input
          (BuilderDynamicTokenCursorStep.finalOutside problem)
          (BuilderFirstClausePrefix.firstClauseTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (remainingPaddingPolynomial problem.verifier) problem.input
          (BuilderDynamicTokenCursorStep.finalOutside problem)
          (BuilderFirstClausePrefix.firstClauseTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (remainingPaddingPolynomial problem.verifier) problem.input
    (BuilderDynamicTokenCursorStep.finalOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)

private theorem take_prefix_separator
    (wordPrefix suffix : List WorkSymbol) :
    (wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol :: suffix).take
        (wordPrefix.length + 1) =
      wordPrefix ++ [BuilderUnaryPolynomial.separatorSymbol] := by
  induction wordPrefix with
  | nil => rfl
  | cons first rest ih => simp [ih]

theorem countdown_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? PaddingCountdown.machine (countdownWorkSteps problem)
        (workStartConfiguration PaddingCountdown.machine
          (countTape problem)) =
      some
        { state := PaddingCountdown.machine.acceptState,
          tape := countdownFinalTape problem } := by
  let polynomial := remainingPaddingPolynomial problem.verifier
  let scratch := countWord problem
  let outside := BuilderDynamicTokenCursorStep.finalOutside problem
  rcases BuilderUnaryPolynomial.root_register_length polynomial
      problem.input.length with ⟨wordPrefix, hScratch, hPrefixLength⟩
  have hCountEval : polynomial.eval problem.input.length =
      remainingPaddingCount problem := by rfl
  rw [hCountEval] at hScratch
  have hPrefixLength' : wordPrefix.length + 1 =
      countRootPrefixLength problem := by
    simpa [polynomial, countRootPrefixLength] using hPrefixLength
  have hScratch' : scratch =
      wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
        List.replicate (remainingPaddingCount problem)
          BuilderUnaryPolynomial.unitSymbol := by
    simpa [scratch, countWord, polynomial] using hScratch
  have hPositive := remainingPaddingCount_positive problem
  cases hCount : remainingPaddingCount problem with
  | zero => omega
  | succ remaining =>
      have hScratchLength : scratch.length + 1 =
          wordPrefix.length + (remaining + 1 + 1) + 1 := by
        rw [hScratch']
        simp [hCount]
      let tail := outside.drop
        (wordPrefix.length + (remaining + 1 + 1) + 1)
      have hCountOutside : countOutside problem =
          BuilderCompleteHeader.HeaderController.outsideBefore wordPrefix
            remaining tail := by
        change scratch ++ BuilderUnaryPolynomial.scratchEndSymbol ::
            outside.drop (scratch.length + 1) = _
        rw [hScratchLength]
        rw [hScratch']
        simp [BuilderCompleteHeader.HeaderController.outsideBefore,
          tail, hCount, PaddingCountdown.replicate_succ_append,
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
            simpa [scratch, countWord, polynomial] using hInScratch)
      have hLoop := PaddingCountdown.loop_workRunExact problem.input
        wordPrefix remaining tail
        (BuilderFirstClausePrefix.firstClauseTokens problem) hPrefixSymbols
      have hFinalOutside : countdownFinalOutside problem =
          PaddingCountdown.finalOutside wordPrefix (remaining + 1) tail := by
        change scratch.take (countRootPrefixLength problem) ++
            List.replicate (remainingPaddingCount problem + 1)
            BuilderUnaryPolynomial.scratchEndSymbol ++
            outside.drop (scratch.length + 1) = _
        rw [hScratchLength]
        rw [hScratch', ← hPrefixLength', hCount]
        rw [take_prefix_separator]
        simp [PaddingCountdown.finalOutside, tail, List.append_assoc]
      simpa [countdownWorkSteps, countControllerPrefixLength,
        ← hPrefixLength', hCount, countTape,
        countdownFinalTape, hCountOutside, hFinalOutside,
        PaddingCountdown.initialConfiguration,
        PaddingCountdown.finalConfiguration,
        PaddingCountdown.finalOutside,
        PaddingCountdown.machine,
        BuilderCompleteHeader.HeaderController.initialConfiguration,
        workStartConfiguration] using hLoop

theorem targetEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (targetEvaluator problem)
        (BuilderUnaryPolynomial.workSteps
          (secondClauseStartPolynomial problem.verifier) problem.input)
        (BuilderUnaryPolynomial.initialConfiguration
          (secondClauseStartPolynomial problem.verifier) problem.input
          (countdownFinalOutside problem)
          (BuilderFirstClausePrefix.firstClauseTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (secondClauseStartPolynomial problem.verifier) problem.input
          (countdownFinalOutside problem)
          (BuilderFirstClausePrefix.firstClauseTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (secondClauseStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)

private theorem countdownTarget_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (countdownTargetMachine problem)
        (countdownWorkSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (secondClauseStartPolynomial problem.verifier) problem.input)
        (workStartConfiguration (countdownTargetMachine problem)
          (countTape problem)) =
      some
        { state := (countdownTargetMachine problem).acceptState,
          tape := finalTape problem } := by
  let countdownInitial := workStartConfiguration PaddingCountdown.machine
    (countTape problem)
  let countdownFinal : WorkConfiguration :=
    { state := PaddingCountdown.machine.acceptState,
      tape := countdownFinalTape problem }
  let targetInitial := BuilderUnaryPolynomial.initialConfiguration
    (secondClauseStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)
  let targetFinal := BuilderUnaryPolynomial.finalConfiguration
    (secondClauseStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)
  have hCountdown : workRunExact? PaddingCountdown.machine
      (countdownWorkSteps problem) countdownInitial =
        some countdownFinal := by
    simpa [countdownInitial, countdownFinal] using
      countdown_workRunExact problem
  have hTarget : workRunExact? (targetEvaluator problem)
      (BuilderUnaryPolynomial.workSteps
        (secondClauseStartPolynomial problem.verifier) problem.input)
      targetInitial = some targetFinal := by
    simpa [targetInitial, targetFinal] using
      targetEvaluator_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    PaddingCountdown.machine (targetEvaluator problem)
    (countdownWorkSteps problem)
    (BuilderUnaryPolynomial.workSteps
      (secondClauseStartPolynomial problem.verifier) problem.input)
    countdownInitial countdownFinal targetFinal hCountdown
    (by
      simp [countdownFinal])
    hTarget
  simpa [countdownTargetMachine, targetEvaluator, countdownInitial, targetFinal,
    finalTape, finalOutside, BuilderUnaryPolynomial.finalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration, Nat.add_assoc] using hCombined

private theorem paddingSuffix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (paddingSuffixMachine problem) (suffixWorkSteps problem)
        (workStartConfiguration (paddingSuffixMachine problem)
          (BuilderDynamicTokenCursorStep.finalTape problem)) =
      some
        { state := (paddingSuffixMachine problem).acceptState,
          tape := finalTape problem } := by
  let countInitial := BuilderUnaryPolynomial.initialConfiguration
    (remainingPaddingPolynomial problem.verifier) problem.input
    (BuilderDynamicTokenCursorStep.finalOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)
  let countFinal := BuilderUnaryPolynomial.finalConfiguration
    (remainingPaddingPolynomial problem.verifier) problem.input
    (BuilderDynamicTokenCursorStep.finalOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)
  let suffixFinal : WorkConfiguration :=
    { state := (countdownTargetMachine problem).acceptState,
      tape := finalTape problem }
  have hCount : workRunExact? (countEvaluator problem)
      (BuilderUnaryPolynomial.workSteps
        (remainingPaddingPolynomial problem.verifier) problem.input)
      countInitial = some countFinal := by
    simpa [countInitial, countFinal] using countEvaluator_workRunExact problem
  have hTail : workRunExact? (countdownTargetMachine problem)
      (countdownWorkSteps problem + 1 +
        BuilderUnaryPolynomial.workSteps
          (secondClauseStartPolynomial problem.verifier) problem.input)
      { state := (countdownTargetMachine problem).startState,
        tape := countFinal.tape } = some suffixFinal := by
    simpa [countFinal, suffixFinal, countTape, countOutside,
      BuilderUnaryPolynomial.finalConfiguration,
      workStartConfiguration] using countdownTarget_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (countEvaluator problem) (countdownTargetMachine problem)
    (BuilderUnaryPolynomial.workSteps
      (remainingPaddingPolynomial problem.verifier) problem.input)
    (countdownWorkSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (secondClauseStartPolynomial problem.verifier) problem.input)
    countInitial countFinal suffixFinal hCount rfl hTail
  simpa [paddingSuffixMachine, countdownTargetMachine, targetEvaluator,
    countEvaluator, suffixWorkSteps, countInitial, suffixFinal,
    BuilderDynamicTokenCursorStep.finalTape,
    BuilderDynamicTokenCursorStep.finalOutside,
    BuilderUnaryPolynomial.initialConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration, Nat.add_assoc] using hCombined

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderDynamicTokenCursorStep.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (BuilderDynamicTokenCursorStep.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderDynamicTokenCursorStep.machine problem) (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderDynamicTokenCursorStep.machine problem)
      (paddingSuffixMachine problem))
    (BuilderDynamicTokenCursorStep.workSteps problem)
    (workStartConfiguration (BuilderDynamicTokenCursorStep.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderDynamicTokenCursorStep.finalConfiguration problem)
    (BuilderDynamicTokenCursorStep.workRunExact problem)
  simpa [machine, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hTransport

theorem launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderDynamicTokenCursorStep.finalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration (paddingSuffixMachine problem)
          (BuilderDynamicTokenCursorStep.finalTape problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderDynamicTokenCursorStep.machine problem)
    (paddingSuffixMachine problem)
    (BuilderDynamicTokenCursorStep.finalTape problem)
  simpa [machine, BuilderDynamicTokenCursorStep.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
/-- Every raw input follows the complete predecessor trace, evaluates the
remaining padding count, executes the input-dependent unary loop exactly, and
materializes the second-clause start coordinate. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let predecessorInitial := workStartConfiguration
    (BuilderDynamicTokenCursorStep.machine problem)
    (rawInputWorkTape problem.input)
  let predecessorFinal := BuilderDynamicTokenCursorStep.finalConfiguration
    problem
  let suffixFinal : WorkConfiguration :=
    { state := (paddingSuffixMachine problem).acceptState,
      tape := finalTape problem }
  have hPredecessor : workRunExact?
      (BuilderDynamicTokenCursorStep.machine problem)
      (BuilderDynamicTokenCursorStep.workSteps problem)
      predecessorInitial = some predecessorFinal := by
    simpa [predecessorInitial, predecessorFinal] using
      BuilderDynamicTokenCursorStep.workRunExact problem
  have hSuffix : workRunExact? (paddingSuffixMachine problem)
      (suffixWorkSteps problem)
      { state := (paddingSuffixMachine problem).startState,
        tape := predecessorFinal.tape } = some suffixFinal := by
    simpa [predecessorFinal, suffixFinal,
      BuilderDynamicTokenCursorStep.finalConfiguration,
      workStartConfiguration] using paddingSuffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderDynamicTokenCursorStep.machine problem)
    (paddingSuffixMachine problem)
    (BuilderDynamicTokenCursorStep.workSteps problem)
    (suffixWorkSteps problem) predecessorInitial predecessorFinal suffixFinal
    hPredecessor rfl hSuffix
  simpa [machine, workSteps, predecessorInitial, suffixFinal,
    finalConfiguration, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

/-! ### Exact schedule semantics -/

private theorem finiteIndices_starts_zero (width : Nat)
    (hWidth : 0 < width) :
    ∃ rest, finiteIndices width = ⟨0, hWidth⟩ :: rest := by
  cases width with
  | zero => exact False.elim (Nat.not_lt_zero 0 hWidth)
  | succ width => exact ⟨(finiteIndices width).map Fin.succ, rfl⟩

private theorem scheduledShapeConstraints_starts_firstSymbol
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ rest,
      problem.scheduledShapeConstraints =
        some (problem.symbolShapeAt time position) :: rest := by
  dsimp
  let time : Fin problem.dimensions.timeCount :=
    ⟨0, problem.dimensions.timeCount_positive⟩
  let position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode) :=
    ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
  rcases finiteIndices_starts_zero problem.dimensions.timeCount
      problem.dimensions.timeCount_positive with ⟨times, hTimes⟩
  rcases finiteIndices_starts_zero
      (problem.dimensions.tapeWidth problem.tableauInputMode)
      (problem.dimensions.tapeWidth_positive problem.tableauInputMode) with
    ⟨positions, hPositions⟩
  refine ⟨(positions.map fun next =>
      some (problem.symbolShapeAt time next)) ++
      [some (problem.headShapeAt time), some (problem.stateShapeAt time)] ++
      times.flatMap fun next =>
        ((finiteIndices
          (problem.dimensions.tapeWidth problem.tableauInputMode)).map
            fun nextPosition =>
              some (problem.symbolShapeAt next nextPosition)) ++
          [some (problem.headShapeAt next), some (problem.stateShapeAt next)],
    ?_⟩
  unfold VerifierTableauProblem.scheduledShapeConstraints
  rw [hTimes]
  simp only [List.flatMap_cons]
  rw [hPositions]
  rfl

private theorem formulaConstraintSchedule_starts_firstSymbol
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ rest,
      problem.formulaConstraintSchedule =
        some (problem.symbolShapeAt time position) :: rest := by
  dsimp
  rcases scheduledShapeConstraints_starts_firstSymbol problem with
    ⟨rest, hRest⟩
  refine ⟨rest ++ problem.scheduledInitialConstraints ++
      problem.scheduledControlConstraints ++
      problem.scheduledPreservationConstraints ++
      [some (.require
        (problem.stateLiteral problem.finalTime problem.acceptingState))], ?_⟩
  unfold VerifierTableauProblem.formulaConstraintSchedule
  rw [hRest]
  simp [List.append_assoc]

private theorem formulaClauseSchedule_starts_twoShapeClauses
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ second rest,
      problem.formulaClauseSchedule =
        some (atLeastOneBoundedClause
          (problem.symbolVariables time position)) ::
        some second :: rest := by
  dsimp
  rcases formulaConstraintSchedule_starts_firstSymbol problem with
    ⟨constraints, hConstraints⟩
  rw [VerifierTableauProblem.formulaClauseSchedule, hConstraints]
  simp only [List.flatMap_cons]
  unfold VerifierTableauProblem.symbolShapeAt
  dsimp [VerifierTableauProblem.scheduledConstraintClauses,
    LocalConstraint.emit, exactlyOneBoundedClauses, FormulaSchedule.pad,
    atMostOneBoundedClauses, excludeBoundedWithClauses]
  exact ⟨_, _, rfl⟩

private theorem firstShapeClause_emit_eq
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    BoundedClause.emit
        (atLeastOneBoundedClause
          (problem.symbolVariables time position)) =
      [{ positive := true, variableIndex := 0 },
       { positive := true, variableIndex := 1 },
       { positive := true, variableIndex := 2 }] := by
  dsimp
  simp [BoundedClause.emit, atLeastOneBoundedClause,
    VerifierTableauProblem.symbolVariables, tapeSymbols, trueLiteral,
    BoundedLiteral.emit, VerifierTableauProblem.symbolLiteral,
    VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
    VariableLayout.symbolBlock, VariableBlock.index,
    VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]

private theorem formulaClauseTokens_firstRectangle_then_secondSep
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest,
      problem.formulaClauseSchedule.flatMap problem.scheduledClauseTokens =
        [some CNFToken.sep,
         some CNFToken.t, some CNFToken.f,
         some CNFToken.t, some CNFToken.t, some CNFToken.f,
         some CNFToken.t, some CNFToken.t, some CNFToken.t,
         some CNFToken.f, some CNFToken.finish] ++
        List.replicate (problem.formulaTokensPerClause - 11) none ++
        some CNFToken.sep :: rest := by
  rcases formulaClauseSchedule_starts_twoShapeClauses problem with
    ⟨second, clauses, hClauses⟩
  rw [hClauses]
  simp only [List.flatMap_cons]
  dsimp [VerifierTableauProblem.scheduledClauseTokens]
  rw [firstShapeClause_emit_eq]
  simp only [encodeClauseTokens, encodeLiteralListTokens,
    encodeLiteralTokens, encodeUnaryTokens]
  unfold FormulaSchedule.pad
  refine ⟨(encodeLiteralListTokens second.emit ++ [CNFToken.finish]).map some ++
      List.replicate (problem.formulaTokensPerClause -
        (CNFToken.sep ::
          (encodeLiteralListTokens second.emit ++ [CNFToken.finish])).length)
        none ++ clauses.flatMap problem.scheduledClauseTokens, ?_⟩
  simp [List.append_assoc]

private theorem formulaTokensPerClause_at_least_twelve
    {language : Language} (problem : VerifierTableauProblem language) :
    12 ≤ problem.formulaTokensPerClause := by
  have hBound := formulaVariableSlotBound_at_least_three problem
  unfold VerifierTableauProblem.formulaTokensPerClause
  have hProduct : 10 ≤
      (problem.formulaVariableSlotBound + 4) *
        (problem.formulaVariableSlotBound + 1) := by
    exact Nat.le_trans (by decide : 10 ≤ 7 * 4)
      (Nat.mul_le_mul (by omega) (by omega))
  omega

/-- Every coordinate traversed by the unary loop is an in-range padding
opportunity in the first fixed-width clause rectangle. -/
theorem paddingSlot_direct_eq_padding {language : Language}
    (problem : VerifierTableauProblem language) (offset : Nat)
    (hOffset : offset < remainingPaddingCount problem) :
    problem.formulaTokenSlotDirect
        (BuilderDynamicTokenCursorStep.finalTokenSlot problem + offset) =
      some none := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_firstRectangle_then_secondSep problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses,
    BuilderDynamicTokenCursorStep.finalTokenSlot_eq_formulaVariableSlotBound_add_thirteen]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
          problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  have hCount :=
    remainingPaddingCount_eq_formulaTokensPerClause_sub_twelve problem
  have hWidth := formulaTokensPerClause_at_least_twelve problem
  simp only [List.append_assoc]
  rw [List.getElem?_append, hHeader, if_neg (by omega)]
  rw [show problem.formulaVariableSlotBound + 13 + offset -
      (problem.formulaVariableSlotBound + 1) = 12 + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 12 + offset - 11 = 1 + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_pos (by omega)]
  rw [List.getElem?_replicate, if_pos (by omega)]

/-- The exact target materialized after the countdown is the populated
separator opportunity beginning the second clause rectangle. -/
theorem secondClauseStart_direct_eq_sep {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect (secondClauseStart problem) =
      some (some CNFToken.sep) := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_firstRectangle_then_secondSep problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses, secondClauseStart_eq]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
          problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  have hWidth := formulaTokensPerClause_at_least_twelve problem
  simp only [List.append_assoc]
  rw [List.getElem?_append, hHeader, if_neg (by omega)]
  rw [show problem.formulaVariableSlotBound + 1 +
      problem.formulaTokensPerClause -
      (problem.formulaVariableSlotBound + 1) =
        problem.formulaTokensPerClause by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause - 11 =
      problem.formulaTokensPerClause - 11 by rfl]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause - 11 -
      (problem.formulaTokensPerClause - 11) = 0 by omega]
  rfl

/-- Fuelled specification traversal used to audit that the literal unary
loop skips only padding.  Populated opportunities are accumulated in order. -/
def specificationRun {language : Language}
    (problem : VerifierTableauProblem language) :
    Nat → VerifierTableauProblem.FormulaTokenCursor →
      Option (List CNFToken ×
        VerifierTableauProblem.FormulaTokenCursor)
  | 0, cursor => some ([], cursor)
  | fuel + 1, cursor =>
      match VerifierTableauProblem.FormulaTokenCursor.step problem cursor with
      | none => none
      | some (entry, next) =>
          match specificationRun problem fuel next with
          | none => none
          | some (tokens, final) => some (entry.toList ++ tokens, final)

private theorem specificationRun_padding_from_offset
    {language : Language} (problem : VerifierTableauProblem language) :
    ∀ count offset,
      offset + count ≤ remainingPaddingCount problem →
      specificationRun problem count
          ⟨BuilderDynamicTokenCursorStep.finalTokenSlot problem + offset⟩ =
        some ([],
          ⟨BuilderDynamicTokenCursorStep.finalTokenSlot problem +
            offset + count⟩) := by
  intro count
  induction count with
  | zero =>
      intro offset _hBound
      simp [specificationRun]
  | succ count ih =>
      intro offset hBound
      have hOffset : offset < remainingPaddingCount problem := by omega
      have hStep : VerifierTableauProblem.FormulaTokenCursor.step problem
          ⟨BuilderDynamicTokenCursorStep.finalTokenSlot problem + offset⟩ =
        some (none,
          ⟨BuilderDynamicTokenCursorStep.finalTokenSlot problem + offset + 1⟩) := by
        unfold VerifierTableauProblem.FormulaTokenCursor.step
        rw [paddingSlot_direct_eq_padding problem offset hOffset]
      have hTail := ih (offset + 1) (by omega)
      rw [specificationRun, hStep]
      rw [show BuilderDynamicTokenCursorStep.finalTokenSlot problem +
          offset + 1 =
        BuilderDynamicTokenCursorStep.finalTokenSlot problem +
          (offset + 1) by omega]
      simp only
      rw [hTail]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The repeated specification cursor emits no token while traversing the
entire remaining first-clause padding block and stops exactly at clause two. -/
theorem specification_padding_run {language : Language}
    (problem : VerifierTableauProblem language) :
    specificationRun problem (remainingPaddingCount problem)
        ⟨BuilderDynamicTokenCursorStep.finalTokenSlot problem⟩ =
      some ([], ⟨secondClauseStart problem⟩) := by
  have hRun := specificationRun_padding_from_offset problem
    (remainingPaddingCount problem) 0 (by omega)
  rw [Nat.add_zero] at hRun
  rw [predecessorSlot_add_remainingPaddingCount problem] at hRun
  exact hRun

/-- The next specification action after the padding run observes, but does
not yet emit, the separator beginning the second clause. -/
theorem specification_target_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨secondClauseStart problem⟩ =
      some (some CNFToken.sep, ⟨secondClauseStart problem + 1⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [secondClauseStart_direct_eq_sep]

theorem finalTokenBits_eq_encodedFormula_firstClause
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (BuilderFirstClausePrefix.firstClauseTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 12)) :=
  BuilderDynamicTokenCursorStep.finalTokenBits_eq_encodedFormula_firstClause
    problem

def finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  secondClauseStart problem

theorem finalTokenSlot_eq_secondClauseStart {language : Language}
    (problem : VerifierTableauProblem language) :
    finalTokenSlot problem = problem.formulaVariableSlotBound + 1 +
      problem.formulaTokensPerClause := by
  exact secondClauseStart_eq problem

theorem finalOutside_contains_finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.root_register_length
      (secondClauseStartPolynomial problem.verifier) problem.input.length with
    ⟨wordPrefix, hScratch, _hPrefixLength⟩
  refine ⟨wordPrefix,
    (countdownFinalOutside problem).drop
      ((BuilderUnaryPolynomial.scratchWord
        (secondClauseStartPolynomial problem.verifier)
        problem.input.length).length + 1), ?_⟩
  unfold finalOutside BuilderUnaryPolynomial.finalOutsideLeft
    BuilderUnaryPolynomial.overlayScratch finalTokenSlot secondClauseStart
  rw [hScratch]

theorem finalConfiguration_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (finalConfiguration problem).state = (machine problem).acceptState := rfl

set_option maxRecDepth 100000 in
private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
  unfold WorkMachine.isHalted
  rw [finalConfiguration_state]
  rw [(nat_beq_true_iff _ _).mpr rfl]
  rfl

/-! ### External compiled-time polynomial -/

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

def countdownBoundPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let count := remainingPaddingPolynomial verifier
  let rootPrefix := BuilderUnaryPolynomial.rootPrefixPolynomial count
  .add
    (.mul count
      (.add (scalePolynomial 2 rootPrefix) (.constant 8)))
    (.mul count count)

/-- External raw-transition bound for the predecessor, three bridges, both
unary evaluators, and the complete input-dependent countdown. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let count := remainingPaddingPolynomial verifier
  let target := secondClauseStartPolynomial verifier
  .add (BuilderDynamicTokenCursorStep.rawTimeBound verifier)
    (.add (.constant 18)
      (.add
        (scalePolynomial 6
          (BuilderUnaryPolynomial.workTimePolynomial count))
        (.add
          (scalePolynomial 6 (countdownBoundPolynomial verifier))
          (scalePolynomial 6
            (BuilderUnaryPolynomial.workTimePolynomial target)))))

theorem countdownBoundPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (countdownBoundPolynomial problem.verifier).eval problem.input.length =
      remainingPaddingCount problem *
          (2 * countRootPrefixLength problem + 8) +
        remainingPaddingCount problem * remainingPaddingCount problem := by
  simp [countdownBoundPolynomial, scalePolynomial,
    NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, remainingPaddingCount,
    countRootPrefixLength]

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderDynamicTokenCursorStep.rawTimeBound problem.verifier).eval
          problem.input.length + 18 +
        6 * BuilderUnaryPolynomial.workSteps
          (remainingPaddingPolynomial problem.verifier) problem.input +
        6 *
          (remainingPaddingCount problem *
              (2 * countRootPrefixLength problem + 8) +
            remainingPaddingCount problem * remainingPaddingCount problem) +
        6 * BuilderUnaryPolynomial.workSteps
          (secondClauseStartPolynomial problem.verifier) problem.input := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, scalePolynomial,
    BuilderUnaryPolynomial.workTimePolynomial_eval]
  rw [countdownBoundPolynomial_eval]
  omega

private theorem countdownWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    countdownWorkSteps problem ≤
      remainingPaddingCount problem *
          (2 * countRootPrefixLength problem + 8) +
        remainingPaddingCount problem * remainingPaddingCount problem := by
  have hLoop := PaddingCountdown.loopSteps_le
    (countControllerPrefixLength problem) (remainingPaddingCount problem)
  rcases BuilderUnaryPolynomial.root_register_length
      (remainingPaddingPolynomial problem.verifier) problem.input.length with
    ⟨wordPrefix, _hScratch, hRootLength⟩
  have hRootPositive : 0 < countRootPrefixLength problem := by
    unfold countRootPrefixLength
    rw [← hRootLength]
    omega
  have hPrefix : countControllerPrefixLength problem + 1 ≤
      countRootPrefixLength problem := by
    unfold countControllerPrefixLength
    omega
  have hInside :
      2 * (countControllerPrefixLength problem + 1) + 8 ≤
        2 * countRootPrefixLength problem + 8 := by omega
  have hScaled := Nat.mul_le_mul_left
    (remainingPaddingCount problem) hInside
  unfold countdownWorkSteps
  exact Nat.le_trans hLoop (Nat.add_le_add_right hScaled _)

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPredecessor := BuilderDynamicTokenCursorStep.rawTimeBound_le problem
  have hCountdown := countdownWorkSteps_le problem
  have hCountdownScaled := Nat.mul_le_mul_left 6 hCountdown
  rw [rawTimeBound_eval]
  unfold workSteps suffixWorkSteps
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

private theorem blankEquivalent_state (first second : Configuration)
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
  have hState := blankEquivalent_state first
    (encodeWorkConfiguration final) hEquivalent
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

/-! ### Fail-closed trace boundaries -/

def malformedCountdownScratchConfiguration
    (left right : List WorkSymbol) : WorkConfiguration :=
  { state := BuilderCompleteHeader.HeaderController.seekEndState
    tape :=
      { left := left
        head := BuilderUnaryPolynomial.registerMarkSymbol
        right := right } }

def malformedCountdownRootConfiguration
    (left right : List WorkSymbol) : WorkConfiguration :=
  { state := BuilderCompleteHeader.HeaderController.consumeState
    tape :=
      { left := left
        head := BuilderUnaryPolynomial.separatorSymbol
        right := right } }

/-- A non-scratch symbol in the countdown scan is stuck and remains a local
timeout for every fuel budget. -/
theorem malformedCountdownScratch_timeout (fuel : Nat)
    (left right : List WorkSymbol) :
    (let config := malformedCountdownScratchConfiguration left right
     let result := workRun PaddingCountdown.machine fuel config
     if result.state == PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let config := malformedCountdownScratchConfiguration left right
  have hStep : workStep? PaddingCountdown.machine config = none := by
    rfl
  have hRun := workRun_eq_self_of_workStep?_eq_none
    PaddingCountdown.machine config fuel hStep
  change
    (if (workRun PaddingCountdown.machine fuel config).state ==
          PaddingCountdown.machine.acceptState then WorkVerdict.accept
     else if (workRun PaddingCountdown.machine fuel config).state ==
          PaddingCountdown.machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  rfl

/-- A separator where the root decrement requires a unit is also stuck and
cannot fall through to either countdown halt. -/
theorem malformedCountdownRoot_timeout (fuel : Nat)
    (left right : List WorkSymbol) :
    (let config := malformedCountdownRootConfiguration left right
     let result := workRun PaddingCountdown.machine fuel config
     if result.state == PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let config := malformedCountdownRootConfiguration left right
  have hStep : workStep? PaddingCountdown.machine config = none := by
    rfl
  have hRun := workRun_eq_self_of_workStep?_eq_none
    PaddingCountdown.machine config fuel hStep
  change
    (if (workRun PaddingCountdown.machine fuel config).state ==
          PaddingCountdown.machine.acceptState then WorkVerdict.accept
     else if (workRun PaddingCountdown.machine fuel config).state ==
          PaddingCountdown.machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  rfl

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

private theorem machine_isHalted_prefix_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          config) = false := by
  have hHalted :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      (BuilderDynamicTokenCursorStep.machine problem)
      (paddingSuffixMachine problem) config
  simpa [machine] using hHalted

/-- The complete one-step cursor endpoint is globally nonhalting until the
outer bridge launches the remaining-padding evaluator. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderDynamicTokenCursorStep.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderDynamicTokenCursorStep.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (BuilderDynamicTokenCursorStep.finalConfiguration problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_prefix_false problem
      (BuilderDynamicTokenCursorStep.finalConfiguration problem))

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

/-- Removing the last target-evaluator transition leaves a nonhalting state;
the complete raw trace therefore cannot accept one work step early. -/
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

end BuilderFirstClausePaddingRun

end CookLevin

end PNP.Concrete
