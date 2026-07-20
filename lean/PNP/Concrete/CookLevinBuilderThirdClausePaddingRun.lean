/-
Copyright (c) 2026 PNP Labs.

Input-dependent traversal of the complete padding rectangle after the third
canonical Cook--Levin clause.

The predecessor retains the first padding opportunity at the third-clause
start plus eight. This module evaluates the exact remaining padding count
`formulaTokensPerClause - 8`, consumes that unary counter with one literal
loop, and then materializes the first coordinate of the fourth clause. No
formula token is emitted by this milestone.
-/

import PNP.Concrete.CookLevinBuilderThirdClausePrefix

namespace PNP.Concrete

namespace CookLevin

namespace BuilderThirdClausePaddingRun

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Exact external coordinates -/

/-- Number of padding opportunities from the retained third-clause endpoint
through the final cell of that fixed-width clause rectangle. -/
def remainingPaddingPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderFirstClausePaddingRun.remainingPaddingPolynomial verifier)
    (.constant 4)

def remainingPaddingCount {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (remainingPaddingPolynomial problem.verifier).eval problem.input.length

theorem remainingPaddingCount_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    remainingPaddingCount problem =
      (problem.formulaVariableSlotBound - 1) *
        (problem.formulaVariableSlotBound + 6) + 4 := by
  unfold remainingPaddingCount remainingPaddingPolynomial
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant]
  change BuilderFirstClausePaddingRun.remainingPaddingCount problem + 4 = _
  rw [BuilderFirstClausePaddingRun.remainingPaddingCount_eq]

theorem remainingPaddingCount_eq_formulaTokensPerClause_sub_eight
    {language : Language} (problem : VerifierTableauProblem language) :
    remainingPaddingCount problem = problem.formulaTokensPerClause - 8 := by
  rw [remainingPaddingCount_eq]
  have hBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three problem
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
  omega

/-- Absolute token coordinate of the first opportunity in the fourth clause
rectangle. -/
def fourthClauseStartPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderSecondClausePaddingRun.thirdClauseStartPolynomial verifier)
    (formulaClauseTokenPolynomial verifier)

def fourthClauseStart {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (fourthClauseStartPolynomial problem.verifier).eval problem.input.length

theorem fourthClauseStart_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    fourthClauseStart problem =
      problem.formulaVariableSlotBound + 1 +
        3 * problem.formulaTokensPerClause := by
  unfold fourthClauseStart fourthClauseStartPolynomial
  simp only [NatPolynomial.eval_add]
  change BuilderSecondClausePaddingRun.thirdClauseStart problem +
      (formulaClauseTokenPolynomial problem.verifier).eval
        problem.input.length = _
  rw [BuilderSecondClausePaddingRun.thirdClauseStart_eq]
  have hClause :
      (formulaClauseTokenPolynomial problem.verifier).eval
          problem.input.length = problem.formulaTokensPerClause := by
    unfold VerifierTableauProblem.formulaTokensPerClause
      VerifierTableauProblem.formulaVariableSlotBound
    simpa [BitString.size] using problem.formulaClauseTokenPolynomial_eval
  rw [hClause]
  omega

theorem predecessorSlot_add_remainingPaddingCount
    {language : Language} (problem : VerifierTableauProblem language) :
    BuilderThirdClausePrefix.finalTokenSlot problem +
        remainingPaddingCount problem = fourthClauseStart problem := by
  rw [BuilderThirdClausePrefix.finalTokenSlot_eq_thirdClauseStart_add_eight,
    remainingPaddingCount_eq_formulaTokensPerClause_sub_eight,
    fourthClauseStart_eq]
  have hWidth : 8 ≤ problem.formulaTokensPerClause := by
    have hBound :=
      BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
        problem
    unfold VerifierTableauProblem.formulaTokensPerClause
    have hProduct : 10 ≤
        (problem.formulaVariableSlotBound + 4) *
          (problem.formulaVariableSlotBound + 1) := by
      exact Nat.le_trans (by decide : 10 ≤ 7 * 4)
        (Nat.mul_le_mul (by omega) (by omega))
    omega
  omega

/-! ### Reused literal unary countdown loop -/


/-! ### Evaluator-loop-evaluator composition -/

def countEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (remainingPaddingPolynomial problem.verifier)

def targetEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (fourthClauseStartPolynomial problem.verifier)

def countdownTargetMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePaddingRun.PaddingCountdown.machine
    (targetEvaluator problem)

def paddingSuffixMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine (countEvaluator problem)
    (countdownTargetMachine problem)

/-- One literal finite rule table from raw input through the complete third
clause and across its entire remaining padding block. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderThirdClausePrefix.machine problem)
    (paddingSuffixMachine problem)

private theorem predecessor_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderThirdClausePrefix.machine problem) := by
  exact BuilderThirdClausePrefix.rule_source_ne_acceptState problem

private theorem countEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (countEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt (BuilderUnaryPolynomial.rule_source_lt_acceptState
    (remainingPaddingPolynomial problem.verifier) rule hRule)

private theorem countdown_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      BuilderFirstClausePaddingRun.PaddingCountdown.machine := by
  exact BuilderFirstClausePaddingRun.PaddingCountdown.rule_source_ne_acceptState

private theorem targetEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (targetEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt (BuilderUnaryPolynomial.rule_source_lt_acceptState
    (fourthClauseStartPolynomial problem.verifier) rule hRule)

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      3178 +
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
          (remainingPaddingPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (fourthClauseStartPolynomial problem.verifier) := by
  have hPredecessor := BuilderThirdClausePrefix.rules_length problem
  have hCount := BuilderUnaryPolynomial.rules_length
    (remainingPaddingPolynomial problem.verifier)
  have hTarget := BuilderUnaryPolynomial.rules_length
    (fourthClauseStartPolynomial problem.verifier)
  have hCountdown := BuilderFirstClausePaddingRun.PaddingCountdown.rules_length
  have hCountMachine :
      (BuilderUnaryPolynomial.machine
        (remainingPaddingPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (remainingPaddingPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hCount
  have hTargetMachine :
      (BuilderUnaryPolynomial.machine
        (fourthClauseStartPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (fourthClauseStartPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hTarget
  have hCountdownMachine :
      BuilderFirstClausePaddingRun.PaddingCountdown.machine.rules.length = 25 := by
    simpa [BuilderFirstClausePaddingRun.PaddingCountdown.machine] using hCountdown
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
    BuilderFirstClausePaddingRun.PaddingCountdown.machine
      (targetEvaluator problem)
    BuilderFirstClausePaddingRun.PaddingCountdown.rules_pairwise_query_distinct
    (BuilderUnaryPolynomial.rules_pairwise_query_distinct
      (fourthClauseStartPolynomial problem.verifier))
    countdown_noRuleAtAccept
  have hSuffix := BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (countEvaluator problem) (countdownTargetMachine problem)
    (BuilderUnaryPolynomial.rules_pairwise_query_distinct
      (remainingPaddingPolynomial problem.verifier))
    hCountdownTarget (countEvaluator_noRuleAtAccept problem)
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (BuilderThirdClausePrefix.machine problem)
    (paddingSuffixMachine problem)
    (BuilderThirdClausePrefix.rules_pairwise_query_distinct problem)
    hSuffix (predecessor_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderThirdClausePrefix.machine problem)
    (paddingSuffixMachine problem)
    (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
      (countEvaluator problem) (countdownTargetMachine problem)
      (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
        BuilderFirstClausePaddingRun.PaddingCountdown.machine
          (targetEvaluator problem)
        (BuilderUnaryPolynomial.machine_acceptState_ne_rejectState
          (fourthClauseStartPolynomial problem.verifier))))

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderThirdClausePrefix.machine problem)
    (paddingSuffixMachine problem)
    (BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
      (countEvaluator problem) (countdownTargetMachine problem)
      (BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
        BuilderFirstClausePaddingRun.PaddingCountdown.machine
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
    (BuilderThirdClausePrefix.finalOutside problem)

def countTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (countOutside problem)
    (BuilderThirdClausePrefix.thirdClauseTokens problem)

def countdownFinalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (countWord problem).take (countRootPrefixLength problem) ++
    List.replicate (remainingPaddingCount problem + 1)
      BuilderUnaryPolynomial.scratchEndSymbol ++
    (BuilderThirdClausePrefix.finalOutside problem).drop
      ((countWord problem).length + 1)

def countdownFinalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (countdownFinalOutside problem)
    (BuilderThirdClausePrefix.thirdClauseTokens problem)

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (fourthClauseStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (BuilderThirdClausePrefix.thirdClauseTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def countdownWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFirstClausePaddingRun.PaddingCountdown.loopSteps
    (countControllerPrefixLength problem)
    (remainingPaddingCount problem)

def suffixWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderUnaryPolynomial.workSteps
      (remainingPaddingPolynomial problem.verifier) problem.input + 1 +
    countdownWorkSteps problem + 1 +
    BuilderUnaryPolynomial.workSteps
      (fourthClauseStartPolynomial problem.verifier) problem.input

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderThirdClausePrefix.workSteps problem + 1 +
    suffixWorkSteps problem

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (BuilderThirdClausePrefix.thirdClauseTokens problem)

theorem countEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (countEvaluator problem)
        (BuilderUnaryPolynomial.workSteps
          (remainingPaddingPolynomial problem.verifier) problem.input)
        (BuilderUnaryPolynomial.initialConfiguration
          (remainingPaddingPolynomial problem.verifier) problem.input
          (BuilderThirdClausePrefix.finalOutside problem)
          (BuilderThirdClausePrefix.thirdClauseTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (remainingPaddingPolynomial problem.verifier) problem.input
          (BuilderThirdClausePrefix.finalOutside problem)
          (BuilderThirdClausePrefix.thirdClauseTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (remainingPaddingPolynomial problem.verifier) problem.input
    (BuilderThirdClausePrefix.finalOutside problem)
    (BuilderThirdClausePrefix.thirdClauseTokens problem)

private theorem take_prefix_separator
    (wordPrefix suffix : List WorkSymbol) :
    (wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol :: suffix).take
        (wordPrefix.length + 1) =
      wordPrefix ++ [BuilderUnaryPolynomial.separatorSymbol] := by
  induction wordPrefix with
  | nil => rfl
  | cons first rest ih => simp [ih]

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

theorem countdown_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderFirstClausePaddingRun.PaddingCountdown.machine (countdownWorkSteps problem)
        (workStartConfiguration BuilderFirstClausePaddingRun.PaddingCountdown.machine
          (countTape problem)) =
      some
        { state := BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState,
          tape := countdownFinalTape problem } := by
  let polynomial := remainingPaddingPolynomial problem.verifier
  let scratch := countWord problem
  let outside := BuilderThirdClausePrefix.finalOutside problem
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
          tail, hCount, replicate_succ_append,
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
      have hLoop := BuilderFirstClausePaddingRun.PaddingCountdown.loop_workRunExact problem.input
        wordPrefix remaining tail
        (BuilderThirdClausePrefix.thirdClauseTokens problem) hPrefixSymbols
      have hFinalOutside : countdownFinalOutside problem =
          BuilderFirstClausePaddingRun.PaddingCountdown.finalOutside wordPrefix (remaining + 1) tail := by
        change scratch.take (countRootPrefixLength problem) ++
            List.replicate (remainingPaddingCount problem + 1)
            BuilderUnaryPolynomial.scratchEndSymbol ++
            outside.drop (scratch.length + 1) = _
        rw [hScratchLength]
        rw [hScratch', ← hPrefixLength', hCount]
        rw [take_prefix_separator]
        simp [BuilderFirstClausePaddingRun.PaddingCountdown.finalOutside, tail, List.append_assoc]
      simpa [countdownWorkSteps, countControllerPrefixLength,
        ← hPrefixLength', hCount, countTape,
        countdownFinalTape, hCountOutside, hFinalOutside,
        BuilderFirstClausePaddingRun.PaddingCountdown.initialConfiguration,
        BuilderFirstClausePaddingRun.PaddingCountdown.finalConfiguration,
        BuilderFirstClausePaddingRun.PaddingCountdown.finalOutside,
        BuilderFirstClausePaddingRun.PaddingCountdown.machine,
        BuilderCompleteHeader.HeaderController.initialConfiguration,
        workStartConfiguration] using hLoop

theorem targetEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (targetEvaluator problem)
        (BuilderUnaryPolynomial.workSteps
          (fourthClauseStartPolynomial problem.verifier) problem.input)
        (BuilderUnaryPolynomial.initialConfiguration
          (fourthClauseStartPolynomial problem.verifier) problem.input
          (countdownFinalOutside problem)
          (BuilderThirdClausePrefix.thirdClauseTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (fourthClauseStartPolynomial problem.verifier) problem.input
          (countdownFinalOutside problem)
          (BuilderThirdClausePrefix.thirdClauseTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (fourthClauseStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderThirdClausePrefix.thirdClauseTokens problem)

private theorem countdownTarget_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (countdownTargetMachine problem)
        (countdownWorkSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (fourthClauseStartPolynomial problem.verifier) problem.input)
        (workStartConfiguration (countdownTargetMachine problem)
          (countTape problem)) =
      some
        { state := (countdownTargetMachine problem).acceptState,
          tape := finalTape problem } := by
  let countdownInitial := workStartConfiguration BuilderFirstClausePaddingRun.PaddingCountdown.machine
    (countTape problem)
  let countdownFinal : WorkConfiguration :=
    { state := BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState,
      tape := countdownFinalTape problem }
  let targetInitial := BuilderUnaryPolynomial.initialConfiguration
    (fourthClauseStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderThirdClausePrefix.thirdClauseTokens problem)
  let targetFinal := BuilderUnaryPolynomial.finalConfiguration
    (fourthClauseStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderThirdClausePrefix.thirdClauseTokens problem)
  have hCountdown : workRunExact? BuilderFirstClausePaddingRun.PaddingCountdown.machine
      (countdownWorkSteps problem) countdownInitial =
        some countdownFinal := by
    simpa [countdownInitial, countdownFinal] using
      countdown_workRunExact problem
  have hTarget : workRunExact? (targetEvaluator problem)
      (BuilderUnaryPolynomial.workSteps
        (fourthClauseStartPolynomial problem.verifier) problem.input)
      targetInitial = some targetFinal := by
    simpa [targetInitial, targetFinal] using
      targetEvaluator_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    BuilderFirstClausePaddingRun.PaddingCountdown.machine (targetEvaluator problem)
    (countdownWorkSteps problem)
    (BuilderUnaryPolynomial.workSteps
      (fourthClauseStartPolynomial problem.verifier) problem.input)
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
          (BuilderThirdClausePrefix.finalTape problem)) =
      some
        { state := (paddingSuffixMachine problem).acceptState,
          tape := finalTape problem } := by
  let countInitial := BuilderUnaryPolynomial.initialConfiguration
    (remainingPaddingPolynomial problem.verifier) problem.input
    (BuilderThirdClausePrefix.finalOutside problem)
    (BuilderThirdClausePrefix.thirdClauseTokens problem)
  let countFinal := BuilderUnaryPolynomial.finalConfiguration
    (remainingPaddingPolynomial problem.verifier) problem.input
    (BuilderThirdClausePrefix.finalOutside problem)
    (BuilderThirdClausePrefix.thirdClauseTokens problem)
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
          (fourthClauseStartPolynomial problem.verifier) problem.input)
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
        (fourthClauseStartPolynomial problem.verifier) problem.input)
    countInitial countFinal suffixFinal hCount rfl hTail
  simpa [paddingSuffixMachine, countdownTargetMachine, targetEvaluator,
    countEvaluator, suffixWorkSteps, countInitial, suffixFinal,
    BuilderThirdClausePrefix.finalTape,
    BuilderThirdClausePrefix.finalOutside,
    BuilderUnaryPolynomial.initialConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration, Nat.add_assoc] using hCombined

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderThirdClausePrefix.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (BuilderThirdClausePrefix.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderThirdClausePrefix.machine problem) (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderThirdClausePrefix.machine problem)
      (paddingSuffixMachine problem))
    (BuilderThirdClausePrefix.workSteps problem)
    (workStartConfiguration (BuilderThirdClausePrefix.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderThirdClausePrefix.finalConfiguration problem)
    (BuilderThirdClausePrefix.workRunExact problem)
  simpa [machine, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hTransport

theorem launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderThirdClausePrefix.finalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration (paddingSuffixMachine problem)
          (BuilderThirdClausePrefix.finalTape problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderThirdClausePrefix.machine problem)
    (paddingSuffixMachine problem)
    (BuilderThirdClausePrefix.finalTape problem)
  simpa [machine, BuilderThirdClausePrefix.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
/-- Every raw input follows the complete predecessor trace, evaluates the
remaining padding count, executes the input-dependent unary loop exactly, and
materializes the fourth-clause start coordinate. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let predecessorInitial := workStartConfiguration
    (BuilderThirdClausePrefix.machine problem)
    (rawInputWorkTape problem.input)
  let predecessorFinal := BuilderThirdClausePrefix.finalConfiguration
    problem
  let suffixFinal : WorkConfiguration :=
    { state := (paddingSuffixMachine problem).acceptState,
      tape := finalTape problem }
  have hPredecessor : workRunExact?
      (BuilderThirdClausePrefix.machine problem)
      (BuilderThirdClausePrefix.workSteps problem)
      predecessorInitial = some predecessorFinal := by
    simpa [predecessorInitial, predecessorFinal] using
      BuilderThirdClausePrefix.workRunExact problem
  have hSuffix : workRunExact? (paddingSuffixMachine problem)
      (suffixWorkSteps problem)
      { state := (paddingSuffixMachine problem).startState,
        tape := predecessorFinal.tape } = some suffixFinal := by
    simpa [predecessorFinal, suffixFinal,
      BuilderThirdClausePrefix.finalConfiguration,
      workStartConfiguration] using paddingSuffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderThirdClausePrefix.machine problem)
    (paddingSuffixMachine problem)
    (BuilderThirdClausePrefix.workSteps problem)
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

private theorem formulaClauseSchedule_starts_fourShapeClauses
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ left right thirdLeft thirdRight fourthLeft fourthRight :
        Fin problem.FormulaWidth, ∃ rest,
      problem.formulaClauseSchedule =
        some (atLeastOneBoundedClause
          (problem.symbolVariables time position)) ::
        some (excludeBoundedPairClause left right) ::
        some (excludeBoundedPairClause thirdLeft thirdRight) ::
        some (excludeBoundedPairClause fourthLeft fourthRight) :: rest ∧
      left.val = 0 ∧ right.val = 1 ∧
        thirdLeft.val = 0 ∧ thirdRight.val = 2 ∧
        fourthLeft.val = 1 ∧ fourthRight.val = 2 := by
  dsimp
  rcases formulaConstraintSchedule_starts_firstSymbol problem with
    ⟨constraints, hConstraints⟩
  rw [VerifierTableauProblem.formulaClauseSchedule, hConstraints]
  simp only [List.flatMap_cons]
  unfold VerifierTableauProblem.symbolShapeAt
  dsimp [VerifierTableauProblem.scheduledConstraintClauses,
    LocalConstraint.emit, exactlyOneBoundedClauses, FormulaSchedule.pad,
    atMostOneBoundedClauses, excludeBoundedWithClauses]
  refine ⟨_, _, _, _, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [VerifierTableauProblem.symbolLiteral,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]

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

private theorem formulaClauseTokens_first_three_rectangles_then_fourthSep
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest,
      problem.formulaClauseSchedule.flatMap problem.scheduledClauseTokens =
        [some CNFToken.sep,
         some CNFToken.t, some CNFToken.f,
         some CNFToken.t, some CNFToken.t, some CNFToken.f,
         some CNFToken.t, some CNFToken.t, some CNFToken.t,
         some CNFToken.f, some CNFToken.finish] ++
        List.replicate (problem.formulaTokensPerClause - 11) none ++
        [some CNFToken.sep,
         some CNFToken.f, some CNFToken.f,
         some CNFToken.f, some CNFToken.t, some CNFToken.f,
         some CNFToken.finish] ++
        List.replicate (problem.formulaTokensPerClause - 7) none ++
        [some CNFToken.sep,
         some CNFToken.f, some CNFToken.f,
         some CNFToken.f, some CNFToken.t, some CNFToken.t,
         some CNFToken.f, some CNFToken.finish] ++
        List.replicate (problem.formulaTokensPerClause - 8) none ++
        some CNFToken.sep :: rest := by
  rcases formulaClauseSchedule_starts_fourShapeClauses problem with
    ⟨left, right, thirdLeft, thirdRight, fourthLeft, fourthRight,
      clauses, hClauses, hLeft, hRight, hThirdLeft, hThirdRight,
      hFourthLeft, hFourthRight⟩
  rw [hClauses]
  simp only [List.flatMap_cons]
  dsimp [VerifierTableauProblem.scheduledClauseTokens]
  rw [firstShapeClause_emit_eq]
  simp only [encodeClauseTokens, encodeLiteralListTokens,
    encodeLiteralTokens, encodeUnaryTokens]
  unfold FormulaSchedule.pad
  have hVariableBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
      problem
  have hClauseWidth : 12 ≤ problem.formulaTokensPerClause := by
    unfold VerifierTableauProblem.formulaTokensPerClause
    have hProduct : 10 ≤
        (problem.formulaVariableSlotBound + 4) *
          (problem.formulaVariableSlotBound + 1) := by
      exact Nat.le_trans (by decide : 10 ≤ 7 * 4)
        (Nat.mul_le_mul (by omega) (by omega))
    omega
  let fourthTail : List (Option CNFToken) :=
    (encodeLiteralListTokens
        (excludeBoundedPairClause fourthLeft fourthRight).emit ++
      [CNFToken.finish]).map some ++
      List.replicate (problem.formulaTokensPerClause -
        (CNFToken.sep ::
          (encodeLiteralListTokens
              (excludeBoundedPairClause fourthLeft fourthRight).emit ++
            [CNFToken.finish])).length)
        none ++ clauses.flatMap problem.scheduledClauseTokens
  refine ⟨fourthTail, ?_⟩
  simp [fourthTail, BoundedClause.emit, excludeBoundedPairClause, falseLiteral,
    BoundedLiteral.emit, encodeLiteralListTokens, encodeLiteralTokens,
    encodeUnaryTokens, hLeft, hRight, hThirdLeft, hThirdRight,
    hFourthLeft, hFourthRight, List.append_assoc]

private theorem formulaTokensPerClause_at_least_twelve
    {language : Language} (problem : VerifierTableauProblem language) :
    12 ≤ problem.formulaTokensPerClause := by
  have hBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three problem
  unfold VerifierTableauProblem.formulaTokensPerClause
  have hProduct : 10 ≤
      (problem.formulaVariableSlotBound + 4) *
        (problem.formulaVariableSlotBound + 1) := by
    exact Nat.le_trans (by decide : 10 ≤ 7 * 4)
      (Nat.mul_le_mul (by omega) (by omega))
  omega

/-- Every coordinate traversed by the unary loop is an in-range padding
opportunity in the third fixed-width clause rectangle. -/
theorem paddingSlot_direct_eq_padding {language : Language}
    (problem : VerifierTableauProblem language) (offset : Nat)
    (hOffset : offset < remainingPaddingCount problem) :
    problem.formulaTokenSlotDirect
        (BuilderThirdClausePrefix.finalTokenSlot problem + offset) =
      some none := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_first_three_rectangles_then_fourthSep problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses,
    BuilderThirdClausePrefix.finalTokenSlot_eq_thirdClauseStart_add_eight]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
          problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  have hCount :=
    remainingPaddingCount_eq_formulaTokensPerClause_sub_eight problem
  have hWidth := formulaTokensPerClause_at_least_twelve problem
  simp only [List.append_assoc]
  rw [List.getElem?_append, hHeader, if_neg (by omega)]
  rw [show problem.formulaVariableSlotBound + 1 +
      2 * problem.formulaTokensPerClause + 8 + offset -
      (problem.formulaVariableSlotBound + 1) =
        2 * problem.formulaTokensPerClause + 8 + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 2 * problem.formulaTokensPerClause + 8 + offset -
      11 = (problem.formulaTokensPerClause - 11) +
        problem.formulaTokensPerClause + 8 + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 11) +
      problem.formulaTokensPerClause + 8 + offset -
      (problem.formulaTokensPerClause - 11) =
        problem.formulaTokensPerClause + 8 + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause + 8 + offset -
      7 = (problem.formulaTokensPerClause - 7) + 8 + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 7) + 8 + offset -
      (problem.formulaTokensPerClause - 7) = 8 + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 8 + offset - 8 = offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_pos (by omega)]
  rw [List.getElem?_replicate, if_pos (by omega)]

/-- The exact target materialized after the countdown is the populated
separator opportunity beginning the fourth clause rectangle. -/
theorem fourthClauseStart_direct_eq_sep {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect (fourthClauseStart problem) =
      some (some CNFToken.sep) := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_first_three_rectangles_then_fourthSep problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses, fourthClauseStart_eq]
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
      3 * problem.formulaTokensPerClause -
      (problem.formulaVariableSlotBound + 1) =
        3 * problem.formulaTokensPerClause by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 3 * problem.formulaTokensPerClause -
      11 = (problem.formulaTokensPerClause - 11) +
        2 * problem.formulaTokensPerClause by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 11) +
      2 * problem.formulaTokensPerClause -
      (problem.formulaTokensPerClause - 11) =
        2 * problem.formulaTokensPerClause by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 2 * problem.formulaTokensPerClause - 7 =
      (problem.formulaTokensPerClause - 7) +
        problem.formulaTokensPerClause by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 7) +
      problem.formulaTokensPerClause -
      (problem.formulaTokensPerClause - 7) =
        problem.formulaTokensPerClause by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause - 8 =
      problem.formulaTokensPerClause - 8 by rfl]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause - 8 -
      (problem.formulaTokensPerClause - 8) = 0 by omega]
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
          ⟨BuilderThirdClausePrefix.finalTokenSlot problem + offset⟩ =
        some ([],
          ⟨BuilderThirdClausePrefix.finalTokenSlot problem +
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
          ⟨BuilderThirdClausePrefix.finalTokenSlot problem + offset⟩ =
        some (none,
          ⟨BuilderThirdClausePrefix.finalTokenSlot problem + offset + 1⟩) := by
        unfold VerifierTableauProblem.FormulaTokenCursor.step
        rw [paddingSlot_direct_eq_padding problem offset hOffset]
      have hTail := ih (offset + 1) (by omega)
      rw [specificationRun, hStep]
      rw [show BuilderThirdClausePrefix.finalTokenSlot problem +
          offset + 1 =
        BuilderThirdClausePrefix.finalTokenSlot problem +
          (offset + 1) by omega]
      simp only
      rw [hTail]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The repeated specification cursor emits no token while traversing the
entire remaining third-clause padding block and stops exactly at clause four. -/
theorem specification_padding_run {language : Language}
    (problem : VerifierTableauProblem language) :
    specificationRun problem (remainingPaddingCount problem)
        ⟨BuilderThirdClausePrefix.finalTokenSlot problem⟩ =
      some ([], ⟨fourthClauseStart problem⟩) := by
  have hRun := specificationRun_padding_from_offset problem
    (remainingPaddingCount problem) 0 (by omega)
  rw [Nat.add_zero] at hRun
  rw [predecessorSlot_add_remainingPaddingCount problem] at hRun
  exact hRun

/-- The next specification action after the padding run observes, but does
not yet emit, the separator beginning the fourth clause. -/
theorem specification_target_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨fourthClauseStart problem⟩ =
      some (some CNFToken.sep, ⟨fourthClauseStart problem + 1⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [fourthClauseStart_direct_eq_sep]

theorem finalTokenBits_eq_encodedFormula_thirdClause
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (BuilderThirdClausePrefix.thirdClauseTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 27)) :=
  BuilderThirdClausePrefix.finalTokenBits_eq_encodedFormula_thirdClause
    problem

def finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  fourthClauseStart problem

theorem finalTokenSlot_eq_fourthClauseStart {language : Language}
    (problem : VerifierTableauProblem language) :
    finalTokenSlot problem = problem.formulaVariableSlotBound + 1 +
      3 * problem.formulaTokensPerClause := by
  exact fourthClauseStart_eq problem

theorem finalOutside_contains_finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.root_register_length
      (fourthClauseStartPolynomial problem.verifier) problem.input.length with
    ⟨wordPrefix, hScratch, _hPrefixLength⟩
  refine ⟨wordPrefix,
    (countdownFinalOutside problem).drop
      ((BuilderUnaryPolynomial.scratchWord
        (fourthClauseStartPolynomial problem.verifier)
        problem.input.length).length + 1), ?_⟩
  unfold finalOutside BuilderUnaryPolynomial.finalOutsideLeft
    BuilderUnaryPolynomial.overlayScratch finalTokenSlot fourthClauseStart
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
  let target := fourthClauseStartPolynomial verifier
  .add (BuilderThirdClausePrefix.rawTimeBound verifier)
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
      (BuilderThirdClausePrefix.rawTimeBound problem.verifier).eval
          problem.input.length + 18 +
        6 * BuilderUnaryPolynomial.workSteps
          (remainingPaddingPolynomial problem.verifier) problem.input +
        6 *
          (remainingPaddingCount problem *
              (2 * countRootPrefixLength problem + 8) +
            remainingPaddingCount problem * remainingPaddingCount problem) +
        6 * BuilderUnaryPolynomial.workSteps
          (fourthClauseStartPolynomial problem.verifier) problem.input := by
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
  have hLoop := BuilderFirstClausePaddingRun.PaddingCountdown.loopSteps_le
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
  have hPredecessor := BuilderThirdClausePrefix.rawTimeBound_le problem
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
     let result := workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config
     if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let config := malformedCountdownScratchConfiguration left right
  have hStep : workStep? BuilderFirstClausePaddingRun.PaddingCountdown.machine config = none := by
    rfl
  have hRun := workRun_eq_self_of_workStep?_eq_none
    BuilderFirstClausePaddingRun.PaddingCountdown.machine config fuel hStep
  change
    (if (workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config).state ==
          BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState then WorkVerdict.accept
     else if (workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config).state ==
          BuilderFirstClausePaddingRun.PaddingCountdown.machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  rfl

/-- A separator where the root decrement requires a unit is also stuck and
cannot fall through to either countdown halt. -/
theorem malformedCountdownRoot_timeout (fuel : Nat)
    (left right : List WorkSymbol) :
    (let config := malformedCountdownRootConfiguration left right
     let result := workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config
     if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState then
       WorkVerdict.accept
     else if result.state == BuilderFirstClausePaddingRun.PaddingCountdown.machine.rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let config := malformedCountdownRootConfiguration left right
  have hStep : workStep? BuilderFirstClausePaddingRun.PaddingCountdown.machine config = none := by
    rfl
  have hRun := workRun_eq_self_of_workStep?_eq_none
    BuilderFirstClausePaddingRun.PaddingCountdown.machine config fuel hStep
  change
    (if (workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config).state ==
          BuilderFirstClausePaddingRun.PaddingCountdown.machine.acceptState then WorkVerdict.accept
     else if (workRun BuilderFirstClausePaddingRun.PaddingCountdown.machine fuel config).state ==
          BuilderFirstClausePaddingRun.PaddingCountdown.machine.rejectState then WorkVerdict.reject
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
      (BuilderThirdClausePrefix.machine problem)
      (paddingSuffixMachine problem) config
  simpa [machine] using hHalted

/-- The complete third-clause endpoint is globally nonhalting until the
outer bridge launches the remaining-padding evaluator. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderThirdClausePrefix.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderThirdClausePrefix.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (BuilderThirdClausePrefix.finalConfiguration problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_prefix_false problem
      (BuilderThirdClausePrefix.finalConfiguration problem))

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

end BuilderThirdClausePaddingRun

end CookLevin

end PNP.Concrete
