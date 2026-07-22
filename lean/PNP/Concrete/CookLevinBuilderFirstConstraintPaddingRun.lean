/-
Copyright (c) 2026 PNP Labs.

Input-dependent traversal of every remaining empty fixed-width clause
rectangle belonging to the first scheduled Cook--Levin constraint.

The predecessor retains the first opportunity in the sixth clause rectangle.
This module evaluates the exact remaining token count
`(formulaVariableSlotBound - 2) * (formulaVariableSlotBound + 2) *
formulaTokensPerClause`, consumes that unary counter with one literal loop,
and then materializes the first coordinate of the second scheduled
constraint. No formula token is emitted by this milestone.
-/

import PNP.Concrete.CookLevinBuilderFifthClausePaddingRun

namespace PNP.Concrete

namespace CookLevin

namespace BuilderFirstConstraintPaddingRun

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Exact external coordinates -/

/-- The tape-width polynomial with its final explicit unit removed. -/
private def tapeWidthPredecessorPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (formulaEncodedInputPolynomial verifier)
    (.mul (.constant 2) (formulaFuelPolynomial verifier))

private theorem tapeWidthPredecessorPolynomial_eval_add_one
    {language : Language} (verifier : PolynomialTimeVerifier language)
    (inputLength : Nat) :
    (tapeWidthPredecessorPolynomial verifier).eval inputLength + 1 =
      (formulaTapeWidthPolynomial verifier).eval inputLength := by
  rfl

/-- A subtraction-free polynomial for `formulaVariableSlotBound - 2`.
The two removed units are exposed by the positive time and tape dimensions. -/
private def formulaVariableMinusTwoPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let fuel := formulaFuelPolynomial verifier
  let time := formulaTimeCountPolynomial verifier
  let tape := formulaTapeWidthPolynomial verifier
  let tapePredecessor := tapeWidthPredecessorPolynomial verifier
  let states := formulaStateCountPolynomial verifier
  let certificate := verifier.certificateBound
  .add
    (.add
      (.add
        (.add
          (.mul (.mul (.constant 2) time) tape)
          (.mul time tapePredecessor))
        fuel)
      (.mul time tape))
    (.add (.mul time states) (.add certificate certificate))

private theorem formulaVariableMinusTwoPolynomial_eval_add_two
    {language : Language} (problem : VerifierTableauProblem language) :
    (formulaVariableMinusTwoPolynomial problem.verifier).eval
        problem.input.length + 2 = problem.formulaVariableSlotBound := by
  have hTime :
      (formulaFuelPolynomial problem.verifier).eval problem.input.length + 1 =
        (formulaTimeCountPolynomial problem.verifier).eval
          problem.input.length := by
    rfl
  have hTape := tapeWidthPredecessorPolynomial_eval_add_one
    problem.verifier problem.input.length
  have hReplacement :
      (formulaTimeCountPolynomial problem.verifier).eval
          problem.input.length *
          (tapeWidthPredecessorPolynomial problem.verifier).eval
            problem.input.length +
        (formulaFuelPolynomial problem.verifier).eval problem.input.length + 1 =
      (formulaTimeCountPolynomial problem.verifier).eval
          problem.input.length *
        (formulaTapeWidthPolynomial problem.verifier).eval
          problem.input.length := by
    calc
      _ = (formulaTimeCountPolynomial problem.verifier).eval
              problem.input.length *
            (tapeWidthPredecessorPolynomial problem.verifier).eval
              problem.input.length +
          (formulaTimeCountPolynomial problem.verifier).eval
            problem.input.length := by rw [Nat.add_assoc, hTime]
      _ = (formulaTimeCountPolynomial problem.verifier).eval
              problem.input.length *
            ((tapeWidthPredecessorPolynomial problem.verifier).eval
              problem.input.length + 1) := by
            rw [Nat.mul_succ]
      _ = _ := by rw [hTape]
  unfold formulaVariableMinusTwoPolynomial
    VerifierTableauProblem.formulaVariableSlotBound
    formulaVariableCountPolynomial
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, BitString.size, Nat.mul_assoc]
  omega

private theorem formulaVariableMinusTwoPolynomial_eval
    {language : Language} (problem : VerifierTableauProblem language) :
    (formulaVariableMinusTwoPolynomial problem.verifier).eval
        problem.input.length = problem.formulaVariableSlotBound - 2 := by
  have hRelation := formulaVariableMinusTwoPolynomial_eval_add_two problem
  omega

/-- Number of token-padding opportunities remaining after the fifth empty
clause rectangle and before the second scheduled constraint. -/
def paddingPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul
    (.mul (formulaVariableMinusTwoPolynomial verifier)
      (.add (formulaVariableCountPolynomial verifier) (.constant 2)))
    (formulaClauseTokenPolynomial verifier)

def paddingCount {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (paddingPolynomial problem.verifier).eval problem.input.length

theorem paddingCount_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    paddingCount problem =
      (problem.formulaVariableSlotBound - 2) *
        (problem.formulaVariableSlotBound + 2) *
          problem.formulaTokensPerClause := by
  unfold paddingCount paddingPolynomial
  simp only [NatPolynomial.eval_mul, NatPolynomial.eval_add,
    NatPolynomial.eval_constant]
  rw [formulaVariableMinusTwoPolynomial_eval problem]
  have hVariable :
      (formulaVariableCountPolynomial problem.verifier).eval
          problem.input.length = problem.formulaVariableSlotBound := by
    rfl
  rw [hVariable]
  have hClause :
      (formulaClauseTokenPolynomial problem.verifier).eval
          problem.input.length = problem.formulaTokensPerClause := by
    unfold VerifierTableauProblem.formulaTokensPerClause
      VerifierTableauProblem.formulaVariableSlotBound
    simpa [BitString.size] using problem.formulaClauseTokenPolynomial_eval
  rw [hClause]

theorem paddingCount_eq_remaining_first_constraint
    {language : Language} (problem : VerifierTableauProblem language) :
    paddingCount problem =
      (problem.formulaClauseSlotsPerConstraint - 5) *
        problem.formulaTokensPerClause := by
  rw [paddingCount_eq]
  have hBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
      problem
  let predecessor := problem.formulaVariableSlotBound - 2
  have hVariable :
      problem.formulaVariableSlotBound = predecessor + 2 := by
    unfold predecessor
    omega
  unfold VerifierTableauProblem.formulaClauseSlotsPerConstraint
  rw [hVariable]
  have hSquare :
      1 + (predecessor + 2) * (predecessor + 2) =
        5 + predecessor * (predecessor + 4) := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  rw [hSquare]
  simp

theorem paddingCount_positive {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < paddingCount problem := by
  rw [paddingCount_eq]
  have hBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
      problem
  have hClause : 0 < problem.formulaTokensPerClause := by
    unfold VerifierTableauProblem.formulaTokensPerClause
    omega
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hClause

/-- Absolute token coordinate of the first opportunity belonging to the
second scheduled constraint. -/
def secondConstraintStartPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderFifthClausePaddingRun.sixthClauseSlotStartPolynomial verifier)
    (paddingPolynomial verifier)

def secondConstraintStart {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (secondConstraintStartPolynomial problem.verifier).eval problem.input.length

theorem secondConstraintStart_eq {language : Language}
    (problem : VerifierTableauProblem language) :
    secondConstraintStart problem =
      problem.formulaVariableSlotBound + 1 +
        problem.formulaClauseSlotsPerConstraint *
          problem.formulaTokensPerClause := by
  unfold secondConstraintStart secondConstraintStartPolynomial
  simp only [NatPolynomial.eval_add]
  change BuilderFifthClausePaddingRun.sixthClauseSlotStart problem +
      paddingCount problem = _
  rw [BuilderFifthClausePaddingRun.sixthClauseSlotStart_eq,
    paddingCount_eq_remaining_first_constraint]
  have hBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
      problem
  have hSlots : 5 ≤ problem.formulaClauseSlotsPerConstraint := by
    unfold VerifierTableauProblem.formulaClauseSlotsPerConstraint
    have hProduct : 9 ≤
        problem.formulaVariableSlotBound *
          problem.formulaVariableSlotBound :=
      Nat.mul_le_mul hBound hBound
    omega
  let remaining := problem.formulaClauseSlotsPerConstraint - 5
  have hDecompose :
      problem.formulaClauseSlotsPerConstraint = 5 + remaining := by
    unfold remaining
    omega
  rw [hDecompose]
  simp only [Nat.add_sub_cancel_left, Nat.add_mul, Nat.add_assoc]

theorem predecessorSlot_add_paddingCount
    {language : Language} (problem : VerifierTableauProblem language) :
    BuilderFifthClausePaddingRun.finalTokenSlot problem +
        paddingCount problem = secondConstraintStart problem := by
  rw [BuilderFifthClausePaddingRun.finalTokenSlot_eq_sixthClauseSlotStart,
    paddingCount_eq_remaining_first_constraint,
    secondConstraintStart_eq]
  have hBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
      problem
  have hSlots : 5 ≤ problem.formulaClauseSlotsPerConstraint := by
    unfold VerifierTableauProblem.formulaClauseSlotsPerConstraint
    have hProduct : 9 ≤
        problem.formulaVariableSlotBound *
          problem.formulaVariableSlotBound :=
      Nat.mul_le_mul hBound hBound
    omega
  let remaining := problem.formulaClauseSlotsPerConstraint - 5
  have hDecompose :
      problem.formulaClauseSlotsPerConstraint = 5 + remaining := by
    unfold remaining
    omega
  rw [hDecompose]
  simp only [Nat.add_sub_cancel_left, Nat.add_mul, Nat.add_assoc]

/-! ### Reused literal unary countdown loop -/


/-! ### Evaluator-loop-evaluator composition -/

def countEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (paddingPolynomial problem.verifier)

def targetEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (secondConstraintStartPolynomial problem.verifier)

def countdownTargetMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePaddingRun.PaddingCountdown.machine
    (targetEvaluator problem)

def paddingSuffixMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine (countEvaluator problem)
    (countdownTargetMachine problem)

/-- One literal finite rule table from raw input through every remaining
empty clause rectangle belonging to the first scheduled constraint. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderFifthClausePaddingRun.machine problem)
    (paddingSuffixMachine problem)

private theorem predecessor_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderFifthClausePaddingRun.machine problem) := by
  exact BuilderFifthClausePaddingRun.rule_source_ne_acceptState problem

private theorem countEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (countEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt (BuilderUnaryPolynomial.rule_source_lt_acceptState
    (paddingPolynomial problem.verifier) rule hRule)

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
    (secondConstraintStartPolynomial problem.verifier) rule hRule)

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      4432 +
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
          (BuilderFifthClausePaddingRun.paddingPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFifthClausePaddingRun.sixthClauseSlotStartPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (paddingPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (secondConstraintStartPolynomial problem.verifier) := by
  have hPredecessor := BuilderFifthClausePaddingRun.rules_length problem
  have hCount := BuilderUnaryPolynomial.rules_length
    (paddingPolynomial problem.verifier)
  have hTarget := BuilderUnaryPolynomial.rules_length
    (secondConstraintStartPolynomial problem.verifier)
  have hCountdown := BuilderFirstClausePaddingRun.PaddingCountdown.rules_length
  have hCountMachine :
      (BuilderUnaryPolynomial.machine
        (paddingPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (paddingPolynomial problem.verifier) := by
    simpa [BuilderUnaryPolynomial.machine] using hCount
  have hTargetMachine :
      (BuilderUnaryPolynomial.machine
        (secondConstraintStartPolynomial problem.verifier)).rules.length =
      BuilderUnaryPolynomial.ruleCount
        (secondConstraintStartPolynomial problem.verifier) := by
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
      (secondConstraintStartPolynomial problem.verifier))
    countdown_noRuleAtAccept
  have hSuffix := BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (countEvaluator problem) (countdownTargetMachine problem)
    (BuilderUnaryPolynomial.rules_pairwise_query_distinct
      (paddingPolynomial problem.verifier))
    hCountdownTarget (countEvaluator_noRuleAtAccept problem)
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (BuilderFifthClausePaddingRun.machine problem)
    (paddingSuffixMachine problem)
    (BuilderFifthClausePaddingRun.rules_pairwise_query_distinct problem)
    hSuffix (predecessor_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderFifthClausePaddingRun.machine problem)
    (paddingSuffixMachine problem)
    (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
      (countEvaluator problem) (countdownTargetMachine problem)
      (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
        BuilderFirstClausePaddingRun.PaddingCountdown.machine
          (targetEvaluator problem)
        (BuilderUnaryPolynomial.machine_acceptState_ne_rejectState
          (secondConstraintStartPolynomial problem.verifier))))

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderFifthClausePaddingRun.machine problem)
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
    (paddingPolynomial problem.verifier) problem.input.length

def countRootPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (BuilderUnaryPolynomial.rootPrefixPolynomial
    (paddingPolynomial problem.verifier)).eval problem.input.length

def countControllerPrefixLength {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  countRootPrefixLength problem - 1

def countOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (paddingPolynomial problem.verifier) problem.input
    (BuilderFifthClausePaddingRun.finalOutside problem)

def countTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (countOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem)

def countdownFinalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (countWord problem).take (countRootPrefixLength problem) ++
    List.replicate (paddingCount problem + 1)
      BuilderUnaryPolynomial.scratchEndSymbol ++
    (BuilderFifthClausePaddingRun.finalOutside problem).drop
      ((countWord problem).length + 1)

def countdownFinalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (countdownFinalOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem)

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (secondConstraintStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def countdownWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFirstClausePaddingRun.PaddingCountdown.loopSteps
    (countControllerPrefixLength problem)
    (paddingCount problem)

def suffixWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderUnaryPolynomial.workSteps
      (paddingPolynomial problem.verifier) problem.input + 1 +
    countdownWorkSteps problem + 1 +
    BuilderUnaryPolynomial.workSteps
      (secondConstraintStartPolynomial problem.verifier) problem.input

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFifthClausePaddingRun.workSteps problem + 1 +
    suffixWorkSteps problem

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (BuilderFourthClausePrefix.fourthClauseTokens problem)

theorem countEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (countEvaluator problem)
        (BuilderUnaryPolynomial.workSteps
          (paddingPolynomial problem.verifier) problem.input)
        (BuilderUnaryPolynomial.initialConfiguration
          (paddingPolynomial problem.verifier) problem.input
          (BuilderFifthClausePaddingRun.finalOutside problem)
          (BuilderFourthClausePrefix.fourthClauseTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (paddingPolynomial problem.verifier) problem.input
          (BuilderFifthClausePaddingRun.finalOutside problem)
          (BuilderFourthClausePrefix.fourthClauseTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (paddingPolynomial problem.verifier) problem.input
    (BuilderFifthClausePaddingRun.finalOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem)

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
  let polynomial := paddingPolynomial problem.verifier
  let scratch := countWord problem
  let outside := BuilderFifthClausePaddingRun.finalOutside problem
  rcases BuilderUnaryPolynomial.root_register_length polynomial
      problem.input.length with ⟨wordPrefix, hScratch, hPrefixLength⟩
  have hCountEval : polynomial.eval problem.input.length =
      paddingCount problem := by rfl
  rw [hCountEval] at hScratch
  have hPrefixLength' : wordPrefix.length + 1 =
      countRootPrefixLength problem := by
    simpa [polynomial, countRootPrefixLength] using hPrefixLength
  have hScratch' : scratch =
      wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
        List.replicate (paddingCount problem)
          BuilderUnaryPolynomial.unitSymbol := by
    simpa [scratch, countWord, polynomial] using hScratch
  have hPositive := paddingCount_positive problem
  cases hCount : paddingCount problem with
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
        (BuilderFourthClausePrefix.fourthClauseTokens problem) hPrefixSymbols
      have hFinalOutside : countdownFinalOutside problem =
          BuilderFirstClausePaddingRun.PaddingCountdown.finalOutside wordPrefix (remaining + 1) tail := by
        change scratch.take (countRootPrefixLength problem) ++
            List.replicate (paddingCount problem + 1)
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
          (secondConstraintStartPolynomial problem.verifier) problem.input)
        (BuilderUnaryPolynomial.initialConfiguration
          (secondConstraintStartPolynomial problem.verifier) problem.input
          (countdownFinalOutside problem)
          (BuilderFourthClausePrefix.fourthClauseTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (secondConstraintStartPolynomial problem.verifier) problem.input
          (countdownFinalOutside problem)
          (BuilderFourthClausePrefix.fourthClauseTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (secondConstraintStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem)

private theorem countdownTarget_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (countdownTargetMachine problem)
        (countdownWorkSteps problem + 1 +
          BuilderUnaryPolynomial.workSteps
            (secondConstraintStartPolynomial problem.verifier) problem.input)
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
    (secondConstraintStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem)
  let targetFinal := BuilderUnaryPolynomial.finalConfiguration
    (secondConstraintStartPolynomial problem.verifier) problem.input
    (countdownFinalOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem)
  have hCountdown : workRunExact? BuilderFirstClausePaddingRun.PaddingCountdown.machine
      (countdownWorkSteps problem) countdownInitial =
        some countdownFinal := by
    simpa [countdownInitial, countdownFinal] using
      countdown_workRunExact problem
  have hTarget : workRunExact? (targetEvaluator problem)
      (BuilderUnaryPolynomial.workSteps
        (secondConstraintStartPolynomial problem.verifier) problem.input)
      targetInitial = some targetFinal := by
    simpa [targetInitial, targetFinal] using
      targetEvaluator_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    BuilderFirstClausePaddingRun.PaddingCountdown.machine (targetEvaluator problem)
    (countdownWorkSteps problem)
    (BuilderUnaryPolynomial.workSteps
      (secondConstraintStartPolynomial problem.verifier) problem.input)
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
          (BuilderFifthClausePaddingRun.finalTape problem)) =
      some
        { state := (paddingSuffixMachine problem).acceptState,
          tape := finalTape problem } := by
  let countInitial := BuilderUnaryPolynomial.initialConfiguration
    (paddingPolynomial problem.verifier) problem.input
    (BuilderFifthClausePaddingRun.finalOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem)
  let countFinal := BuilderUnaryPolynomial.finalConfiguration
    (paddingPolynomial problem.verifier) problem.input
    (BuilderFifthClausePaddingRun.finalOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem)
  let suffixFinal : WorkConfiguration :=
    { state := (countdownTargetMachine problem).acceptState,
      tape := finalTape problem }
  have hCount : workRunExact? (countEvaluator problem)
      (BuilderUnaryPolynomial.workSteps
        (paddingPolynomial problem.verifier) problem.input)
      countInitial = some countFinal := by
    simpa [countInitial, countFinal] using countEvaluator_workRunExact problem
  have hTail : workRunExact? (countdownTargetMachine problem)
      (countdownWorkSteps problem + 1 +
        BuilderUnaryPolynomial.workSteps
          (secondConstraintStartPolynomial problem.verifier) problem.input)
      { state := (countdownTargetMachine problem).startState,
        tape := countFinal.tape } = some suffixFinal := by
    simpa [countFinal, suffixFinal, countTape, countOutside,
      BuilderUnaryPolynomial.finalConfiguration,
      workStartConfiguration] using countdownTarget_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (countEvaluator problem) (countdownTargetMachine problem)
    (BuilderUnaryPolynomial.workSteps
      (paddingPolynomial problem.verifier) problem.input)
    (countdownWorkSteps problem + 1 +
      BuilderUnaryPolynomial.workSteps
        (secondConstraintStartPolynomial problem.verifier) problem.input)
    countInitial countFinal suffixFinal hCount rfl hTail
  simpa [paddingSuffixMachine, countdownTargetMachine, targetEvaluator,
    countEvaluator, suffixWorkSteps, countInitial, suffixFinal,
    BuilderFifthClausePaddingRun.finalTape,
    BuilderFifthClausePaddingRun.finalOutside,
    BuilderUnaryPolynomial.initialConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration, Nat.add_assoc] using hCombined

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderFifthClausePaddingRun.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (BuilderFifthClausePaddingRun.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderFifthClausePaddingRun.machine problem) (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderFifthClausePaddingRun.machine problem)
      (paddingSuffixMachine problem))
    (BuilderFifthClausePaddingRun.workSteps problem)
    (workStartConfiguration (BuilderFifthClausePaddingRun.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderFifthClausePaddingRun.finalConfiguration problem)
    (BuilderFifthClausePaddingRun.workRunExact problem)
  simpa [machine, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hTransport

theorem launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderFifthClausePaddingRun.finalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration (paddingSuffixMachine problem)
          (BuilderFifthClausePaddingRun.finalTape problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderFifthClausePaddingRun.machine problem)
    (paddingSuffixMachine problem)
    (BuilderFifthClausePaddingRun.finalTape problem)
  simpa [machine, BuilderFifthClausePaddingRun.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
/-- Every raw input follows the complete predecessor trace, evaluates the
remaining padding count, executes the input-dependent unary loop exactly, and
materializes the second-constraint boundary coordinate. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let predecessorInitial := workStartConfiguration
    (BuilderFifthClausePaddingRun.machine problem)
    (rawInputWorkTape problem.input)
  let predecessorFinal := BuilderFifthClausePaddingRun.finalConfiguration
    problem
  let suffixFinal : WorkConfiguration :=
    { state := (paddingSuffixMachine problem).acceptState,
      tape := finalTape problem }
  have hPredecessor : workRunExact?
      (BuilderFifthClausePaddingRun.machine problem)
      (BuilderFifthClausePaddingRun.workSteps problem)
      predecessorInitial = some predecessorFinal := by
    simpa [predecessorInitial, predecessorFinal] using
      BuilderFifthClausePaddingRun.workRunExact problem
  have hSuffix : workRunExact? (paddingSuffixMachine problem)
      (suffixWorkSteps problem)
      { state := (paddingSuffixMachine problem).startState,
        tape := predecessorFinal.tape } = some suffixFinal := by
    simpa [predecessorFinal, suffixFinal,
      BuilderFifthClausePaddingRun.finalConfiguration,
      workStartConfiguration] using paddingSuffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderFifthClausePaddingRun.machine problem)
    (paddingSuffixMachine problem)
    (BuilderFifthClausePaddingRun.workSteps problem)
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

private theorem scheduledShapeConstraint_entry_exactlyOne
    {language : Language} (problem : VerifierTableauProblem language)
    (entry : Option (LocalConstraint problem.FormulaWidth))
    (hEntry : entry ∈ problem.scheduledShapeConstraints) :
    ∃ variables : List (Fin problem.FormulaWidth),
      entry = some (.exactlyOne variables) := by
  unfold VerifierTableauProblem.scheduledShapeConstraints at hEntry
  simp only [List.mem_flatMap] at hEntry
  rcases hEntry with ⟨time, _hTime, hRow⟩
  rw [List.mem_append] at hRow
  rcases hRow with hSymbol | hHeadState
  · rcases List.mem_map.mp hSymbol with ⟨position, _hPosition, hEqual⟩
    subst entry
    exact ⟨problem.symbolVariables time position, rfl⟩
  · simp at hHeadState
    rcases hHeadState with hHead | hState
    · subst entry
      exact ⟨problem.headVariables time, rfl⟩
    · subst entry
      exact ⟨problem.stateVariables time, rfl⟩

private theorem scheduledShapeConstraints_starts_twoExactlyOne
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ nextVariables rest,
      problem.scheduledShapeConstraints =
        some (problem.symbolShapeAt time position) ::
          some (.exactlyOne nextVariables) :: rest := by
  dsimp
  rcases scheduledShapeConstraints_starts_firstSymbol problem with
    ⟨rest, hRest⟩
  have hTime : 1 ≤ problem.dimensions.timeCount :=
    Nat.succ_le_iff.mpr problem.dimensions.timeCount_positive
  have hTape : 1 ≤
      problem.dimensions.tapeWidth problem.tableauInputMode :=
    Nat.succ_le_iff.mpr
      (problem.dimensions.tapeWidth_positive problem.tableauInputMode)
  have hThree : 3 ≤ problem.scheduledShapeConstraints.length := by
    rw [problem.scheduledShapeConstraints_length]
    have hWidth : 3 ≤
        problem.dimensions.tapeWidth problem.tableauInputMode + 2 := by
      omega
    have hProduct := Nat.mul_le_mul hTime hWidth
    simpa using hProduct
  have hRestLength : 1 ≤ rest.length := by
    rw [hRest] at hThree
    simp only [List.length_cons] at hThree
    omega
  cases rest with
  | nil => simp at hRestLength
  | cons next tail =>
      have hNextMem : next ∈ problem.scheduledShapeConstraints := by
        rw [hRest]
        simp
      rcases scheduledShapeConstraint_entry_exactlyOne problem next hNextMem with
        ⟨nextVariables, hNext⟩
      subst next
      exact ⟨nextVariables, tail, hRest⟩

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

private theorem formulaConstraintSchedule_starts_twoExactlyOne
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ nextVariables rest,
      problem.formulaConstraintSchedule =
        some (problem.symbolShapeAt time position) ::
          some (.exactlyOne nextVariables) :: rest := by
  dsimp
  rcases scheduledShapeConstraints_starts_twoExactlyOne problem with
    ⟨nextVariables, rest, hRest⟩
  refine ⟨nextVariables,
    rest ++ problem.scheduledInitialConstraints ++
      problem.scheduledControlConstraints ++
      problem.scheduledPreservationConstraints ++
      [some (.require
        (problem.stateLiteral problem.finalTime problem.acceptingState))], ?_⟩
  unfold VerifierTableauProblem.formulaConstraintSchedule
  rw [hRest]
  simp [List.append_assoc]

private theorem scheduledExactlyOneClauses_starts_atLeast
    {language : Language} (problem : VerifierTableauProblem language)
    (variables : List (Fin problem.FormulaWidth)) :
    ∃ rest,
      problem.scheduledConstraintClauses (some (.exactlyOne variables)) =
        some (atLeastOneBoundedClause variables) :: rest := by
  refine ⟨(atMostOneBoundedClauses variables).map some ++
      List.replicate
        (problem.formulaClauseSlotsPerConstraint -
          (exactlyOneBoundedClauses variables).length) none, ?_⟩
  simp [VerifierTableauProblem.scheduledConstraintClauses,
    FormulaSchedule.pad, LocalConstraint.emit, exactlyOneBoundedClauses]

private theorem formulaClauseSchedule_starts_firstConstraint_then_nextClause
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ left right thirdLeft thirdRight fourthLeft fourthRight :
        Fin problem.FormulaWidth, ∃ nextVariables rest,
      problem.formulaClauseSchedule =
        some (atLeastOneBoundedClause
          (problem.symbolVariables time position)) ::
        some (excludeBoundedPairClause left right) ::
        some (excludeBoundedPairClause thirdLeft thirdRight) ::
        some (excludeBoundedPairClause fourthLeft fourthRight) ::
        List.replicate
          (problem.formulaClauseSlotsPerConstraint - 4) none ++
        some (atLeastOneBoundedClause nextVariables) :: rest ∧
      left.val = 0 ∧ right.val = 1 ∧
        thirdLeft.val = 0 ∧ thirdRight.val = 2 ∧
        fourthLeft.val = 1 ∧ fourthRight.val = 2 := by
  dsimp
  rcases formulaConstraintSchedule_starts_twoExactlyOne problem with
    ⟨nextVariables, constraints, hConstraints⟩
  rcases scheduledExactlyOneClauses_starts_atLeast problem nextVariables with
    ⟨nextClauses, hNextClauses⟩
  have hVariableBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
      problem
  let rest : List (Option (BoundedClause problem.FormulaWidth)) :=
    nextClauses ++
      constraints.flatMap problem.scheduledConstraintClauses
  rw [VerifierTableauProblem.formulaClauseSchedule, hConstraints]
  simp only [List.flatMap_cons]
  rw [hNextClauses]
  unfold VerifierTableauProblem.symbolShapeAt
  dsimp [VerifierTableauProblem.scheduledConstraintClauses,
    LocalConstraint.emit, exactlyOneBoundedClauses, FormulaSchedule.pad,
    atMostOneBoundedClauses, excludeBoundedWithClauses]
  simp only [VerifierTableauProblem.symbolVariables, tapeSymbols,
    List.map_cons, List.map_nil,
    atMostOneBoundedClauses, excludeBoundedWithClauses,
    List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, List.append_nil]
  let firstTime : Fin problem.dimensions.timeCount :=
    ⟨0, problem.dimensions.timeCount_positive⟩
  let firstPosition : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode) :=
    ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
  let blankIndex : Fin problem.FormulaWidth :=
    (problem.symbolLiteral firstTime firstPosition .blank).index
  let zeroIndex : Fin problem.FormulaWidth :=
    (problem.symbolLiteral firstTime firstPosition .zero).index
  let oneIndex : Fin problem.FormulaWidth :=
    (problem.symbolLiteral firstTime firstPosition .one).index
  refine ⟨blankIndex, zeroIndex, blankIndex, oneIndex,
    zeroIndex, oneIndex, nextVariables, rest,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [rest, blankIndex, zeroIndex, oneIndex, firstTime,
      firstPosition]
  · simp [VerifierTableauProblem.symbolLiteral,
      blankIndex, firstTime, firstPosition,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      zeroIndex, firstTime, firstPosition,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      blankIndex, firstTime, firstPosition,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      oneIndex, firstTime, firstPosition,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      zeroIndex, firstTime, firstPosition,
      VariableLayout.symbolVariable, VariableLayout.symbolLocalIndex,
      VariableLayout.symbolBlock, VariableBlock.index,
      VariableLayout.flattenTwo, VariableLayout.tapeSymbolCode]
  · simp [VerifierTableauProblem.symbolLiteral,
      oneIndex, firstTime, firstPosition,
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

private theorem flatMap_empty_clause_rectangles
    {language : Language} (problem : VerifierTableauProblem language) :
    ∀ count,
      (List.replicate count
          (none : Option (BoundedClause problem.FormulaWidth))).flatMap
          problem.scheduledClauseTokens =
        List.replicate
          (count * problem.formulaTokensPerClause) none := by
  intro count
  induction count with
  | zero => simp
  | succ count ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih]
      dsimp [VerifierTableauProblem.scheduledClauseTokens]
      rw [List.replicate_append_replicate]
      congr 1
      simp [Nat.succ_mul, Nat.add_comm]

private theorem scheduledClauseTokens_starts_sep
    {language : Language} (problem : VerifierTableauProblem language)
    (clause : BoundedClause problem.FormulaWidth) :
    ∃ rest,
      problem.scheduledClauseTokens (some clause) =
        some CNFToken.sep :: rest := by
  refine ⟨List.map some
        (encodeLiteralListTokens (BoundedClause.emit clause) ++ [.finish]) ++
      List.replicate
        (problem.formulaTokensPerClause -
          (encodeClauseTokens (BoundedClause.emit clause)).length) none, ?_⟩
  simp [VerifierTableauProblem.scheduledClauseTokens, FormulaSchedule.pad,
    encodeClauseTokens]

private theorem formulaClauseTokens_firstConstraint_padding_then_sep
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
        [some CNFToken.sep,
         some CNFToken.f, some CNFToken.t, some CNFToken.f,
         some CNFToken.f, some CNFToken.t, some CNFToken.t,
        some CNFToken.f, some CNFToken.finish] ++
        List.replicate (problem.formulaTokensPerClause - 9) none ++
        List.replicate
          ((problem.formulaClauseSlotsPerConstraint - 4) *
            problem.formulaTokensPerClause) none ++
        some CNFToken.sep :: rest := by
  rcases formulaClauseSchedule_starts_firstConstraint_then_nextClause problem with
    ⟨left, right, thirdLeft, thirdRight, fourthLeft, fourthRight,
      nextVariables, clauses, hClauses, hLeft, hRight, hThirdLeft, hThirdRight,
      hFourthLeft, hFourthRight⟩
  rcases scheduledClauseTokens_starts_sep problem
      (atLeastOneBoundedClause nextVariables) with
    ⟨nextTokens, hNextTokens⟩
  rw [hClauses]
  simp only [List.flatMap_cons, List.flatMap_append]
  rw [flatMap_empty_clause_rectangles problem, hNextTokens]
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
  refine ⟨nextTokens ++ clauses.flatMap problem.scheduledClauseTokens, ?_⟩
  simp [BoundedClause.emit, excludeBoundedPairClause, falseLiteral,
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
opportunity in the remaining empty clause rectangles of the first scheduled
constraint. -/
theorem paddingSlot_direct_eq_padding {language : Language}
    (problem : VerifierTableauProblem language) (offset : Nat)
    (hOffset : offset < paddingCount problem) :
    problem.formulaTokenSlotDirect
        (BuilderFifthClausePaddingRun.finalTokenSlot problem + offset) =
      some none := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_firstConstraint_padding_then_sep problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses,
    BuilderFifthClausePaddingRun.finalTokenSlot_eq_sixthClauseSlotStart]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
          problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  have hCount :=
    paddingCount_eq_remaining_first_constraint problem
  have hWidth := formulaTokensPerClause_at_least_twelve problem
  have hVariableBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
      problem
  have hSlots : 5 ≤ problem.formulaClauseSlotsPerConstraint := by
    unfold VerifierTableauProblem.formulaClauseSlotsPerConstraint
    have hProduct : 9 ≤
        problem.formulaVariableSlotBound *
          problem.formulaVariableSlotBound :=
      Nat.mul_le_mul hVariableBound hVariableBound
    omega
  have hEmptyCount :
      (problem.formulaClauseSlotsPerConstraint - 4) *
          problem.formulaTokensPerClause =
        problem.formulaTokensPerClause + paddingCount problem := by
    rw [hCount]
    have hRemaining :
        problem.formulaClauseSlotsPerConstraint - 4 =
          (problem.formulaClauseSlotsPerConstraint - 5) + 1 := by
      omega
    rw [hRemaining]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  simp only [List.append_assoc]
  rw [List.getElem?_append, hHeader, if_neg (by omega)]
  rw [show problem.formulaVariableSlotBound + 1 +
      5 * problem.formulaTokensPerClause + offset -
      (problem.formulaVariableSlotBound + 1) =
        5 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 5 * problem.formulaTokensPerClause + offset -
      11 = (problem.formulaTokensPerClause - 11) +
        4 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 11) +
      4 * problem.formulaTokensPerClause + offset -
      (problem.formulaTokensPerClause - 11) =
        4 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 4 * problem.formulaTokensPerClause + offset -
      7 = (problem.formulaTokensPerClause - 7) +
        3 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 7) +
      3 * problem.formulaTokensPerClause + offset -
      (problem.formulaTokensPerClause - 7) =
        3 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 3 * problem.formulaTokensPerClause + offset -
      8 = (problem.formulaTokensPerClause - 8) +
        2 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 8) +
      2 * problem.formulaTokensPerClause + offset -
      (problem.formulaTokensPerClause - 8) =
        2 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 2 * problem.formulaTokensPerClause + offset - 9 =
      (problem.formulaTokensPerClause - 9) +
        problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 9) +
      problem.formulaTokensPerClause + offset -
      (problem.formulaTokensPerClause - 9) =
        problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_pos (by rw [hEmptyCount]; omega)]
  rw [List.getElem?_replicate, if_pos (by omega)]

/-- The exact target materialized after the countdown is the separator that
begins the second scheduled constraint. -/
theorem secondConstraintStart_direct_eq_sep {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect (secondConstraintStart problem) =
      some (some CNFToken.sep) := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_firstConstraint_padding_then_sep problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses, secondConstraintStart_eq]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
          problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  have hWidth := formulaTokensPerClause_at_least_twelve problem
  have hVariableBound :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
      problem
  have hSlots : 4 ≤ problem.formulaClauseSlotsPerConstraint := by
    unfold VerifierTableauProblem.formulaClauseSlotsPerConstraint
    have hProduct : 9 ≤
        problem.formulaVariableSlotBound *
          problem.formulaVariableSlotBound :=
      Nat.mul_le_mul hVariableBound hVariableBound
    omega
  let emptyCount :=
    (problem.formulaClauseSlotsPerConstraint - 4) *
      problem.formulaTokensPerClause
  have hDecompose :
      problem.formulaClauseSlotsPerConstraint *
          problem.formulaTokensPerClause =
        4 * problem.formulaTokensPerClause + emptyCount := by
    have hSlotsDecompose :
        problem.formulaClauseSlotsPerConstraint =
          4 + (problem.formulaClauseSlotsPerConstraint - 4) := by
      omega
    rw [hSlotsDecompose]
    simp only [Nat.add_mul]
    rfl
  simp only [List.append_assoc]
  rw [List.getElem?_append, hHeader, if_neg (by omega)]
  rw [show problem.formulaVariableSlotBound + 1 +
      problem.formulaClauseSlotsPerConstraint *
          problem.formulaTokensPerClause -
      (problem.formulaVariableSlotBound + 1) =
        4 * problem.formulaTokensPerClause + emptyCount by
          rw [hDecompose]
          omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 4 * problem.formulaTokensPerClause + emptyCount -
      11 = (problem.formulaTokensPerClause - 11) +
        3 * problem.formulaTokensPerClause + emptyCount by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 11) +
      3 * problem.formulaTokensPerClause + emptyCount -
      (problem.formulaTokensPerClause - 11) =
        3 * problem.formulaTokensPerClause + emptyCount by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 3 * problem.formulaTokensPerClause + emptyCount - 7 =
      (problem.formulaTokensPerClause - 7) +
        2 * problem.formulaTokensPerClause + emptyCount by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 7) +
      2 * problem.formulaTokensPerClause + emptyCount -
      (problem.formulaTokensPerClause - 7) =
        2 * problem.formulaTokensPerClause + emptyCount by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 2 * problem.formulaTokensPerClause + emptyCount - 8 =
      (problem.formulaTokensPerClause - 8) +
        problem.formulaTokensPerClause + emptyCount by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 8) +
      problem.formulaTokensPerClause + emptyCount -
      (problem.formulaTokensPerClause - 8) =
        problem.formulaTokensPerClause + emptyCount by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause + emptyCount - 9 =
      (problem.formulaTokensPerClause - 9) + emptyCount by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 9) + emptyCount -
      (problem.formulaTokensPerClause - 9) = emptyCount by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [show (problem.formulaClauseSlotsPerConstraint - 4) *
      problem.formulaTokensPerClause = emptyCount by rfl]
  rw [if_neg (by omega)]
  rw [show emptyCount - emptyCount = 0 by omega]
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
      offset + count ≤ paddingCount problem →
      specificationRun problem count
          ⟨BuilderFifthClausePaddingRun.finalTokenSlot problem + offset⟩ =
        some ([],
          ⟨BuilderFifthClausePaddingRun.finalTokenSlot problem +
            offset + count⟩) := by
  intro count
  induction count with
  | zero =>
      intro offset _hBound
      simp [specificationRun]
  | succ count ih =>
      intro offset hBound
      have hOffset : offset < paddingCount problem := by omega
      have hStep : VerifierTableauProblem.FormulaTokenCursor.step problem
          ⟨BuilderFifthClausePaddingRun.finalTokenSlot problem + offset⟩ =
        some (none,
          ⟨BuilderFifthClausePaddingRun.finalTokenSlot problem + offset + 1⟩) := by
        unfold VerifierTableauProblem.FormulaTokenCursor.step
        rw [paddingSlot_direct_eq_padding problem offset hOffset]
      have hTail := ih (offset + 1) (by omega)
      rw [specificationRun, hStep]
      rw [show BuilderFifthClausePaddingRun.finalTokenSlot problem +
          offset + 1 =
        BuilderFifthClausePaddingRun.finalTokenSlot problem +
          (offset + 1) by omega]
      simp only
      rw [hTail]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The repeated specification cursor emits no token while traversing the
entire remaining padding region of the first scheduled constraint and stops
exactly at the second scheduled constraint. -/
theorem specification_padding_run {language : Language}
    (problem : VerifierTableauProblem language) :
    specificationRun problem (paddingCount problem)
        ⟨BuilderFifthClausePaddingRun.finalTokenSlot problem⟩ =
      some ([], ⟨secondConstraintStart problem⟩) := by
  have hRun := specificationRun_padding_from_offset problem
    (paddingCount problem) 0 (by omega)
  rw [Nat.add_zero] at hRun
  rw [predecessorSlot_add_paddingCount problem] at hRun
  exact hRun

/-- The next specification action after the padding run observes the
separator that begins the second scheduled constraint. -/
theorem specification_target_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨secondConstraintStart problem⟩ =
      some (some CNFToken.sep,
        ⟨secondConstraintStart problem + 1⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [secondConstraintStart_direct_eq_sep]

theorem finalTokenBits_eq_encodedFormula_fourthClause
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (BuilderFourthClausePrefix.fourthClauseTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 36)) :=
  BuilderFifthClausePaddingRun.finalTokenBits_eq_encodedFormula_fourthClause
    problem

def finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  secondConstraintStart problem

theorem finalTokenSlot_eq_secondConstraintStart {language : Language}
    (problem : VerifierTableauProblem language) :
    finalTokenSlot problem = problem.formulaVariableSlotBound + 1 +
      problem.formulaClauseSlotsPerConstraint *
        problem.formulaTokensPerClause := by
  exact secondConstraintStart_eq problem

theorem finalOutside_contains_finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.root_register_length
      (secondConstraintStartPolynomial problem.verifier) problem.input.length with
    ⟨wordPrefix, hScratch, _hPrefixLength⟩
  refine ⟨wordPrefix,
    (countdownFinalOutside problem).drop
      ((BuilderUnaryPolynomial.scratchWord
        (secondConstraintStartPolynomial problem.verifier)
        problem.input.length).length + 1), ?_⟩
  unfold finalOutside BuilderUnaryPolynomial.finalOutsideLeft
    BuilderUnaryPolynomial.overlayScratch finalTokenSlot secondConstraintStart
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
  let count := paddingPolynomial verifier
  let rootPrefix := BuilderUnaryPolynomial.rootPrefixPolynomial count
  .add
    (.mul count
      (.add (scalePolynomial 2 rootPrefix) (.constant 8)))
    (.mul count count)

/-- External raw-transition bound for the predecessor, three bridges, both
unary evaluators, and the complete input-dependent countdown. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let count := paddingPolynomial verifier
  let target := secondConstraintStartPolynomial verifier
  .add (BuilderFifthClausePaddingRun.rawTimeBound verifier)
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
      paddingCount problem *
          (2 * countRootPrefixLength problem + 8) +
        paddingCount problem * paddingCount problem := by
  simp [countdownBoundPolynomial, scalePolynomial,
    NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, paddingCount,
    countRootPrefixLength]

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderFifthClausePaddingRun.rawTimeBound problem.verifier).eval
          problem.input.length + 18 +
        6 * BuilderUnaryPolynomial.workSteps
          (paddingPolynomial problem.verifier) problem.input +
        6 *
          (paddingCount problem *
              (2 * countRootPrefixLength problem + 8) +
            paddingCount problem * paddingCount problem) +
        6 * BuilderUnaryPolynomial.workSteps
          (secondConstraintStartPolynomial problem.verifier) problem.input := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, scalePolynomial,
    BuilderUnaryPolynomial.workTimePolynomial_eval]
  rw [countdownBoundPolynomial_eval]
  omega

private theorem countdownWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    countdownWorkSteps problem ≤
      paddingCount problem *
          (2 * countRootPrefixLength problem + 8) +
        paddingCount problem * paddingCount problem := by
  have hLoop := BuilderFirstClausePaddingRun.PaddingCountdown.loopSteps_le
    (countControllerPrefixLength problem) (paddingCount problem)
  rcases BuilderUnaryPolynomial.root_register_length
      (paddingPolynomial problem.verifier) problem.input.length with
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
    (paddingCount problem) hInside
  unfold countdownWorkSteps
  exact Nat.le_trans hLoop (Nat.add_le_add_right hScaled _)

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPredecessor := BuilderFifthClausePaddingRun.rawTimeBound_le problem
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
      (BuilderFifthClausePaddingRun.machine problem)
      (paddingSuffixMachine problem) config
  simpa [machine] using hHalted

/-- The sixth-clause-slot endpoint is globally nonhalting until the outer
bridge launches the remaining-first-constraint padding evaluator. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFifthClausePaddingRun.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderFifthClausePaddingRun.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (BuilderFifthClausePaddingRun.finalConfiguration problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_prefix_false problem
      (BuilderFifthClausePaddingRun.finalConfiguration problem))

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

end BuilderFirstConstraintPaddingRun

end CookLevin

end PNP.Concrete
