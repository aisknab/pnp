/-
Copyright (c) 2026 PNP Labs.

The fourth width-dependent padding-or-unary opportunity after the first
literal of the second canonical Cook--Levin constraint.

The literal work table in this file evaluates the represented tableau width
and uses the existing unary-root controller to distinguish width one from a
wider tableau.  At width one it consumes one in-range padding opportunity
without changing the formula output.  At every wider width it enters the
already-audited token appender at its `T` state and emits the second literal's
fourth unary unit.  Both branches then materialize the following formula
coordinate.  No host-side schedule lookup or caller-supplied branch
certificate is used.

This processes exactly one additional schedule opportunity.  It does not
process the following padding or terminating `F`, complete the second literal
at wider widths, traverse the second constraint, implement a general schedule
cursor, complete the formula builder, or establish P = NP.
-/

import PNP.Concrete.CookLevinBuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep

namespace PNP.Concrete

namespace CookLevin

namespace BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep

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

def opportunitySlotPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.opportunitySlotPolynomial
      verifier)
    (.constant 1)

def opportunitySlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  (opportunitySlotPolynomial problem.verifier).eval problem.input.length

theorem opportunitySlot_eq_secondConstraintStart_add_eleven
    {language : Language} (problem : VerifierTableauProblem language) :
    opportunitySlot problem =
      problem.formulaVariableSlotBound + 1 +
        problem.formulaClauseSlotsPerConstraint *
          problem.formulaTokensPerClause + 11 := by
  unfold opportunitySlot opportunitySlotPolynomial
  rw [NatPolynomial.eval_add, NatPolynomial.eval_constant]
  change
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.opportunitySlot
        problem +
      1 = _
  rw [
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.opportunitySlot_eq_secondConstraintStart_add_ten]

/-! ### Sequential evaluator/branch/evaluator composition -/

def widthEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine (widthPolynomial problem)

def targetEvaluator {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderUnaryPolynomial.machine
    (opportunitySlotPolynomial problem.verifier)

def widthBranchMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (widthEvaluator problem)
    BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine

def suffixMachine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (widthBranchMachine problem) (targetEvaluator problem)

def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
    (suffixMachine problem)

private theorem predecessor_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem) := by
  exact
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.rule_source_ne_acceptState
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
      BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine :=
  BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rule_source_ne_acceptState

private theorem targetEvaluator_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (targetEvaluator problem) := by
  intro rule hRule
  exact Nat.ne_of_lt
    (BuilderUnaryPolynomial.rule_source_lt_acceptState
      (opportunitySlotPolynomial problem.verifier) rule hRule)

private theorem widthBranch_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (widthBranchMachine problem) := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (widthEvaluator problem)
    BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine
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
      5764 +
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
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintFirstLiteralSuccessorTokenStep.widthPolynomial
            problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintFirstLiteralSuccessorTokenStep.successorTokenSlotPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintPaddingOrUnaryOpportunityStep.widthPolynomial
            problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintPaddingOrUnaryOpportunityStep.opportunitySlotPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.widthPolynomial
            problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.opportunitySlotPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.widthPolynomial
            problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.opportunitySlotPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount (widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (opportunitySlotPolynomial problem.verifier) := by
  have hPredecessor :=
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.rules_length problem
  have hWidth := BuilderUnaryPolynomial.rules_length (widthPolynomial problem)
  have hTarget := BuilderUnaryPolynomial.rules_length
    (opportunitySlotPolynomial problem.verifier)
  have hBranch := BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_length
  have hLaunch : ∀ source target,
      (launchRules source target).length = 9 := by
    intro source target
    rfl
  unfold machine suffixMachine widthBranchMachine
    BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
    BuilderFirstClausePrefix.WorkChain.bridgeRules
  simp only [List.length_append, List.length_map, widthEvaluator,
    targetEvaluator, BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine,
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
      (widthEvaluator problem)
      BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine
      (BuilderUnaryPolynomial.rules_pairwise_query_distinct
        (widthPolynomial problem))
      BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.rules_pairwise_query_distinct
      (widthEvaluator_noRuleAtAccept problem)
  have hSuffix :=
    BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
      (widthBranchMachine problem) (targetEvaluator problem)
      hWidthBranch
      (BuilderUnaryPolynomial.rules_pairwise_query_distinct
        (opportunitySlotPolynomial problem.verifier))
      (widthBranch_noRuleAtAccept problem)
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
    (suffixMachine problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.rules_pairwise_query_distinct
      problem)
    hSuffix (predecessor_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
    (suffixMachine problem)
    (BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
      (widthBranchMachine problem) (targetEvaluator problem)
      (BuilderUnaryPolynomial.machine_acceptState_ne_rejectState
        (opportunitySlotPolynomial problem.verifier)))

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
    (suffixMachine problem) (suffix_noRuleAtAccept problem) rule hRule

/-! ### Exact workspace geometry -/

def opportunityOutput {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  if width problem = 1 then [] else [.t]

def secondConstraintFourthPaddingOrUnaryTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
      problem ++
    opportunityOutput problem

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
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalOutside problem)

def widthTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (widthOutside problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
      problem)

def controllerFinalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (widthWord problem).take (widthRootPrefixLength problem) ++
    List.replicate (width problem - 1)
      BuilderUnaryPolynomial.unitSymbol ++
    [BuilderUnaryPolynomial.scratchEndSymbol,
     BuilderUnaryPolynomial.scratchEndSymbol] ++
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalOutside problem).drop
      ((widthWord problem).length + 1)

def branchFinalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input
    (controllerFinalOutside problem)
    (secondConstraintFourthPaddingOrUnaryTokens problem)

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.finalOutsideLeft
    (opportunitySlotPolynomial problem.verifier) problem.input
    (controllerFinalOutside problem)

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (secondConstraintFourthPaddingOrUnaryTokens problem)

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
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
      problem)

def branchWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  controllerWorkSteps problem + 1 +
    if width problem = 1 then 0 else appenderWorkSteps problem

def targetWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderUnaryPolynomial.workSteps
    (opportunitySlotPolynomial problem.verifier) problem.input

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workSteps problem + 1 +
    widthWorkSteps problem + 1 +
    branchWorkSteps problem + 1 +
    targetWorkSteps problem

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem)
    (secondConstraintFourthPaddingOrUnaryTokens problem)

theorem widthEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (widthEvaluator problem) (widthWorkSteps problem)
        (BuilderUnaryPolynomial.initialConfiguration
          (widthPolynomial problem) problem.input
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalOutside
            problem)
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
            problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (widthPolynomial problem) problem.input
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalOutside
            problem)
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
            problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (widthPolynomial problem) problem.input
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalOutside problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
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

theorem optionalAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine (branchWorkSteps problem)
        (workStartConfiguration BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine
          (widthTape problem)) =
      some
        { state := BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine.acceptState
          tape := branchFinalTape problem } := by
  let polynomial := widthPolynomial problem
  let scratch := widthWord problem
  let outside :=
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalOutside problem
  let output :=
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
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
      have hRun := BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.workRunExact problem.input
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
      cases remaining with
      | zero =>
          have hWidthOne : width problem = 1 := by omega
          have hBranchWorkSteps :
              branchWorkSteps problem = controllerWorkSteps problem + 1 := by
            rw [branchWorkSteps, if_pos hWidthOne, Nat.add_zero]
          have hOpportunityOutput : opportunityOutput problem = [] := by
            rw [opportunityOutput, if_pos hWidthOne]
          simpa [hBranchWorkSteps, controllerWorkSteps,
            widthControllerPrefixLength, ← hPrefixLength', hWidth,
            appenderWorkSteps, widthTape, branchFinalTape,
            secondConstraintFourthPaddingOrUnaryTokens, hOpportunityOutput,
            hWidthOutside, hFinalOutside,
            BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine,
            BuilderCompleteHeader.HeaderController.machine,
            BuilderTokenAppender.finalConfiguration, output,
            BuilderCompleteHeader.HeaderController.initialConfiguration,
            workStartConfiguration, renameConfiguration] using hRun
      | succ rest =>
          have hWidthNotOne : width problem ≠ 1 := by omega
          have hBranchWorkSteps :
              branchWorkSteps problem =
                controllerWorkSteps problem + 1 +
                  appenderWorkSteps problem := by
            rw [branchWorkSteps, if_neg hWidthNotOne]
          have hOpportunityOutput :
              opportunityOutput problem = [CNFToken.t] := by
            rw [opportunityOutput, if_neg hWidthNotOne]
          simpa [hBranchWorkSteps, controllerWorkSteps,
            widthControllerPrefixLength, ← hPrefixLength', hWidth,
            appenderWorkSteps, widthTape, branchFinalTape,
            secondConstraintFourthPaddingOrUnaryTokens, hOpportunityOutput,
            hWidthOutside, hFinalOutside,
            BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine,
            BuilderCompleteHeader.HeaderController.machine,
            BuilderTokenAppender.finalConfiguration, output,
            BuilderCompleteHeader.HeaderController.initialConfiguration,
            workStartConfiguration, renameConfiguration] using hRun

theorem targetEvaluator_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (targetEvaluator problem) (targetWorkSteps problem)
        (BuilderUnaryPolynomial.initialConfiguration
          (opportunitySlotPolynomial problem.verifier) problem.input
          (controllerFinalOutside problem)
          (secondConstraintFourthPaddingOrUnaryTokens problem)) =
      some
        (BuilderUnaryPolynomial.finalConfiguration
          (opportunitySlotPolynomial problem.verifier) problem.input
          (controllerFinalOutside problem)
          (secondConstraintFourthPaddingOrUnaryTokens problem)) := by
  exact BuilderUnaryPolynomial.workRunExact
    (opportunitySlotPolynomial problem.verifier) problem.input
    (controllerFinalOutside problem)
    (secondConstraintFourthPaddingOrUnaryTokens problem)

private theorem widthBranch_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (widthBranchMachine problem)
        (widthWorkSteps problem + 1 + branchWorkSteps problem)
        (workStartConfiguration (widthBranchMachine problem)
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTape
            problem)) =
      some
        { state := (widthBranchMachine problem).acceptState
          tape := branchFinalTape problem } := by
  let widthInitial := BuilderUnaryPolynomial.initialConfiguration
    (widthPolynomial problem) problem.input
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalOutside problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
      problem)
  let widthFinal := BuilderUnaryPolynomial.finalConfiguration
    (widthPolynomial problem) problem.input
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalOutside problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
      problem)
  let branchInitial := workStartConfiguration BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine
    (widthTape problem)
  let branchFinal : WorkConfiguration :=
    { state := BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine.acceptState
      tape := branchFinalTape problem }
  have hWidth : workRunExact? (widthEvaluator problem)
      (widthWorkSteps problem) widthInitial = some widthFinal := by
    simpa [widthInitial, widthFinal] using
      widthEvaluator_workRunExact problem
  have hBranch : workRunExact? BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine
      (branchWorkSteps problem) branchInitial = some branchFinal := by
    simpa [branchInitial, branchFinal] using
      optionalAppender_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (widthEvaluator problem) BuilderSecondConstraintPaddingOrUnaryOpportunityStep.WidthOptionalAppender.machine
    (widthWorkSteps problem) (branchWorkSteps problem)
    widthInitial widthFinal branchFinal hWidth (by rfl)
    hBranch
  simpa [widthBranchMachine, widthInitial, branchFinal,
    widthEvaluator, BuilderUnaryPolynomial.initialConfiguration,
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTape,
    BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

theorem suffix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (suffixMachine problem)
        (widthWorkSteps problem + 1 + branchWorkSteps problem + 1 +
          targetWorkSteps problem)
        (workStartConfiguration (suffixMachine problem)
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTape
            problem)) =
      some
        { state := (suffixMachine problem).acceptState
          tape := finalTape problem } := by
  let widthBranchInitial := workStartConfiguration
    (widthBranchMachine problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTape problem)
  let widthBranchFinal : WorkConfiguration :=
    { state := (widthBranchMachine problem).acceptState
      tape := branchFinalTape problem }
  let targetInitial := BuilderUnaryPolynomial.initialConfiguration
    (opportunitySlotPolynomial problem.verifier) problem.input
    (controllerFinalOutside problem)
    (secondConstraintFourthPaddingOrUnaryTokens problem)
  let targetFinal := BuilderUnaryPolynomial.finalConfiguration
    (opportunitySlotPolynomial problem.verifier) problem.input
    (controllerFinalOutside problem)
    (secondConstraintFourthPaddingOrUnaryTokens problem)
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
        (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workSteps problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (workStartConfiguration
            (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
            (rawInputWorkTape problem.input))) =
      some
        (renameConfiguration
          BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalConfiguration
            problem)) := by
  have hTransport := workRunExact?_transport
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
    (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
      (suffixMachine problem))
  have hRun := hTransport
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workSteps problem)
    (workStartConfiguration
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalConfiguration
      problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workRunExact problem)
  exact hRun

theorem prefixSuffix_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalConfiguration
            problem)) =
      some
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (workStartConfiguration (suffixMachine problem)
            (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTape
              problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
    (suffixMachine problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTape problem)
  simpa [machine,
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let prefixInitial := workStartConfiguration
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal :=
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalConfiguration problem
  let suffixFinal : WorkConfiguration :=
    { state := (suffixMachine problem).acceptState
      tape := finalTape problem }
  have hPrefix : workRunExact?
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workSteps problem)
      prefixInitial = some prefixFinal := by
    simpa [prefixInitial, prefixFinal] using
      BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workRunExact problem
  have hSuffix : workRunExact? (suffixMachine problem)
      (widthWorkSteps problem + 1 + branchWorkSteps problem + 1 +
        targetWorkSteps problem)
      { state := (suffixMachine problem).startState
        tape := prefixFinal.tape } = some suffixFinal := by
    simpa [prefixFinal, suffixFinal,
      BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalConfiguration,
      workStartConfiguration] using suffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
    (suffixMachine problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workSteps problem)
    (widthWorkSteps problem + 1 + branchWorkSteps problem + 1 +
      targetWorkSteps problem)
    prefixInitial prefixFinal suffixFinal hPrefix rfl hSuffix
  simpa [machine, workSteps, prefixInitial, suffixFinal,
    finalConfiguration, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration, Nat.add_assoc] using hCombined

/-! ### Exact schedule boundary -/

theorem opportunityOutput_eq_nil_or_t {language : Language}
    (problem : VerifierTableauProblem language) :
    opportunityOutput problem =
      if problem.dimensions.tapeWidth problem.tableauInputMode = 1
        then [] else [CNFToken.t] := by
  unfold opportunityOutput
  rw [width_eq_tapeWidth]

theorem opportunityOutput_eq_nil_iff {language : Language}
    (problem : VerifierTableauProblem language) :
    opportunityOutput problem = [] ↔
      problem.dimensions.tapeWidth problem.tableauInputMode = 1 := by
  rw [opportunityOutput_eq_nil_or_t]
  by_cases hWidth :
      problem.dimensions.tapeWidth problem.tableauInputMode = 1
  · simp [hWidth]
  · simp [hWidth]

theorem opportunityOutput_eq_singleton_t_iff {language : Language}
    (problem : VerifierTableauProblem language) :
    opportunityOutput problem = [CNFToken.t] ↔
      problem.dimensions.tapeWidth problem.tableauInputMode ≠ 1 := by
  rw [opportunityOutput_eq_nil_or_t]
  by_cases hWidth :
      problem.dimensions.tapeWidth problem.tableauInputMode = 1
  · simp [hWidth]
  · simp [hWidth]

theorem specification_opportunity_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTokenSlot
          problem⟩ =
      some ((if problem.dimensions.tapeWidth problem.tableauInputMode = 1
          then none else some CNFToken.t),
        ⟨BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTokenSlot
          problem + 1⟩) := by
  exact
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.specification_following_step
      problem

/-- The finite output is exactly the canonical token prefix after consuming
the fourth width-selected padding-or-unary opportunity. -/
theorem secondConstraintFourthPaddingOrUnaryTokens_eq_canonical_formula_prefix
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest, encodeCNFTokens problem.formula =
      secondConstraintFourthPaddingOrUnaryTokens problem ++ rest := by
  rcases
      BuilderSecondConstraintFirstLiteralTerminatorStep.encodeCNFTokens_eq_terminator_then_successor_and_four_optional_unary
        problem with
    ⟨rest, hTokens⟩
  refine ⟨rest, ?_⟩
  unfold secondConstraintFourthPaddingOrUnaryTokens
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
    BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.secondConstraintSecondPaddingOrUnaryTokens
    BuilderSecondConstraintPaddingOrUnaryOpportunityStep.secondConstraintPaddingOrUnaryTokens
    BuilderSecondConstraintFirstLiteralSuccessorTokenStep.secondConstraintFirstLiteralSuccessorTokens
  rw [
    BuilderSecondConstraintFirstLiteralSuccessorTokenStep.successorToken_eq_finish_or_t,
    BuilderSecondConstraintPaddingOrUnaryOpportunityStep.opportunityOutput_eq_nil_or_t,
    BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.opportunityOutput_eq_nil_or_t,
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.opportunityOutput_eq_nil_or_t,
    opportunityOutput_eq_nil_or_t]
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
  opportunitySlot problem

theorem finalTokenSlot_eq_predecessor_add_one {language : Language}
  (problem : VerifierTableauProblem language) :
    finalTokenSlot problem =
      BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTokenSlot problem +
        1 := by
  rw [finalTokenSlot, opportunitySlot_eq_secondConstraintStart_add_eleven,
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTokenSlot_eq_secondConstraintStart_add_ten]

theorem finalTokenSlot_eq_secondConstraintStart_add_eleven
    {language : Language} (problem : VerifierTableauProblem language) :
    finalTokenSlot problem =
      problem.formulaVariableSlotBound + 1 +
        problem.formulaClauseSlotsPerConstraint *
          problem.formulaTokensPerClause + 11 := by
  exact opportunitySlot_eq_secondConstraintStart_add_eleven problem

/-- The retained coordinate identifies the opportunity after the processed
slot: another padding opportunity at width one, otherwise the terminating
`F` of the second literal. -/
theorem followingTokenSlot_direct_eq_padding_or_f {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect (finalTokenSlot problem) =
      some
        (if problem.dimensions.tapeWidth problem.tableauInputMode = 1
          then none else some CNFToken.f) := by
  have hFollowing :=
    BuilderSecondConstraintFirstLiteralTerminatorStep.fifthFollowingTokenSlot_direct_eq_padding_or_f
      problem
  rw [finalTokenSlot_eq_predecessor_add_one,
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalTokenSlot_eq_predecessor_add_one,
    BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.finalTokenSlot_eq_predecessor_add_one,
    BuilderSecondConstraintPaddingOrUnaryOpportunityStep.finalTokenSlot_eq_predecessor_add_one,
    BuilderSecondConstraintFirstLiteralSuccessorTokenStep.finalTokenSlot_eq_predecessor_add_one]
  exact hFollowing

theorem specification_following_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨finalTokenSlot problem⟩ =
      some
        ((if problem.dimensions.tapeWidth problem.tableauInputMode = 1
          then none else some CNFToken.f),
        ⟨finalTokenSlot problem + 1⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [followingTokenSlot_direct_eq_padding_or_f]

theorem finalOutside_contains_finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  let polynomial := opportunitySlotPolynomial problem.verifier
  let scratch :=
    BuilderUnaryPolynomial.scratchWord polynomial problem.input.length
  rcases BuilderUnaryPolynomial.scratchWord_eq_root polynomial
      problem.input.length with ⟨wordPrefix, hScratch⟩
  have hScratch' :
      scratch =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (opportunitySlot problem)
            BuilderUnaryPolynomial.unitSymbol := by
    simpa [scratch, polynomial, opportunitySlot] using hScratch
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
  let targetPolynomial := opportunitySlotPolynomial verifier
  .add
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.rawTimeBound verifier)
    (.add (.constant 648)
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
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens
      problem).length =
        problem.FormulaWidth + 43 +
          (if problem.dimensions.tapeWidth problem.tableauInputMode = 1
            then 0 else 3) := by
  rw [BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.secondConstraintThirdPaddingOrUnaryTokens,
    List.length_append]
  have hFirstOpportunity :
      (BuilderSecondConstraintPaddingOrUnaryOpportunityStep.secondConstraintPaddingOrUnaryTokens
        problem).length =
          problem.FormulaWidth + 43 +
            (if problem.dimensions.tapeWidth problem.tableauInputMode = 1
              then 0 else 1) := by
    rw [BuilderSecondConstraintPaddingOrUnaryOpportunityStep.secondConstraintPaddingOrUnaryTokens,
      List.length_append]
    have hSuccessor :
        (BuilderSecondConstraintFirstLiteralSuccessorTokenStep.secondConstraintFirstLiteralSuccessorTokens
          problem).length = problem.FormulaWidth + 43 := by
      rw [BuilderSecondConstraintFirstLiteralSuccessorTokenStep.secondConstraintFirstLiteralSuccessorTokens,
        List.length_append]
      have hTerminator :
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
      rw [hTerminator]
      simp
    have hOpportunity :
        (BuilderSecondConstraintPaddingOrUnaryOpportunityStep.opportunityOutput
          problem).length =
            if problem.dimensions.tapeWidth problem.tableauInputMode = 1
              then 0 else 1 := by
      rw [
        BuilderSecondConstraintPaddingOrUnaryOpportunityStep.opportunityOutput_eq_nil_or_t]
      by_cases hWidth :
          problem.dimensions.tapeWidth problem.tableauInputMode = 1
      · simp [hWidth]
      · simp [hWidth]
    rw [hSuccessor, hOpportunity]
  have hSecondOpportunity :
      (BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.secondConstraintSecondPaddingOrUnaryTokens
        problem).length =
          problem.FormulaWidth + 43 +
            (if problem.dimensions.tapeWidth problem.tableauInputMode = 1
              then 0 else 2) := by
    rw [
      BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.secondConstraintSecondPaddingOrUnaryTokens,
      List.length_append]
    have hOpportunity :
        (BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.opportunityOutput
          problem).length =
            if problem.dimensions.tapeWidth problem.tableauInputMode = 1
              then 0 else 1 := by
      rw [
        BuilderSecondConstraintSecondPaddingOrUnaryOpportunityStep.opportunityOutput_eq_nil_or_t]
      by_cases hWidth :
          problem.dimensions.tapeWidth problem.tableauInputMode = 1
      · simp [hWidth]
      · simp [hWidth]
    rw [hFirstOpportunity, hOpportunity]
    by_cases hWidth :
        problem.dimensions.tapeWidth problem.tableauInputMode = 1
    · simp [hWidth]
    · simp [hWidth]
  have hThirdOpportunity :
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.opportunityOutput
        problem).length =
          if problem.dimensions.tapeWidth problem.tableauInputMode = 1
            then 0 else 1 := by
    rw [
      BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.opportunityOutput_eq_nil_or_t]
    by_cases hWidth :
        problem.dimensions.tapeWidth problem.tableauInputMode = 1
    · simp [hWidth]
    · simp [hWidth]
  rw [hSecondOpportunity, hThirdOpportunity]
  by_cases hWidth :
      problem.dimensions.tapeWidth problem.tableauInputMode = 1
  · simp [hWidth]
  · simp [hWidth]

/-- The emitted work-tape bits are exactly the canonical formula prefix
after the fourth width-selected padding-or-unary opportunity. -/
theorem finalTokenBits_eq_encodedFormula_secondConstraintFourthPaddingOrUnary
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (secondConstraintFourthPaddingOrUnaryTokens problem) =
      problem.encodedFormula.take
        (2 * (problem.FormulaWidth + 43 +
          if problem.dimensions.tapeWidth problem.tableauInputMode = 1
            then 0 else 4)) := by
  rcases
      secondConstraintFourthPaddingOrUnaryTokens_eq_canonical_formula_prefix
        problem with
    ⟨rest, hTokens⟩
  have hOutputLength :
      (opportunityOutput problem).length =
        if problem.dimensions.tapeWidth problem.tableauInputMode = 1
          then 0 else 1 := by
    rw [opportunityOutput_eq_nil_or_t]
    by_cases hWidth :
        problem.dimensions.tapeWidth problem.tableauInputMode = 1
    · simp [hWidth]
    · simp [hWidth]
  have hLength :
      (encodeTokenPairs
        (secondConstraintFourthPaddingOrUnaryTokens problem)).length =
        2 * (problem.FormulaWidth + 43 +
          if problem.dimensions.tapeWidth problem.tableauInputMode = 1
            then 0 else 4) := by
    rw [encodeTokenPairs_length,
      secondConstraintFourthPaddingOrUnaryTokens, List.length_append,
      predecessorTokens_length, hOutputLength]
    by_cases hWidth :
        problem.dimensions.tapeWidth problem.tableauInputMode = 1
    · simp [hWidth]
    · simp [hWidth]
  let suffix := encodeTokenPairs rest ++ [false]
  have hShape : problem.encodedFormula =
      encodeTokenPairs (secondConstraintFourthPaddingOrUnaryTokens problem) ++
        suffix := by
    simp only [VerifierTableauProblem.encodedFormula, encodeCNF]
    rw [hTokens, encodeTokenPairs_append_local]
    simp [suffix, List.append_assoc]
  rw [hShape, ← hLength]
  exact List.take_left.symm

private theorem appenderWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    appenderWorkSteps problem ≤
      4 * problem.input.length + 2 * problem.FormulaWidth + 100 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  unfold appenderWorkSteps BuilderTokenAppender.workSteps
    BuilderTokenAppender.halfSteps
  rw [predecessorTokens_length]
  by_cases hWidth :
      problem.dimensions.tapeWidth problem.tableauInputMode = 1
  · simp [hWidth]
    omega
  · simp [hWidth]
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
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.rawTimeBound
        problem.verifier).eval problem.input.length +
      648 + 24 * problem.input.length + 12 * problem.FormulaWidth +
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
    [BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep.widthPolynomial]
  omega

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix :=
    BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.rawTimeBound_le problem
  have hAppender := appenderWorkSteps_le problem
  rw [rawTimeBound_eval]
  unfold workSteps branchWorkSteps
  rw [controllerWorkSteps_eq]
  by_cases hWidth : width problem = 1
  · simp [hWidth]
    omega
  · simp [hWidth]
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
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
      (suffixMachine problem) config
  simpa [machine] using hHalted

/-- The complete predecessor endpoint is still globally nonhalting until the
outer bridge launches the width-dependent padding-or-unary suffix. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    (let initial := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (workStartConfiguration
          (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
          (rawInputWorkTape problem.input))
     let result := workRun (machine problem)
       (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workSteps problem)
       initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = .timeout := by
  dsimp only
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.workSteps problem)
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (workStartConfiguration
        (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.machine problem)
        (rawInputWorkTape problem.input)))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalConfiguration
        problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_predecessor_false problem
      (BuilderSecondConstraintThirdPaddingOrUnaryOpportunityStep.finalConfiguration
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

end BuilderSecondConstraintFourthPaddingOrUnaryOpportunityStep

end CookLevin

end PNP.Concrete
