/-
Copyright (c) 2026 PNP Labs.

The second complete negative literal of the fourth canonical Cook--Levin
clause.

The machine in this file composes the complete clause-four first-literal
prefix with the fixed token sequence `F`, `T`, `T`, `F` and one unary cursor
advance after each token. Every raw input therefore emits the negative
literal on variable two and leaves the retained coordinate on the following
clause terminator. This is a fixed four-token prefix, not a general schedule
decoder, a complete clause-four emitter, or a complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderFourthClauseFirstLiteralPrefix

namespace PNP.Concrete

namespace CookLevin

namespace BuilderFourthClauseSecondLiteralPrefix

open PipelineTape PipelineStateNamespace PipelineStageBridges
open BuilderThirdClauseSecondLiteralPrefix

private theorem predecessor_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderFourthClauseFirstLiteralPrefix.machine problem) := by
  exact BuilderFourthClauseFirstLiteralPrefix.rule_source_ne_acceptState problem

private theorem suffix_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine := by
  exact
    BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.rule_source_ne_acceptState

/-- One literal finite work machine from raw input through the second complete
negative literal of clause four. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      4154 +
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
            problem.verifier) := by
  have hPrefix := BuilderFourthClauseFirstLiteralPrefix.rules_length problem
  have hSuffix :=
    BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.rules_length
  have hLaunch : ∀ source target,
      (launchRules source target).length = 9 := by
    intro source target
    rfl
  unfold machine BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
    BuilderFirstClausePrefix.WorkChain.bridgeRules
  simp only [List.length_append, List.length_map]
  rw [hPrefix, hSuffix, hLaunch]
  omega

theorem rules_pairwise_query_distinct {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine
    (BuilderFourthClauseFirstLiteralPrefix.rules_pairwise_query_distinct problem)
    BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.rules_pairwise_query_distinct
    (predecessor_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine
    BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine_acceptState_ne_rejectState

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    BuilderThirdClauseSecondLiteralPrefix.SecondLiteralSuffix.machine
    suffix_noRuleAtAccept rule hRule

/-! ### Exact workspace and trace -/

def signTokenOutput {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens problem ++
    [.f]

def firstUnaryTokenOutput {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  signTokenOutput problem ++ [.t]

def secondUnaryTokenOutput {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  firstUnaryTokenOutput problem ++ [.t]

def fourthClauseSecondLiteralTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  secondUnaryTokenOutput problem ++ [.f]

/-- Active cursor word at the negative sign of variable two. -/
def firstCursorWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderFourthClauseFirstLiteralPrefix.thirdCursorWord problem ++
    [BuilderUnaryPolynomial.unitSymbol]

/-- Active cursor word at the first unary-two unit. -/
def secondCursorWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  firstCursorWord problem ++ [BuilderUnaryPolynomial.unitSymbol]

/-- Active cursor word at the second unary-two unit. -/
def thirdCursorWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  secondCursorWord problem ++ [BuilderUnaryPolynomial.unitSymbol]

/-- Active cursor word at the unary-two terminator. -/
def fourthCursorWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  thirdCursorWord problem ++ [BuilderUnaryPolynomial.unitSymbol]

private def cursorOutsideTail {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (BuilderFourthClauseFirstLiteralPrefix.finalOutside problem).drop
    ((firstCursorWord problem).length + 1)

private theorem predecessor_finalOutside_eq_firstCursor {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFourthClauseFirstLiteralPrefix.finalOutside problem =
      firstCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        cursorOutsideTail problem := by
  unfold cursorOutsideTail firstCursorWord
  simp only [BuilderFourthClauseFirstLiteralPrefix.finalOutside,
    List.length_append, List.length_singleton]
  rw [show
      (BuilderFourthClauseFirstLiteralPrefix.thirdCursorWord problem).length +
          1 + 1 =
        (BuilderFourthClauseFirstLiteralPrefix.thirdCursorWord problem).length +
          2 by omega]
  simp [List.append_assoc]

private theorem firstCursorOutside_eq_secondCursor {language : Language}
    (problem : VerifierTableauProblem language) :
    firstCursorWord problem ++ BuilderUnaryPolynomial.unitSymbol ::
        BuilderUnaryPolynomial.scratchEndSymbol ::
          (cursorOutsideTail problem).drop 1 =
      secondCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 1 := by
  simp [secondCursorWord, List.append_assoc]

private theorem secondCursorOutside_eq_thirdCursor {language : Language}
    (problem : VerifierTableauProblem language) :
    secondCursorWord problem ++ BuilderUnaryPolynomial.unitSymbol ::
        BuilderUnaryPolynomial.scratchEndSymbol ::
          (cursorOutsideTail problem).drop 2 =
      thirdCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 2 := by
  simp [thirdCursorWord, List.append_assoc]

private theorem thirdCursorOutside_eq_fourthCursor {language : Language}
    (problem : VerifierTableauProblem language) :
    thirdCursorWord problem ++ BuilderUnaryPolynomial.unitSymbol ::
        BuilderUnaryPolynomial.scratchEndSymbol ::
          (cursorOutsideTail problem).drop 3 =
      fourthCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 3 := by
  simp [fourthCursorWord, List.append_assoc]

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  fourthCursorWord problem ++ BuilderUnaryPolynomial.unitSymbol ::
    BuilderUnaryPolynomial.scratchEndSymbol ::
      (cursorOutsideTail problem).drop 4

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (fourthClauseSecondLiteralTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def firstAppenderWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderTokenAppender.workSteps problem.input
    (BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens
      problem)

def firstCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
    (firstCursorWord problem)

def signTokenCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  firstAppenderWorkSteps problem + 1 + firstCursorWorkSteps problem

def secondAppenderWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderTokenAppender.workSteps problem.input (signTokenOutput problem)

def secondCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
    (secondCursorWord problem)

def unaryTokenCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  secondAppenderWorkSteps problem + 1 + secondCursorWorkSteps problem

def thirdAppenderWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderTokenAppender.workSteps problem.input (firstUnaryTokenOutput problem)

def thirdCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
    (thirdCursorWord problem)

def secondUnaryTokenCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  thirdAppenderWorkSteps problem + 1 + thirdCursorWorkSteps problem

def fourthAppenderWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderTokenAppender.workSteps problem.input (secondUnaryTokenOutput problem)

def fourthCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
    (fourthCursorWord problem)

def terminatorTokenCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  fourthAppenderWorkSteps problem + 1 + fourthCursorWorkSteps problem

def trueFalseSuffixWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  secondUnaryTokenCursorWorkSteps problem + 1 +
    terminatorTokenCursorWorkSteps problem

def trueTrueFalseSuffixWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  unaryTokenCursorWorkSteps problem + 1 +
    trueFalseSuffixWorkSteps problem

def suffixWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  signTokenCursorWorkSteps problem + 1 +
    trueTrueFalseSuffixWorkSteps problem

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFourthClauseFirstLiteralPrefix.workSteps problem + 1 +
    suffixWorkSteps problem

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (fourthClauseSecondLiteralTokens problem)

private def selectedAppender (request : CNFToken) : WorkMachine :=
  { rules := BuilderTokenAppender.machine.rules
    startState := BuilderTokenAppender.seekInputState request
    acceptState := BuilderTokenAppender.machine.acceptState
    rejectState := BuilderTokenAppender.machine.rejectState }

private theorem selectedAppender_workRunExact
    (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) (request : CNFToken) :
    workRunExact? (selectedAppender request)
        (BuilderTokenAppender.workSteps input output)
        (workStartConfiguration (selectedAppender request)
          (BuilderTokenAppender.workspaceTape input outside output)) =
      some
        { state := (selectedAppender request).acceptState
          tape := BuilderTokenAppender.workspaceTape input outside
            (output ++ [request]) } := by
  have hRunEq : ∀ steps config,
      workRunExact? (selectedAppender request) steps config =
        workRunExact? BuilderTokenAppender.machine steps config := by
    intro steps
    induction steps with
    | zero => intro config; rfl
    | succ steps ih =>
        intro config
        unfold workRunExact?
        change
          (match workStep? BuilderTokenAppender.machine config with
           | none => none
           | some next =>
              workRunExact? (selectedAppender request) steps next) =
          (match workStep? BuilderTokenAppender.machine config with
           | none => none
           | some next =>
              workRunExact? BuilderTokenAppender.machine steps next)
        cases workStep? BuilderTokenAppender.machine config with
        | none => rfl
        | some next => exact ih next
  have hExact := BuilderTokenAppender.appendToken_workRunExact
    input outside output request
  rw [hRunEq]
  simpa [selectedAppender, BuilderTokenAppender.entryConfiguration,
    BuilderTokenAppender.finalConfiguration, workStartConfiguration] using
      hExact

def firstAppenderFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state :=
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (BuilderFourthClauseFirstLiteralPrefix.finalOutside problem)
      (signTokenOutput problem) }

theorem firstAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact?
        BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
        (firstAppenderWorkSteps problem)
        (workStartConfiguration
          BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
          (BuilderFourthClauseFirstLiteralPrefix.finalTape problem)) =
      some (firstAppenderFinalConfiguration problem) := by
  simpa [selectedAppender,
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender,
    firstAppenderWorkSteps,
    BuilderFourthClauseFirstLiteralPrefix.finalTape,
    firstAppenderFinalConfiguration, signTokenOutput] using
      selectedAppender_workRunExact problem.input
        (BuilderFourthClauseFirstLiteralPrefix.finalOutside problem)
        (BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens
          problem) CNFToken.f

def firstCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (secondCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 1)
      (signTokenOutput problem) }

private theorem appendUnit_symbol
    (word : List WorkSymbol)
    (hWord : ∀ symbol ∈ word,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
        symbol = BuilderUnaryPolynomial.separatorSymbol) :
    ∀ symbol ∈ word ++ [BuilderUnaryPolynomial.unitSymbol],
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
        symbol = BuilderUnaryPolynomial.separatorSymbol := by
  intro symbol hMem
  simp only [List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hBase | hUnit
  · exact hWord symbol hBase
  · exact Or.inl hUnit

private theorem predecessorCursorWord_symbol {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ symbol ∈ BuilderFourthClauseFirstLiteralPrefix.thirdCursorWord problem,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
        symbol = BuilderUnaryPolynomial.separatorSymbol := by
  intro symbol hMem
  unfold BuilderFourthClauseFirstLiteralPrefix.thirdCursorWord
    BuilderFourthClauseFirstLiteralPrefix.secondCursorWord
    BuilderFourthClauseFirstLiteralPrefix.firstCursorWord at hMem
  simp only [List.mem_append, List.mem_singleton] at hMem
  rcases hMem with ((hBase | hFirstUnit) | hSecondUnit) | hThirdUnit
  · exact BuilderUnaryPolynomial.scratchWord_symbol
      (BuilderThirdClausePaddingRun.fourthClauseStartPolynomial
        problem.verifier) problem.input.length symbol (by
          simpa [BuilderFourthClauseSeparatorStep.cursorWord] using hBase)
  · exact Or.inl hFirstUnit
  · exact Or.inl hSecondUnit
  · exact Or.inl hThirdUnit

private theorem firstCursorWord_symbol {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ symbol ∈ firstCursorWord problem,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
        symbol = BuilderUnaryPolynomial.separatorSymbol := by
  exact appendUnit_symbol
    (BuilderFourthClauseFirstLiteralPrefix.thirdCursorWord problem)
    (predecessorCursorWord_symbol problem)

private theorem secondCursorWord_symbol {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ symbol ∈ secondCursorWord problem,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
        symbol = BuilderUnaryPolynomial.separatorSymbol := by
  exact appendUnit_symbol (firstCursorWord problem)
    (firstCursorWord_symbol problem)

private theorem thirdCursorWord_symbol {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ symbol ∈ thirdCursorWord problem,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
        symbol = BuilderUnaryPolynomial.separatorSymbol := by
  exact appendUnit_symbol (secondCursorWord problem)
    (secondCursorWord_symbol problem)

private theorem fourthCursorWord_symbol {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ symbol ∈ fourthCursorWord problem,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
        symbol = BuilderUnaryPolynomial.separatorSymbol := by
  exact appendUnit_symbol (thirdCursorWord problem)
    (thirdCursorWord_symbol problem)

set_option maxHeartbeats 3000000 in
theorem firstCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderDynamicTokenCursorStep.CursorAdvance.machine
        (firstCursorWorkSteps problem)
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (BuilderTokenAppender.workspaceTape problem.input
            (BuilderFourthClauseFirstLiteralPrefix.finalOutside problem)
            (signTokenOutput problem))) =
      some (firstCursorFinalConfiguration problem) := by
  have hExact :=
    BuilderDynamicTokenCursorStep.CursorAdvance.advance_workRunExact
      problem.input (firstCursorWord problem) (cursorOutsideTail problem)
      (signTokenOutput problem) (firstCursorWord_symbol problem)
  rw [predecessor_finalOutside_eq_firstCursor]
  rw [firstCursorOutside_eq_secondCursor] at hExact
  simpa only [firstCursorWorkSteps, firstCursorFinalConfiguration] using hExact

theorem signAppenderCursor_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep?
        BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (firstAppenderFinalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (firstAppenderFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (firstAppenderFinalConfiguration problem).tape
  simpa [BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine,
    firstAppenderFinalConfiguration, workStartConfiguration] using hLaunch

def signTokenCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state :=
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine.acceptState
    tape := (firstCursorFinalConfiguration problem).tape }

theorem signTokenCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact?
        BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
        (signTokenCursorWorkSteps problem)
        (workStartConfiguration
          BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
          (BuilderFourthClauseFirstLiteralPrefix.finalTape problem)) =
      some (signTokenCursorFinalConfiguration problem) := by
  let appenderInitial := workStartConfiguration
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    (BuilderFourthClauseFirstLiteralPrefix.finalTape problem)
  let appenderFinal := firstAppenderFinalConfiguration problem
  let cursorFinal := firstCursorFinalConfiguration problem
  have hAppender : workRunExact?
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
      (firstAppenderWorkSteps problem) appenderInitial = some appenderFinal := by
    simpa [appenderInitial, appenderFinal] using
      firstAppender_workRunExact problem
  have hCursor : workRunExact?
      BuilderDynamicTokenCursorStep.CursorAdvance.machine
      (firstCursorWorkSteps problem)
      { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.startState
        tape := appenderFinal.tape } = some cursorFinal := by
    simpa [appenderFinal, firstAppenderFinalConfiguration, cursorFinal,
      workStartConfiguration] using firstCursor_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (firstAppenderWorkSteps problem) (firstCursorWorkSteps problem)
    appenderInitial appenderFinal cursorFinal hAppender rfl hCursor
  simpa [BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine,
    signTokenCursorWorkSteps, appenderInitial, cursorFinal,
    firstCursorFinalConfiguration, signTokenCursorFinalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration] using hCombined

def secondAppenderFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := TrueTokenCursor.appender.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (secondCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 1)
      (firstUnaryTokenOutput problem) }

theorem secondAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? TrueTokenCursor.appender
        (secondAppenderWorkSteps problem)
        (workStartConfiguration TrueTokenCursor.appender
          (firstCursorFinalConfiguration problem).tape) =
      some (secondAppenderFinalConfiguration problem) := by
  simpa [selectedAppender, TrueTokenCursor.appender,
    secondAppenderWorkSteps, firstCursorFinalConfiguration,
    secondAppenderFinalConfiguration, firstUnaryTokenOutput] using
      selectedAppender_workRunExact problem.input
        (secondCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
          (cursorOutsideTail problem).drop 1)
        (signTokenOutput problem) CNFToken.t

def secondCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (thirdCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 2)
      (firstUnaryTokenOutput problem) }

theorem secondCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderDynamicTokenCursorStep.CursorAdvance.machine
        (secondCursorWorkSteps problem)
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (secondAppenderFinalConfiguration problem).tape) =
      some (secondCursorFinalConfiguration problem) := by
  have hExact :=
    BuilderDynamicTokenCursorStep.CursorAdvance.advance_workRunExact
      problem.input (secondCursorWord problem)
      ((cursorOutsideTail problem).drop 1)
      (firstUnaryTokenOutput problem) (secondCursorWord_symbol problem)
  simpa [secondCursorWorkSteps, secondAppenderFinalConfiguration,
    secondCursorFinalConfiguration, thirdCursorWord, List.drop_drop,
    Nat.add_comm] using hExact

theorem unaryAppenderCursor_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? TrueTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (secondAppenderFinalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (secondAppenderFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    TrueTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (secondAppenderFinalConfiguration problem).tape
  simpa [TrueTokenCursor.machine, secondAppenderFinalConfiguration,
    workStartConfiguration] using hLaunch

def unaryTokenCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := TrueTokenCursor.machine.acceptState
    tape := (secondCursorFinalConfiguration problem).tape }

theorem unaryTokenCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? TrueTokenCursor.machine
        (unaryTokenCursorWorkSteps problem)
        (workStartConfiguration TrueTokenCursor.machine
          (firstCursorFinalConfiguration problem).tape) =
      some (unaryTokenCursorFinalConfiguration problem) := by
  let appenderInitial := workStartConfiguration TrueTokenCursor.appender
    (firstCursorFinalConfiguration problem).tape
  let appenderFinal := secondAppenderFinalConfiguration problem
  let cursorFinal := secondCursorFinalConfiguration problem
  have hAppender : workRunExact? TrueTokenCursor.appender
      (secondAppenderWorkSteps problem) appenderInitial = some appenderFinal := by
    simpa [appenderInitial, appenderFinal] using
      secondAppender_workRunExact problem
  have hCursor : workRunExact?
      BuilderDynamicTokenCursorStep.CursorAdvance.machine
      (secondCursorWorkSteps problem)
      { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.startState
        tape := appenderFinal.tape } = some cursorFinal := by
    simpa [appenderFinal, cursorFinal, secondCursorFinalConfiguration,
      workStartConfiguration] using secondCursor_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    TrueTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (secondAppenderWorkSteps problem) (secondCursorWorkSteps problem)
    appenderInitial appenderFinal cursorFinal hAppender rfl hCursor
  simpa [TrueTokenCursor.machine, unaryTokenCursorWorkSteps,
    appenderInitial, cursorFinal, secondCursorFinalConfiguration,
    unaryTokenCursorFinalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration] using hCombined

def thirdAppenderFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := TrueTokenCursor.appender.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (thirdCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 2)
      (secondUnaryTokenOutput problem) }

theorem thirdAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? TrueTokenCursor.appender
        (thirdAppenderWorkSteps problem)
        (workStartConfiguration TrueTokenCursor.appender
          (secondCursorFinalConfiguration problem).tape) =
      some (thirdAppenderFinalConfiguration problem) := by
  simpa [selectedAppender, TrueTokenCursor.appender,
    thirdAppenderWorkSteps, secondCursorFinalConfiguration,
    thirdAppenderFinalConfiguration, secondUnaryTokenOutput] using
      selectedAppender_workRunExact problem.input
        (thirdCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
          (cursorOutsideTail problem).drop 2)
        (firstUnaryTokenOutput problem) CNFToken.t

def thirdCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (fourthCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 3)
      (secondUnaryTokenOutput problem) }

theorem thirdCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderDynamicTokenCursorStep.CursorAdvance.machine
        (thirdCursorWorkSteps problem)
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (thirdAppenderFinalConfiguration problem).tape) =
      some (thirdCursorFinalConfiguration problem) := by
  have hExact :=
    BuilderDynamicTokenCursorStep.CursorAdvance.advance_workRunExact
      problem.input (thirdCursorWord problem)
      ((cursorOutsideTail problem).drop 2)
      (secondUnaryTokenOutput problem) (thirdCursorWord_symbol problem)
  simpa [thirdCursorWorkSteps, thirdAppenderFinalConfiguration,
    thirdCursorFinalConfiguration, fourthCursorWord, List.drop_drop,
    Nat.add_comm] using hExact

theorem secondUnaryAppenderCursor_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? TrueTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (thirdAppenderFinalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (thirdAppenderFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    TrueTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (thirdAppenderFinalConfiguration problem).tape
  simpa [TrueTokenCursor.machine, thirdAppenderFinalConfiguration,
    workStartConfiguration] using hLaunch

def secondUnaryTokenCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := TrueTokenCursor.machine.acceptState
    tape := (thirdCursorFinalConfiguration problem).tape }

theorem secondUnaryTokenCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? TrueTokenCursor.machine
        (secondUnaryTokenCursorWorkSteps problem)
        (workStartConfiguration TrueTokenCursor.machine
          (secondCursorFinalConfiguration problem).tape) =
      some (secondUnaryTokenCursorFinalConfiguration problem) := by
  let appenderInitial := workStartConfiguration TrueTokenCursor.appender
    (secondCursorFinalConfiguration problem).tape
  let appenderFinal := thirdAppenderFinalConfiguration problem
  let cursorFinal := thirdCursorFinalConfiguration problem
  have hAppender : workRunExact? TrueTokenCursor.appender
      (thirdAppenderWorkSteps problem) appenderInitial = some appenderFinal := by
    simpa [appenderInitial, appenderFinal] using
      thirdAppender_workRunExact problem
  have hCursor : workRunExact?
      BuilderDynamicTokenCursorStep.CursorAdvance.machine
      (thirdCursorWorkSteps problem)
      { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.startState
        tape := appenderFinal.tape } = some cursorFinal := by
    simpa [appenderFinal, cursorFinal, thirdCursorFinalConfiguration,
      workStartConfiguration] using thirdCursor_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    TrueTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (thirdAppenderWorkSteps problem) (thirdCursorWorkSteps problem)
    appenderInitial appenderFinal cursorFinal hAppender rfl hCursor
  simpa [TrueTokenCursor.machine, secondUnaryTokenCursorWorkSteps,
    appenderInitial, cursorFinal, thirdCursorFinalConfiguration,
    secondUnaryTokenCursorFinalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration] using hCombined

def fourthAppenderFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state :=
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (fourthCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 3)
      (fourthClauseSecondLiteralTokens problem) }

theorem fourthAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact?
        BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
        (fourthAppenderWorkSteps problem)
        (workStartConfiguration
          BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
          (thirdCursorFinalConfiguration problem).tape) =
      some (fourthAppenderFinalConfiguration problem) := by
  simpa [selectedAppender,
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender,
    fourthAppenderWorkSteps, thirdCursorFinalConfiguration,
    fourthAppenderFinalConfiguration, fourthClauseSecondLiteralTokens] using
      selectedAppender_workRunExact problem.input
        (fourthCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
          (cursorOutsideTail problem).drop 3)
        (secondUnaryTokenOutput problem) CNFToken.f

def fourthCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.acceptState
    tape := finalTape problem }

theorem fourthCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderDynamicTokenCursorStep.CursorAdvance.machine
        (fourthCursorWorkSteps problem)
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (fourthAppenderFinalConfiguration problem).tape) =
      some (fourthCursorFinalConfiguration problem) := by
  have hExact :=
    BuilderDynamicTokenCursorStep.CursorAdvance.advance_workRunExact
      problem.input (fourthCursorWord problem)
      ((cursorOutsideTail problem).drop 3)
      (fourthClauseSecondLiteralTokens problem)
      (fourthCursorWord_symbol problem)
  simpa [fourthCursorWorkSteps, fourthAppenderFinalConfiguration,
    fourthCursorFinalConfiguration, finalTape, finalOutside,
    List.drop_drop, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using hExact

theorem terminatorAppenderCursor_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep?
        BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (fourthAppenderFinalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (fourthAppenderFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (fourthAppenderFinalConfiguration problem).tape
  simpa [BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine,
    fourthAppenderFinalConfiguration, workStartConfiguration] using hLaunch

def terminatorTokenCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state :=
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine.acceptState
    tape := finalTape problem }

theorem terminatorTokenCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact?
        BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
        (terminatorTokenCursorWorkSteps problem)
        (workStartConfiguration
          BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
          (thirdCursorFinalConfiguration problem).tape) =
      some (terminatorTokenCursorFinalConfiguration problem) := by
  let appenderInitial := workStartConfiguration
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    (thirdCursorFinalConfiguration problem).tape
  let appenderFinal := fourthAppenderFinalConfiguration problem
  let cursorFinal := fourthCursorFinalConfiguration problem
  have hAppender : workRunExact?
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
      (fourthAppenderWorkSteps problem) appenderInitial = some appenderFinal := by
    simpa [appenderInitial, appenderFinal] using
      fourthAppender_workRunExact problem
  have hCursor : workRunExact?
      BuilderDynamicTokenCursorStep.CursorAdvance.machine
      (fourthCursorWorkSteps problem)
      { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.startState
        tape := appenderFinal.tape } = some cursorFinal := by
    simpa [appenderFinal, cursorFinal, fourthCursorFinalConfiguration,
      workStartConfiguration] using fourthCursor_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (fourthAppenderWorkSteps problem) (fourthCursorWorkSteps problem)
    appenderInitial appenderFinal cursorFinal hAppender rfl hCursor
  simpa [BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine,
    terminatorTokenCursorWorkSteps, appenderInitial, cursorFinal,
    fourthCursorFinalConfiguration, terminatorTokenCursorFinalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration] using hCombined

theorem trueFalseSuffix_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? TrueFalseSuffix.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (secondUnaryTokenCursorFinalConfiguration problem)) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
          (secondUnaryTokenCursorFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    TrueTokenCursor.machine
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    (secondUnaryTokenCursorFinalConfiguration problem).tape
  simpa [TrueFalseSuffix.machine, secondUnaryTokenCursorFinalConfiguration,
    workStartConfiguration] using hLaunch

theorem trueFalseSuffix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? TrueFalseSuffix.machine
        (trueFalseSuffixWorkSteps problem)
        (workStartConfiguration TrueFalseSuffix.machine
          (secondCursorFinalConfiguration problem).tape) =
      some
        { state := TrueFalseSuffix.machine.acceptState
          tape := finalTape problem } := by
  let unaryInitial := workStartConfiguration TrueTokenCursor.machine
    (secondCursorFinalConfiguration problem).tape
  let unaryFinal := secondUnaryTokenCursorFinalConfiguration problem
  let terminatorFinal := terminatorTokenCursorFinalConfiguration problem
  have hUnary : workRunExact? TrueTokenCursor.machine
      (secondUnaryTokenCursorWorkSteps problem)
      unaryInitial = some unaryFinal := by
    simpa [unaryInitial, unaryFinal] using
      secondUnaryTokenCursor_workRunExact problem
  have hTerminator : workRunExact?
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
      (terminatorTokenCursorWorkSteps problem)
      { state :=
          BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine.startState
        tape := unaryFinal.tape } = some terminatorFinal := by
    simpa [unaryFinal, secondUnaryTokenCursorFinalConfiguration,
      terminatorFinal,
      workStartConfiguration] using
        terminatorTokenCursor_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    TrueTokenCursor.machine
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    (secondUnaryTokenCursorWorkSteps problem)
    (terminatorTokenCursorWorkSteps problem)
    unaryInitial unaryFinal terminatorFinal hUnary rfl hTerminator
  simpa [TrueFalseSuffix.machine, trueFalseSuffixWorkSteps, unaryInitial,
    terminatorFinal, terminatorTokenCursorFinalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration] using hCombined

theorem trueTrueFalseSuffix_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? TrueTrueFalseSuffix.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (unaryTokenCursorFinalConfiguration problem)) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration TrueFalseSuffix.machine
          (unaryTokenCursorFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    TrueTokenCursor.machine TrueFalseSuffix.machine
    (unaryTokenCursorFinalConfiguration problem).tape
  simpa [TrueTrueFalseSuffix.machine, unaryTokenCursorFinalConfiguration,
    workStartConfiguration] using hLaunch

theorem trueTrueFalseSuffix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? TrueTrueFalseSuffix.machine
        (trueTrueFalseSuffixWorkSteps problem)
        (workStartConfiguration TrueTrueFalseSuffix.machine
          (firstCursorFinalConfiguration problem).tape) =
      some
        { state := TrueTrueFalseSuffix.machine.acceptState
          tape := finalTape problem } := by
  let unaryInitial := workStartConfiguration TrueTokenCursor.machine
    (firstCursorFinalConfiguration problem).tape
  let unaryFinal := unaryTokenCursorFinalConfiguration problem
  let tailFinal : WorkConfiguration :=
    { state := TrueFalseSuffix.machine.acceptState
      tape := finalTape problem }
  have hUnary : workRunExact? TrueTokenCursor.machine
      (unaryTokenCursorWorkSteps problem) unaryInitial = some unaryFinal := by
    simpa [unaryInitial, unaryFinal] using
      unaryTokenCursor_workRunExact problem
  have hTail : workRunExact? TrueFalseSuffix.machine
      (trueFalseSuffixWorkSteps problem)
      { state := TrueFalseSuffix.machine.startState
        tape := unaryFinal.tape } = some tailFinal := by
    simpa [unaryFinal, unaryTokenCursorFinalConfiguration, tailFinal,
      workStartConfiguration] using trueFalseSuffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    TrueTokenCursor.machine TrueFalseSuffix.machine
    (unaryTokenCursorWorkSteps problem) (trueFalseSuffixWorkSteps problem)
    unaryInitial unaryFinal tailFinal hUnary rfl hTail
  simpa [TrueTrueFalseSuffix.machine, trueTrueFalseSuffixWorkSteps,
    unaryInitial, tailFinal, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

theorem secondLiteralSuffix_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? SecondLiteralSuffix.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (signTokenCursorFinalConfiguration problem)) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration TrueTrueFalseSuffix.machine
          (signTokenCursorFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine
    (signTokenCursorFinalConfiguration problem).tape
  simpa [SecondLiteralSuffix.machine, signTokenCursorFinalConfiguration,
    workStartConfiguration] using hLaunch

theorem suffix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? SecondLiteralSuffix.machine (suffixWorkSteps problem)
        (workStartConfiguration SecondLiteralSuffix.machine
          (BuilderFourthClauseFirstLiteralPrefix.finalTape problem)) =
      some
        { state := SecondLiteralSuffix.machine.acceptState
          tape := finalTape problem } := by
  let signInitial := workStartConfiguration
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    (BuilderFourthClauseFirstLiteralPrefix.finalTape problem)
  let signFinal := signTokenCursorFinalConfiguration problem
  let tailFinal : WorkConfiguration :=
    { state := TrueTrueFalseSuffix.machine.acceptState
      tape := finalTape problem }
  have hSign : workRunExact?
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
      (signTokenCursorWorkSteps problem) signInitial = some signFinal := by
    simpa [signInitial, signFinal] using signTokenCursor_workRunExact problem
  have hTail : workRunExact? TrueTrueFalseSuffix.machine
      (trueTrueFalseSuffixWorkSteps problem)
      { state := TrueTrueFalseSuffix.machine.startState
        tape := signFinal.tape } = some tailFinal := by
    simpa [signFinal, signTokenCursorFinalConfiguration, tailFinal,
      workStartConfiguration] using trueTrueFalseSuffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine
    (signTokenCursorWorkSteps problem)
    (trueTrueFalseSuffixWorkSteps problem)
    signInitial signFinal tailFinal hSign rfl hTail
  simpa [SecondLiteralSuffix.machine, suffixWorkSteps, signInitial, tailFinal,
    BuilderFirstClausePrefix.WorkChain.machine, workStartConfiguration,
    renameConfiguration] using hCombined

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderFourthClauseFirstLiteralPrefix.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (BuilderFourthClauseFirstLiteralPrefix.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderFourthClauseFirstLiteralPrefix.machine problem) (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderFourthClauseFirstLiteralPrefix.machine problem)
      SecondLiteralSuffix.machine)
    (BuilderFourthClauseFirstLiteralPrefix.workSteps problem)
    (workStartConfiguration
      (BuilderFourthClauseFirstLiteralPrefix.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderFourthClauseFirstLiteralPrefix.finalConfiguration problem)
    (BuilderFourthClauseFirstLiteralPrefix.workRunExact problem)
  simpa [machine, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hTransport

theorem prefixSecondLiteral_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderFourthClauseFirstLiteralPrefix.finalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration SecondLiteralSuffix.machine
          (BuilderFourthClauseFirstLiteralPrefix.finalTape problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine
    (BuilderFourthClauseFirstLiteralPrefix.finalTape problem)
  simpa [machine,
    BuilderFourthClauseFirstLiteralPrefix.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
/-- Every raw input follows the complete first-literal prefix, appends `F`,
`T`, `T`, `F`, and advances the retained coordinate four times. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let prefixInitial := workStartConfiguration
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal :=
    BuilderFourthClauseFirstLiteralPrefix.finalConfiguration problem
  let suffixFinal : WorkConfiguration :=
    { state := SecondLiteralSuffix.machine.acceptState
      tape := finalTape problem }
  have hPrefix : workRunExact?
      (BuilderFourthClauseFirstLiteralPrefix.machine problem)
      (BuilderFourthClauseFirstLiteralPrefix.workSteps problem)
      prefixInitial = some prefixFinal := by
    simpa [prefixInitial, prefixFinal] using
      BuilderFourthClauseFirstLiteralPrefix.workRunExact problem
  have hSuffix : workRunExact? SecondLiteralSuffix.machine
      (suffixWorkSteps problem)
      { state := SecondLiteralSuffix.machine.startState
        tape := prefixFinal.tape } = some suffixFinal := by
    simpa [prefixFinal, suffixFinal,
      BuilderFourthClauseFirstLiteralPrefix.finalConfiguration,
      workStartConfiguration] using suffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine
    (BuilderFourthClauseFirstLiteralPrefix.workSteps problem)
    (suffixWorkSteps problem) prefixInitial prefixFinal suffixFinal
    hPrefix rfl hSuffix
  simpa [machine, workSteps, prefixInitial, suffixFinal,
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

private theorem formulaClauseTokens_first_three_rectangles_then_fourthSecondLiteral
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
         some CNFToken.f, some CNFToken.finish] ++ rest := by
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

/-- The finite output is exactly the canonical token prefix through the
second negative literal of clause four. -/
theorem fourthClauseSecondLiteralTokens_eq_canonical_formula_prefix
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest, encodeCNFTokens problem.formula =
      fourthClauseSecondLiteralTokens problem ++ rest := by
  rcases formulaClauseTokens_first_three_rectangles_then_fourthSecondLiteral
      problem with
    ⟨clauseTail, hClauseTail⟩
  have hEmit :
      FormulaSchedule.emit
          (problem.formulaClauseSchedule.flatMap
            problem.scheduledClauseTokens) =
        [CNFToken.sep,
         CNFToken.t, CNFToken.f,
         CNFToken.t, CNFToken.t, CNFToken.f,
         CNFToken.t, CNFToken.t, CNFToken.t,
         CNFToken.f, CNFToken.finish,
         CNFToken.sep, CNFToken.f, CNFToken.f,
         CNFToken.f, CNFToken.t, CNFToken.f,
         CNFToken.finish,
         CNFToken.sep, CNFToken.f, CNFToken.f,
         CNFToken.f, CNFToken.t, CNFToken.t, CNFToken.f,
         CNFToken.finish,
         CNFToken.sep, CNFToken.f, CNFToken.t, CNFToken.f,
         CNFToken.f, CNFToken.t, CNFToken.t, CNFToken.f,
         CNFToken.finish] ++ FormulaSchedule.emit clauseTail := by
    rw [hClauseTail]
    simp
  refine ⟨CNFToken.finish :: FormulaSchedule.emit clauseTail ++
      [CNFToken.finish], ?_⟩
  rw [← problem.formulaTokenSchedule_emit_eq_encodeCNFTokens]
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [FormulaSchedule.emit_append, FormulaSchedule.emit_append,
    FormulaSchedule.emit_pad, hEmit]
  unfold fourthClauseSecondLiteralTokens secondUnaryTokenOutput
    firstUnaryTokenOutput signTokenOutput
    BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens
    BuilderFourthClauseFirstLiteralPrefix.unaryTokenOutput
    BuilderFourthClauseFirstLiteralPrefix.signTokenOutput
    BuilderFourthClauseSeparatorStep.fourthClauseStartTokens
    BuilderThirdClausePrefix.thirdClauseTokens
    BuilderThirdClauseSecondLiteralPrefix.thirdClauseSecondLiteralTokens
    BuilderThirdClauseSecondLiteralPrefix.secondUnaryTokenOutput
    BuilderThirdClauseSecondLiteralPrefix.firstUnaryTokenOutput
    BuilderThirdClauseSecondLiteralPrefix.signTokenOutput
    BuilderThirdClauseFirstLiteralPrefix.thirdClauseFirstLiteralTokens
    BuilderThirdClauseFirstLiteralPrefix.firstTokenOutput
    BuilderThirdClauseSeparatorStep.thirdClauseStartTokens
    BuilderSecondClausePrefix.secondClauseTokens
    BuilderSecondClauseSecondLiteralPrefix.secondClauseSecondLiteralTokens
    BuilderSecondClauseSecondLiteralPrefix.unaryTokenOutput
    BuilderSecondClauseSecondLiteralPrefix.signTokenOutput
    BuilderSecondClauseFirstLiteralPrefix.secondClauseFirstLiteralTokens
    BuilderSecondClauseFirstLiteralPrefix.firstTokenOutput
    BuilderSecondClauseSeparatorStep.secondClauseStartTokens
  rw [BuilderFirstClausePrefix.firstClauseTokens_eq_canonical_prefix]
  simp [List.append_assoc]

private theorem encodeTokenPairs_append_local
    (left right : List CNFToken) :
    encodeTokenPairs (left ++ right) =
      encodeTokenPairs left ++ encodeTokenPairs right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      cases token <;>
        simp [encodeTokenPairs, ih, List.append_assoc]

/-- The emitted work-tape bits are exactly the canonical formula prefix
through negative variable two in clause four. -/
theorem finalTokenBits_eq_encodedFormula_fourthClauseSecondLiteral
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (fourthClauseSecondLiteralTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 35)) := by
  rcases fourthClauseSecondLiteralTokens_eq_canonical_formula_prefix problem with
    ⟨rest, hTokens⟩
  have hLength :
      (encodeTokenPairs (fourthClauseSecondLiteralTokens problem)).length =
        2 * (problem.FormulaWidth + 35) := by
    rw [encodeTokenPairs_length]
    simp [fourthClauseSecondLiteralTokens, secondUnaryTokenOutput,
      firstUnaryTokenOutput, signTokenOutput,
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
  let suffix := encodeTokenPairs rest ++ [false]
  have hShape : problem.encodedFormula =
      encodeTokenPairs (fourthClauseSecondLiteralTokens problem) ++ suffix := by
    simp only [VerifierTableauProblem.encodedFormula, encodeCNF]
    rw [hTokens, encodeTokenPairs_append_local]
    simp [suffix, List.append_assoc]
  rw [hShape, ← hLength]
  exact List.take_left.symm

def finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderThirdClausePaddingRun.fourthClauseStart problem + 8

theorem finalTokenSlot_eq_fourthClauseStart_add_eight
    {language : Language} (problem : VerifierTableauProblem language) :
    finalTokenSlot problem = problem.formulaVariableSlotBound + 1 +
        3 * problem.formulaTokensPerClause + 8 := by
  rw [finalTokenSlot,
    BuilderThirdClausePaddingRun.fourthClauseStart_eq]

theorem finalOutside_contains_finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.scratchWord_eq_root
      (BuilderThirdClausePaddingRun.fourthClauseStartPolynomial
        problem.verifier) problem.input.length with
    ⟨wordPrefix, hPrefix⟩
  refine ⟨wordPrefix, (cursorOutsideTail problem).drop 4, ?_⟩
  unfold finalOutside fourthCursorWord thirdCursorWord secondCursorWord
    firstCursorWord
    finalTokenSlot
    BuilderFourthClauseFirstLiteralPrefix.thirdCursorWord
    BuilderFourthClauseFirstLiteralPrefix.secondCursorWord
    BuilderFourthClauseFirstLiteralPrefix.firstCursorWord
    BuilderFourthClauseSeparatorStep.cursorWord
  rw [hPrefix]
  rw [show BuilderThirdClausePaddingRun.fourthClauseStart problem + 8 =
      (((((((BuilderThirdClausePaddingRun.fourthClauseStart problem + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1 by omega]
  rw [List.replicate_succ', List.replicate_succ', List.replicate_succ',
    List.replicate_succ', List.replicate_succ', List.replicate_succ',
    List.replicate_succ', List.replicate_succ']
  simp [BuilderThirdClausePaddingRun.fourthClauseStart,
    List.append_assoc]

private theorem directSlot_at_fourthClauseOffset
    {language : Language} (problem : VerifierTableauProblem language)
    (offset : Nat) (token : CNFToken)
    (hOffset : offset < 9)
    (hLookup :
      ([some CNFToken.sep,
        some CNFToken.f, some CNFToken.t, some CNFToken.f,
        some CNFToken.f, some CNFToken.t, some CNFToken.t,
        some CNFToken.f, some CNFToken.finish] : List (Option CNFToken))[offset]? =
          some (some token)) :
    problem.formulaTokenSlotDirect
        (BuilderThirdClausePaddingRun.fourthClauseStart problem + offset) =
      some (some token) := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_first_three_rectangles_then_fourthSecondLiteral
      problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses, BuilderThirdClausePaddingRun.fourthClauseStart_eq]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
          problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
  have hWidth :=
    BuilderFirstClausePaddingRun.formulaVariableSlotBound_at_least_three
      problem
  have hProduct : 10 ≤
      (problem.formulaVariableSlotBound + 4) *
        (problem.formulaVariableSlotBound + 1) := by
    exact Nat.le_trans (by decide : 10 ≤ 7 * 4)
      (Nat.mul_le_mul (by omega) (by omega))
  have hClauseWidth : 12 ≤ problem.formulaTokensPerClause := by
    unfold VerifierTableauProblem.formulaTokensPerClause
    omega
  simp only [List.append_assoc]
  rw [List.getElem?_append, hHeader, if_neg (by omega)]
  rw [show problem.formulaVariableSlotBound + 1 +
      3 * problem.formulaTokensPerClause + offset -
        (problem.formulaVariableSlotBound + 1) =
      3 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 3 * problem.formulaTokensPerClause + offset - 11 =
      (problem.formulaTokensPerClause - 11) +
        2 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 11) +
      2 * problem.formulaTokensPerClause + offset -
      (problem.formulaTokensPerClause - 11) =
        2 * problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 2 * problem.formulaTokensPerClause + offset - 7 =
      (problem.formulaTokensPerClause - 7) +
        problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 7) +
      problem.formulaTokensPerClause + offset -
      (problem.formulaTokensPerClause - 7) =
        problem.formulaTokensPerClause + offset by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause + offset - 8 =
      (problem.formulaTokensPerClause - 8) + offset by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 8) + offset -
      (problem.formulaTokensPerClause - 8) = offset by omega]
  rw [List.getElem?_append]
  rw [if_pos (by simpa using hOffset)]
  exact hLookup

/-- The second literal begins with a negative sign. -/
theorem secondLiteralSignSlot_direct_eq_f {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (BuilderThirdClausePaddingRun.fourthClauseStart problem + 4) =
      some (some CNFToken.f) := by
  exact directSlot_at_fourthClauseOffset problem 4 CNFToken.f
    (by decide) (by decide)

/-- Variable two contributes its first unary `T` unit. -/
theorem secondLiteralFirstUnaryUnitSlot_direct_eq_t {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (BuilderThirdClausePaddingRun.fourthClauseStart problem + 5) =
      some (some CNFToken.t) := by
  exact directSlot_at_fourthClauseOffset problem 5 CNFToken.t
    (by decide) (by decide)

/-- Variable two contributes its second unary `T` unit. -/
theorem secondLiteralSecondUnaryUnitSlot_direct_eq_t {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (BuilderThirdClausePaddingRun.fourthClauseStart problem + 6) =
      some (some CNFToken.t) := by
  exact directSlot_at_fourthClauseOffset problem 6 CNFToken.t
    (by decide) (by decide)

/-- The unary-two encoding ends with `F`. -/
theorem secondLiteralTerminatorSlot_direct_eq_f {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (BuilderThirdClausePaddingRun.fourthClauseStart problem + 7) =
      some (some CNFToken.f) := by
  exact directSlot_at_fourthClauseOffset problem 7 CNFToken.f
    (by decide) (by decide)

/-- The retained coordinate is the clause terminator. -/
theorem nextTokenSlot_direct_eq_finish {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect (finalTokenSlot problem) =
      some (some CNFToken.finish) := by
  simpa [finalTokenSlot] using
    directSlot_at_fourthClauseOffset problem 8 CNFToken.finish
      (by decide) (by decide)

theorem specification_secondLiteral_sign_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderThirdClausePaddingRun.fourthClauseStart problem + 4⟩ =
      some (some CNFToken.f,
        ⟨BuilderThirdClausePaddingRun.fourthClauseStart problem + 5⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [secondLiteralSignSlot_direct_eq_f]

theorem specification_secondLiteral_unaryUnit_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderThirdClausePaddingRun.fourthClauseStart problem + 5⟩ =
      some (some CNFToken.t,
        ⟨BuilderThirdClausePaddingRun.fourthClauseStart problem + 6⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [secondLiteralFirstUnaryUnitSlot_direct_eq_t]

theorem specification_secondLiteral_secondUnaryUnit_step
    {language : Language} (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderThirdClausePaddingRun.fourthClauseStart problem + 6⟩ =
      some (some CNFToken.t,
        ⟨BuilderThirdClausePaddingRun.fourthClauseStart problem + 7⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [secondLiteralSecondUnaryUnitSlot_direct_eq_t]

theorem specification_secondLiteral_terminator_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderThirdClausePaddingRun.fourthClauseStart problem + 7⟩ =
      some (some CNFToken.f,
        ⟨BuilderThirdClausePaddingRun.fourthClauseStart problem + 8⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [secondLiteralTerminatorSlot_direct_eq_f]

theorem specification_next_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨finalTokenSlot problem⟩ =
      some (some CNFToken.finish, ⟨finalTokenSlot problem + 1⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [nextTokenSlot_direct_eq_finish]

set_option maxRecDepth 100000 in
theorem finalConfiguration_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (finalConfiguration problem).state = (machine problem).acceptState := rfl

set_option maxRecDepth 100000 in
private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
  rfl

/-! ### External compiled-time polynomial -/

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

/-- External raw-transition bound for eight launches, four selected token
appends, and four complete bidirectional cursor scans. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderFourthClauseFirstLiteralPrefix.rawTimeBound verifier)
    (.add (.constant 2232)
      (.add (scalePolynomial 96 .variable)
        (.add (scalePolynomial 48 (formulaWidthPolynomial verifier))
          (scalePolynomial 48
            (BuilderUnaryPolynomial.registerSpanPolynomial
              (BuilderThirdClausePaddingRun.fourthClauseStartPolynomial
                verifier))))))

private theorem predecessorTokens_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens
      problem).length = problem.FormulaWidth + 31 := by
  simp [BuilderFourthClauseFirstLiteralPrefix.fourthClauseFirstLiteralTokens,
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

private theorem signTokenOutput_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (signTokenOutput problem).length = problem.FormulaWidth + 32 := by
  rw [signTokenOutput, List.length_append, predecessorTokens_length]
  simp

private theorem firstUnaryTokenOutput_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (firstUnaryTokenOutput problem).length = problem.FormulaWidth + 33 := by
  rw [firstUnaryTokenOutput, List.length_append, signTokenOutput_length]
  simp

private theorem secondUnaryTokenOutput_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (secondUnaryTokenOutput problem).length = problem.FormulaWidth + 34 := by
  rw [secondUnaryTokenOutput, List.length_append,
    firstUnaryTokenOutput_length]
  simp

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderFourthClauseFirstLiteralPrefix.rawTimeBound
          problem.verifier).eval problem.input.length + 2232 +
        96 * problem.input.length + 48 * problem.FormulaWidth +
        48 * (BuilderFourthClauseSeparatorStep.cursorWord problem).length := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, NatPolynomial.eval_variable, scalePolynomial]
  have hWidth :
      (formulaWidthPolynomial problem.verifier).eval problem.input.length =
        problem.FormulaWidth := by
    simpa [BitString.size] using problem.formulaWidthPolynomial_eval
  rw [hWidth]
  rw [← BuilderUnaryPolynomial.scratchWord_length
    (BuilderThirdClausePaddingRun.fourthClauseStartPolynomial
      problem.verifier) problem.input.length]
  simp only [BuilderFourthClauseSeparatorStep.cursorWord]
  omega

private theorem firstAppenderWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    firstAppenderWorkSteps problem ≤
      4 * problem.input.length + 2 * problem.FormulaWidth + 70 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  unfold firstAppenderWorkSteps BuilderTokenAppender.workSteps
    BuilderTokenAppender.halfSteps
  rw [predecessorTokens_length]
  omega

private theorem secondAppenderWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    secondAppenderWorkSteps problem ≤
      4 * problem.input.length + 2 * problem.FormulaWidth + 72 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  unfold secondAppenderWorkSteps BuilderTokenAppender.workSteps
    BuilderTokenAppender.halfSteps
  rw [signTokenOutput_length]
  omega

private theorem thirdAppenderWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    thirdAppenderWorkSteps problem ≤
      4 * problem.input.length + 2 * problem.FormulaWidth + 74 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  unfold thirdAppenderWorkSteps BuilderTokenAppender.workSteps
    BuilderTokenAppender.halfSteps
  rw [firstUnaryTokenOutput_length]
  omega

private theorem fourthAppenderWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    fourthAppenderWorkSteps problem ≤
      4 * problem.input.length + 2 * problem.FormulaWidth + 76 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  unfold fourthAppenderWorkSteps BuilderTokenAppender.workSteps
    BuilderTokenAppender.halfSteps
  rw [secondUnaryTokenOutput_length]
  omega

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix :=
    BuilderFourthClauseFirstLiteralPrefix.rawTimeBound_le problem
  have hFirstAppender := firstAppenderWorkSteps_le problem
  have hSecondAppender := secondAppenderWorkSteps_le problem
  have hThirdAppender := thirdAppenderWorkSteps_le problem
  have hFourthAppender := fourthAppenderWorkSteps_le problem
  have hFirstCursorLength :
      (firstCursorWord problem).length =
        (BuilderFourthClauseSeparatorStep.cursorWord problem).length + 4 := by
    simp [firstCursorWord,
      BuilderFourthClauseFirstLiteralPrefix.thirdCursorWord,
      BuilderFourthClauseFirstLiteralPrefix.secondCursorWord,
      BuilderFourthClauseFirstLiteralPrefix.firstCursorWord]
  have hSecondCursorLength :
      (secondCursorWord problem).length =
        (BuilderFourthClauseSeparatorStep.cursorWord problem).length + 5 := by
    simp [secondCursorWord, hFirstCursorLength]
  have hThirdCursorLength :
      (thirdCursorWord problem).length =
        (BuilderFourthClauseSeparatorStep.cursorWord problem).length + 6 := by
    simp [thirdCursorWord, hSecondCursorLength]
  have hFourthCursorLength :
      (fourthCursorWord problem).length =
        (BuilderFourthClauseSeparatorStep.cursorWord problem).length + 7 := by
    simp [fourthCursorWord, hThirdCursorLength]
  rw [rawTimeBound_eval]
  unfold workSteps suffixWorkSteps trueTrueFalseSuffixWorkSteps
    trueFalseSuffixWorkSteps signTokenCursorWorkSteps
    unaryTokenCursorWorkSteps secondUnaryTokenCursorWorkSteps
    terminatorTokenCursorWorkSteps firstCursorWorkSteps secondCursorWorkSteps
    thirdCursorWorkSteps fourthCursorWorkSteps
    BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
  rw [hFirstCursorLength, hSecondCursorLength, hThirdCursorLength,
    hFourthCursorLength]
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

/-! ### Fail-closed trace boundaries -/

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

private theorem stuck_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (config : WorkConfiguration)
    (hHalted : (machine problem).isHalted config = false)
    (hStep : workStep? (machine problem) config = none) :
    (let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  have hRun := workRun_eq_self_of_workStep?_eq_none
    (machine problem) config fuel hStep
  rw [hRun]
  exact verdict_timeout_of_not_halted problem config hHalted

private theorem state_ne_accept_of_not_halted
    (localMachine : WorkMachine) (config : WorkConfiguration)
    (hHalted : localMachine.isHalted config = false) :
    config.state ≠ localMachine.acceptState := by
  intro hState
  unfold WorkMachine.isHalted at hHalted
  rw [hState, (nat_beq_true_iff _ _).mpr rfl] at hHalted
  contradiction

private theorem findWorkRule_none_of_workStep_none_local
    (localMachine : WorkMachine) (config : WorkConfiguration)
    (hHalted : localMachine.isHalted config = false)
    (hStep : workStep? localMachine config = none) :
    findWorkRule localMachine.rules config.state config.tape.head = none := by
  unfold workStep? at hStep
  rw [hHalted] at hStep
  cases hFind : findWorkRule localMachine.rules config.state
      config.tape.head with
  | none => rfl
  | some rule =>
      rw [hFind] at hStep
      contradiction

private theorem findWorkRule_first_of_none_local
    (first second : WorkMachine) (state : Nat) (symbol : WorkSymbol)
    (hAccept : state ≠ first.acceptState)
    (hFind : findWorkRule first.rules state symbol = none) :
    findWorkRule (BuilderFirstClausePrefix.WorkChain.machine first second).rules
        (BuilderFirstClausePrefix.WorkChain.firstState state) symbol = none := by
  have hBridge : findWorkRule
      (BuilderFirstClausePrefix.WorkChain.bridgeRules first second)
      (BuilderFirstClausePrefix.WorkChain.firstState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    intro h
    exact hAccept
      (BuilderFirstClausePrefix.WorkChain.firstState_injective h).symm
  have hFirst := findWorkRule_rename
    BuilderFirstClausePrefix.WorkChain.firstState
    BuilderFirstClausePrefix.WorkChain.firstState_injective
    first.rules state symbol
  rw [hFind] at hFirst
  have hSecond : findWorkRule
      (second.rules.map (renameRule
        BuilderFirstClausePrefix.WorkChain.secondState))
      (BuilderFirstClausePrefix.WorkChain.firstState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact Ne.symm
      (BuilderFirstClausePrefix.WorkChain.firstState_ne_secondState _ _)
  unfold BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hFirst]
  exact hSecond

private theorem findWorkRule_second_of_none_local
    (first second : WorkMachine) (state : Nat) (symbol : WorkSymbol)
    (hFind : findWorkRule second.rules state symbol = none) :
    findWorkRule (BuilderFirstClausePrefix.WorkChain.machine first second).rules
        (BuilderFirstClausePrefix.WorkChain.secondState state) symbol = none := by
  have hBridge : findWorkRule
      (BuilderFirstClausePrefix.WorkChain.bridgeRules first second)
      (BuilderFirstClausePrefix.WorkChain.secondState state) symbol = none := by
    apply findWorkRule_launchRules_none_of_source_ne
    exact BuilderFirstClausePrefix.WorkChain.firstState_ne_secondState _ _
  have hFirst : findWorkRule
      (first.rules.map (renameRule
        BuilderFirstClausePrefix.WorkChain.firstState))
      (BuilderFirstClausePrefix.WorkChain.secondState state) symbol = none := by
    apply findWorkRule_renamedRules_none
    intro source
    exact BuilderFirstClausePrefix.WorkChain.firstState_ne_secondState _ _
  have hSecond := findWorkRule_rename
    BuilderFirstClausePrefix.WorkChain.secondState
    BuilderFirstClausePrefix.WorkChain.secondState_injective
    second.rules state symbol
  rw [hFind] at hSecond
  unfold BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
  rw [findWorkRule_append_of_none _ _ _ _ hBridge,
    findWorkRule_append_of_none _ _ _ _ hFirst]
  exact hSecond

private theorem first_workStep_none_of_local
    (first second : WorkMachine) (config : WorkConfiguration)
    (hAccept : config.state ≠ first.acceptState)
    (hLocalHalted : first.isHalted config = false)
    (hLocalStep : workStep? first config = none) :
    workStep? (BuilderFirstClausePrefix.WorkChain.machine first second)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          config) = none := by
  have hFind := findWorkRule_none_of_workStep_none_local first config
    hLocalHalted hLocalStep
  have hGlobalFind := findWorkRule_first_of_none_local first second
    config.state config.tape.head hAccept hFind
  unfold workStep?
  rw [BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
    first second config]
  change
    (match findWorkRule
        (BuilderFirstClausePrefix.WorkChain.machine first second).rules
        (BuilderFirstClausePrefix.WorkChain.firstState config.state)
        config.tape.head with
     | none => none
     | some rule => some (applyWorkRule rule
         (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
           config))) = none
  rw [hGlobalFind]

private theorem second_workStep_none_of_local
    (first second : WorkMachine) (config : WorkConfiguration)
    (hLocalHalted : second.isHalted config = false)
    (hLocalStep : workStep? second config = none) :
    workStep? (BuilderFirstClausePrefix.WorkChain.machine first second)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          config) = none := by
  have hFind := findWorkRule_none_of_workStep_none_local second config
    hLocalHalted hLocalStep
  have hGlobalFind := findWorkRule_second_of_none_local first second
    config.state config.tape.head hFind
  unfold workStep?
  rw [BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
    first second config hLocalHalted]
  change
    (match findWorkRule
        (BuilderFirstClausePrefix.WorkChain.machine first second).rules
        (BuilderFirstClausePrefix.WorkChain.secondState config.state)
        config.tape.head with
     | none => none
     | some rule => some (applyWorkRule rule
         (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
           config))) = none
  rw [hGlobalFind]

private theorem first_stuck_pair
    (first second : WorkMachine) (config : WorkConfiguration)
    (hLocalHalted : first.isHalted config = false)
    (hLocalStep : workStep? first config = none) :
    let lifted := renameConfiguration
      BuilderFirstClausePrefix.WorkChain.firstState config
    (BuilderFirstClausePrefix.WorkChain.machine first second).isHalted
        lifted = false ∧
      workStep? (BuilderFirstClausePrefix.WorkChain.machine first second)
        lifted = none := by
  dsimp
  constructor
  · exact BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      first second config
  · exact first_workStep_none_of_local first second config
      (state_ne_accept_of_not_halted first config hLocalHalted)
      hLocalHalted hLocalStep

private theorem second_stuck_pair
    (first second : WorkMachine) (config : WorkConfiguration)
    (hLocalHalted : second.isHalted config = false)
    (hLocalStep : workStep? second config = none) :
    let lifted := renameConfiguration
      BuilderFirstClausePrefix.WorkChain.secondState config
    (BuilderFirstClausePrefix.WorkChain.machine first second).isHalted
        lifted = false ∧
      workStep? (BuilderFirstClausePrefix.WorkChain.machine first second)
        lifted = none := by
  dsimp
  constructor
  · exact
      BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
        first second config hLocalHalted
  · exact second_workStep_none_of_local first second config
      hLocalHalted hLocalStep

def signAppenderGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        config))

def firstUnaryAppenderGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          config)))

def secondUnaryAppenderGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
            config))))

def terminatorAppenderGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
            config))))

private theorem signAppender_stuck_pair {language : Language}
    (problem : VerifierTableauProblem language) (bad : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted bad = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine bad = none) :
    (machine problem).isHalted
        (signAppenderGlobalConfiguration problem bad) = false ∧
      workStep? (machine problem)
        (signAppenderGlobalConfiguration problem bad) = none := by
  have hAppenderHalted :
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender.isHalted
        bad = false := by
    change BuilderTokenAppender.machine.isHalted bad = false
    exact hLocalHalted
  have hAppenderStep : workStep?
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender bad =
        none := by
    change workStep? BuilderTokenAppender.machine bad = none
    exact hLocalStep
  have hComponent := first_stuck_pair
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine bad
    hAppenderHalted hAppenderStep
  have hSuffix := first_stuck_pair
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState bad)
    hComponent.1 hComponent.2
  have hGlobal := second_stuck_pair
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState bad))
    (by simpa [SecondLiteralSuffix.machine] using hSuffix.1)
    (by simpa [SecondLiteralSuffix.machine] using hSuffix.2)
  simpa [machine, signAppenderGlobalConfiguration,
    SecondLiteralSuffix.machine,
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine] using
      hGlobal

private theorem firstUnaryAppender_stuck_pair {language : Language}
    (problem : VerifierTableauProblem language) (bad : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted bad = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine bad = none) :
    (machine problem).isHalted
        (firstUnaryAppenderGlobalConfiguration problem bad) = false ∧
      workStep? (machine problem)
        (firstUnaryAppenderGlobalConfiguration problem bad) = none := by
  have hAppenderHalted : TrueTokenCursor.appender.isHalted bad = false := by
    change BuilderTokenAppender.machine.isHalted bad = false
    exact hLocalHalted
  have hAppenderStep : workStep? TrueTokenCursor.appender bad = none := by
    change workStep? BuilderTokenAppender.machine bad = none
    exact hLocalStep
  have hComponent := first_stuck_pair TrueTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine bad
    hAppenderHalted hAppenderStep
  have hTail := first_stuck_pair TrueTokenCursor.machine
    TrueFalseSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState bad)
    (by simpa [TrueTokenCursor.machine] using hComponent.1)
    (by simpa [TrueTokenCursor.machine] using hComponent.2)
  have hSuffix := second_stuck_pair
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState bad))
    (by simpa [TrueTrueFalseSuffix.machine] using hTail.1)
    (by simpa [TrueTrueFalseSuffix.machine] using hTail.2)
  have hGlobal := second_stuck_pair
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          bad)))
    (by simpa [SecondLiteralSuffix.machine] using hSuffix.1)
    (by simpa [SecondLiteralSuffix.machine] using hSuffix.2)
  simpa [machine, firstUnaryAppenderGlobalConfiguration,
    SecondLiteralSuffix.machine, TrueTrueFalseSuffix.machine,
    TrueTokenCursor.machine] using hGlobal

private theorem secondUnaryAppender_stuck_pair {language : Language}
    (problem : VerifierTableauProblem language) (bad : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted bad = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine bad = none) :
    (machine problem).isHalted
        (secondUnaryAppenderGlobalConfiguration problem bad) = false ∧
      workStep? (machine problem)
        (secondUnaryAppenderGlobalConfiguration problem bad) = none := by
  have hAppenderHalted : TrueTokenCursor.appender.isHalted bad = false := by
    change BuilderTokenAppender.machine.isHalted bad = false
    exact hLocalHalted
  have hAppenderStep : workStep? TrueTokenCursor.appender bad = none := by
    change workStep? BuilderTokenAppender.machine bad = none
    exact hLocalStep
  have hComponent := first_stuck_pair TrueTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine bad
    hAppenderHalted hAppenderStep
  have hTail := first_stuck_pair TrueTokenCursor.machine
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState bad)
    (by simpa [TrueTokenCursor.machine] using hComponent.1)
    (by simpa [TrueTokenCursor.machine] using hComponent.2)
  have hDoubleTail := second_stuck_pair TrueTokenCursor.machine
    TrueFalseSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState bad))
    (by simpa [TrueFalseSuffix.machine] using hTail.1)
    (by simpa [TrueFalseSuffix.machine] using hTail.2)
  have hSuffix := second_stuck_pair
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          bad)))
    (by simpa [TrueTrueFalseSuffix.machine] using hDoubleTail.1)
    (by simpa [TrueTrueFalseSuffix.machine] using hDoubleTail.2)
  have hGlobal := second_stuck_pair
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
            bad))))
    (by simpa [SecondLiteralSuffix.machine] using hSuffix.1)
    (by simpa [SecondLiteralSuffix.machine] using hSuffix.2)
  simpa [machine, secondUnaryAppenderGlobalConfiguration,
    SecondLiteralSuffix.machine, TrueTrueFalseSuffix.machine,
    TrueFalseSuffix.machine, TrueTokenCursor.machine] using hGlobal

private theorem terminatorAppender_stuck_pair {language : Language}
    (problem : VerifierTableauProblem language) (bad : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted bad = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine bad = none) :
    (machine problem).isHalted
        (terminatorAppenderGlobalConfiguration problem bad) = false ∧
      workStep? (machine problem)
        (terminatorAppenderGlobalConfiguration problem bad) = none := by
  have hAppenderHalted :
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender.isHalted
        bad = false := by
    change BuilderTokenAppender.machine.isHalted bad = false
    exact hLocalHalted
  have hAppenderStep : workStep?
      BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender bad =
        none := by
    change workStep? BuilderTokenAppender.machine bad = none
    exact hLocalStep
  have hComponent := first_stuck_pair
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine bad
    hAppenderHalted hAppenderStep
  have hTail := second_stuck_pair TrueTokenCursor.machine
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState bad)
    (by
      simpa [BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine]
        using hComponent.1)
    (by
      simpa [BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine]
        using hComponent.2)
  have hDoubleTail := second_stuck_pair TrueTokenCursor.machine
    TrueFalseSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState bad))
    (by simpa [TrueFalseSuffix.machine] using hTail.1)
    (by simpa [TrueFalseSuffix.machine] using hTail.2)
  have hSuffix := second_stuck_pair
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          bad)))
    (by simpa [TrueTrueFalseSuffix.machine] using hDoubleTail.1)
    (by simpa [TrueTrueFalseSuffix.machine] using hDoubleTail.2)
  have hGlobal := second_stuck_pair
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
            bad))))
    (by simpa [SecondLiteralSuffix.machine] using hSuffix.1)
    (by simpa [SecondLiteralSuffix.machine] using hSuffix.2)
  simpa [machine, terminatorAppenderGlobalConfiguration,
    SecondLiteralSuffix.machine, TrueTrueFalseSuffix.machine,
    TrueFalseSuffix.machine,
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine] using
      hGlobal

private theorem timeout_of_stuck_pair {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (config : WorkConfiguration)
    (hPair : (machine problem).isHalted config = false ∧
      workStep? (machine problem) config = none) :
    (let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout :=
  stuck_timeout problem fuel config hPair.1 hPair.2

theorem malformedSignAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedTallyConfiguration
        request left right
     let global := signAppenderGlobalConfiguration problem bad
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact timeout_of_stuck_pair problem fuel _
    (signAppender_stuck_pair problem _
      (BuilderTokenAppender.malformedTallySymbol_isHalted_false
        request left right)
      (BuilderTokenAppender.malformedTallySymbol_workStep_none
        request left right))

theorem malformedFirstUnaryAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedTallyConfiguration
        request left right
     let global := firstUnaryAppenderGlobalConfiguration problem bad
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact timeout_of_stuck_pair problem fuel _
    (firstUnaryAppender_stuck_pair problem _
      (BuilderTokenAppender.malformedTallySymbol_isHalted_false
        request left right)
      (BuilderTokenAppender.malformedTallySymbol_workStep_none
        request left right))

theorem malformedSecondUnaryAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedTallyConfiguration
        request left right
     let global := secondUnaryAppenderGlobalConfiguration problem bad
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact timeout_of_stuck_pair problem fuel _
    (secondUnaryAppender_stuck_pair problem _
      (BuilderTokenAppender.malformedTallySymbol_isHalted_false
        request left right)
      (BuilderTokenAppender.malformedTallySymbol_workStep_none
        request left right))

theorem malformedTerminatorAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedTallyConfiguration
        request left right
     let global := terminatorAppenderGlobalConfiguration problem bad
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact timeout_of_stuck_pair problem fuel _
    (terminatorAppender_stuck_pair problem _
      (BuilderTokenAppender.malformedTallySymbol_isHalted_false
        request left right)
      (BuilderTokenAppender.malformedTallySymbol_workStep_none
        request left right))

theorem malformedSignAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedOutputConfiguration
        request left right
     let global := signAppenderGlobalConfiguration problem bad
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact timeout_of_stuck_pair problem fuel _
    (signAppender_stuck_pair problem _
      (BuilderTokenAppender.malformedOutputSymbol_isHalted_false
        request left right)
      (BuilderTokenAppender.malformedOutputSymbol_workStep_none
        request left right))

theorem malformedFirstUnaryAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedOutputConfiguration
        request left right
     let global := firstUnaryAppenderGlobalConfiguration problem bad
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact timeout_of_stuck_pair problem fuel _
    (firstUnaryAppender_stuck_pair problem _
      (BuilderTokenAppender.malformedOutputSymbol_isHalted_false
        request left right)
      (BuilderTokenAppender.malformedOutputSymbol_workStep_none
        request left right))

theorem malformedSecondUnaryAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedOutputConfiguration
        request left right
     let global := secondUnaryAppenderGlobalConfiguration problem bad
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact timeout_of_stuck_pair problem fuel _
    (secondUnaryAppender_stuck_pair problem _
      (BuilderTokenAppender.malformedOutputSymbol_isHalted_false
        request left right)
      (BuilderTokenAppender.malformedOutputSymbol_workStep_none
        request left right))

theorem malformedTerminatorAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedOutputConfiguration
        request left right
     let global := terminatorAppenderGlobalConfiguration problem bad
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact timeout_of_stuck_pair problem fuel _
    (terminatorAppender_stuck_pair problem _
      (BuilderTokenAppender.malformedOutputSymbol_isHalted_false
        request left right)
      (BuilderTokenAppender.malformedOutputSymbol_workStep_none
        request left right))

private def cursorDeadConfiguration (tape : WorkTape) : WorkConfiguration :=
  { state := 4, tape := tape }

private theorem cursorMalformed_workStep
    (left right : List WorkSymbol) :
    workStep? BuilderDynamicTokenCursorStep.CursorAdvance.machine
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right) =
      some (cursorDeadConfiguration
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right).tape) := by
  simpa [cursorDeadConfiguration] using
    BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratch_enters_dead
      left right

private theorem cursorDead_workStep (tape : WorkTape) :
    workStep? BuilderDynamicTokenCursorStep.CursorAdvance.machine
        (cursorDeadConfiguration tape) =
      some (cursorDeadConfiguration tape) := by
  simpa [cursorDeadConfiguration] using
    BuilderDynamicTokenCursorStep.CursorAdvance.deadState_workStep tape

def signCursorGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        config))

def firstUnaryCursorGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          config)))

def secondUnaryCursorGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
            config))))

def terminatorCursorGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
            config))))

private theorem signCursorGlobal_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderDynamicTokenCursorStep.CursorAdvance.machine
      config = some next) :
    workStep? (machine problem) (signCursorGlobalConfiguration problem config) =
      some (signCursorGlobalConfiguration problem next) := by
  have hComponent := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine config next hStep
  have hSuffix := BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine _ _ (by
      simpa [BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine]
        using hComponent)
  have hGlobal := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine _ _ (by
      simpa [SecondLiteralSuffix.machine] using hSuffix)
  simpa [machine, signCursorGlobalConfiguration,
    SecondLiteralSuffix.machine,
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine] using
      hGlobal

private theorem firstUnaryCursorGlobal_workStep_of_some
    {language : Language} (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderDynamicTokenCursorStep.CursorAdvance.machine
      config = some next) :
    workStep? (machine problem)
        (firstUnaryCursorGlobalConfiguration problem config) =
      some (firstUnaryCursorGlobalConfiguration problem next) := by
  have hComponent := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    TrueTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine config next hStep
  have hTail := BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
    TrueTokenCursor.machine TrueFalseSuffix.machine _ _ (by
      simpa [TrueTokenCursor.machine] using hComponent)
  have hSuffix := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine _ _ (by
      simpa [TrueTrueFalseSuffix.machine] using hTail)
  have hGlobal := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine _ _ (by
      simpa [SecondLiteralSuffix.machine] using hSuffix)
  simpa [machine, firstUnaryCursorGlobalConfiguration,
    SecondLiteralSuffix.machine, TrueTrueFalseSuffix.machine,
    TrueTokenCursor.machine] using hGlobal

private theorem secondUnaryCursorGlobal_workStep_of_some
    {language : Language} (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderDynamicTokenCursorStep.CursorAdvance.machine
      config = some next) :
    workStep? (machine problem)
        (secondUnaryCursorGlobalConfiguration problem config) =
      some (secondUnaryCursorGlobalConfiguration problem next) := by
  have hComponent := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    TrueTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine config next hStep
  have hTail := BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
    TrueTokenCursor.machine
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine _ _ (by
      simpa [TrueTokenCursor.machine] using hComponent)
  have hDoubleTail :=
    BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
      TrueTokenCursor.machine TrueFalseSuffix.machine _ _ (by
        simpa [TrueFalseSuffix.machine] using hTail)
  have hSuffix := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine _ _ (by
      simpa [TrueTrueFalseSuffix.machine] using hDoubleTail)
  have hGlobal := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine _ _ (by
      simpa [SecondLiteralSuffix.machine] using hSuffix)
  simpa [machine, secondUnaryCursorGlobalConfiguration,
    SecondLiteralSuffix.machine, TrueTrueFalseSuffix.machine,
    TrueFalseSuffix.machine, TrueTokenCursor.machine] using hGlobal

private theorem terminatorCursorGlobal_workStep_of_some
    {language : Language} (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderDynamicTokenCursorStep.CursorAdvance.machine
      config = some next) :
    workStep? (machine problem)
        (terminatorCursorGlobalConfiguration problem config) =
      some (terminatorCursorGlobalConfiguration problem next) := by
  have hComponent := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine config next hStep
  have hTail := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    TrueTokenCursor.machine
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine _ _ (by
      simpa [BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine]
        using hComponent)
  have hDoubleTail :=
    BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
      TrueTokenCursor.machine TrueFalseSuffix.machine _ _ (by
        simpa [TrueFalseSuffix.machine] using hTail)
  have hSuffix := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine
    TrueTrueFalseSuffix.machine _ _ (by
      simpa [TrueTrueFalseSuffix.machine] using hDoubleTail)
  have hGlobal := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderFourthClauseFirstLiteralPrefix.machine problem)
    SecondLiteralSuffix.machine _ _ (by
      simpa [SecondLiteralSuffix.machine] using hSuffix)
  simpa [machine, terminatorCursorGlobalConfiguration,
    SecondLiteralSuffix.machine, TrueTrueFalseSuffix.machine,
    TrueFalseSuffix.machine,
    BuilderSecondClauseFirstLiteralPrefix.FalseTokenCursor.machine] using
      hGlobal

private theorem workRun_eq_self_of_workStep_self
    (localMachine : WorkMachine) (fuel : Nat) (config : WorkConfiguration)
    (hStep : workStep? localMachine config = some config) :
    workRun localMachine fuel config = config := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      unfold workRun
      rw [hStep]
      exact ih

private theorem workRun_succ_eq_of_step_and_loop
    (localMachine : WorkMachine) (fuel : Nat)
    (start dead : WorkConfiguration)
    (hStart : workStep? localMachine start = some dead)
    (hDead : workStep? localMachine dead = some dead) :
    workRun localMachine (fuel + 1) start = dead := by
  unfold workRun
  rw [hStart]
  exact workRun_eq_self_of_workStep_self localMachine fuel dead hDead

private theorem isHalted_false_of_workStep_some
    (localMachine : WorkMachine) (config next : WorkConfiguration)
    (hStep : workStep? localMachine config = some next) :
    localMachine.isHalted config = false := by
  cases hHalted : localMachine.isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem malformedCursorScratch_timeout_of_lift {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (left right : List WorkSymbol)
    (embed : WorkConfiguration → WorkConfiguration)
    (hLift : ∀ config next,
      workStep? BuilderDynamicTokenCursorStep.CursorAdvance.machine config =
        some next →
      workStep? (machine problem) (embed config) = some (embed next)) :
    (let bad := embed
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine problem) fuel bad
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let localBad :=
    BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
      left right
  let localDead := cursorDeadConfiguration localBad.tape
  let bad := embed localBad
  let dead := embed localDead
  have hBadStep : workStep? (machine problem) bad = some dead := by
    simpa [bad, dead, localBad, localDead] using
      hLift localBad localDead (cursorMalformed_workStep left right)
  have hDeadStep : workStep? (machine problem) dead = some dead := by
    simpa [dead, localDead] using
      hLift localDead localDead (cursorDead_workStep localBad.tape)
  cases fuel with
  | zero =>
      exact verdict_timeout_of_not_halted problem bad
        (isHalted_false_of_workStep_some (machine problem) bad dead hBadStep)
  | succ fuel =>
      have hRun := workRun_succ_eq_of_step_and_loop
        (machine problem) fuel bad dead hBadStep hDeadStep
      change
        (let result := workRun (machine problem) (fuel + 1) bad
         if result.state == (machine problem).acceptState then
           WorkVerdict.accept
         else if result.state == (machine problem).rejectState then
           WorkVerdict.reject
         else WorkVerdict.timeout) = WorkVerdict.timeout
      rw [hRun]
      exact verdict_timeout_of_not_halted problem dead
        (isHalted_false_of_workStep_some
          (machine problem) dead dead hDeadStep)

theorem malformedSignCursorScratch_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (left right : List WorkSymbol) :
    (let bad := signCursorGlobalConfiguration problem
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine problem) fuel bad
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact malformedCursorScratch_timeout_of_lift problem fuel left right
    (signCursorGlobalConfiguration problem)
    (signCursorGlobal_workStep_of_some problem)

theorem malformedFirstUnaryCursorScratch_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (left right : List WorkSymbol) :
    (let bad := firstUnaryCursorGlobalConfiguration problem
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine problem) fuel bad
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact malformedCursorScratch_timeout_of_lift problem fuel left right
    (firstUnaryCursorGlobalConfiguration problem)
    (firstUnaryCursorGlobal_workStep_of_some problem)

theorem malformedSecondUnaryCursorScratch_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (left right : List WorkSymbol) :
    (let bad := secondUnaryCursorGlobalConfiguration problem
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine problem) fuel bad
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact malformedCursorScratch_timeout_of_lift problem fuel left right
    (secondUnaryCursorGlobalConfiguration problem)
    (secondUnaryCursorGlobal_workStep_of_some problem)

theorem malformedTerminatorCursorScratch_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (left right : List WorkSymbol) :
    (let bad := terminatorCursorGlobalConfiguration problem
        (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
          left right)
     let result := workRun (machine problem) fuel bad
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  exact malformedCursorScratch_timeout_of_lift problem fuel left right
    (terminatorCursorGlobalConfiguration problem)
    (terminatorCursorGlobal_workStep_of_some problem)

/-! ### Exact pre-launch endpoints -/

private theorem workRunExact_prefix_has_step {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ (count suffix : Nat) (initial final : WorkConfiguration),
      workRunExact? (machine problem) (count + suffix + 1) initial =
          some final →
      ∃ boundary next,
        workRunExact? (machine problem) count initial = some boundary ∧
        workStep? (machine problem) boundary = some next := by
  intro count
  induction count with
  | zero =>
      intro suffix initial final hRun
      rw [show 0 + suffix + 1 = Nat.succ suffix by omega] at hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next =>
                 workRunExact? (machine problem) suffix next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          exact ⟨initial, next, rfl, hStep⟩
  | succ count ih =>
      intro suffix initial final hRun
      rw [show count + 1 + suffix + 1 =
        Nat.succ (count + suffix + 1) by omega] at hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next =>
                 workRunExact? (machine problem)
                   (count + suffix + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some first =>
          have hTail : workRunExact? (machine problem)
              (count + suffix + 1) first = some final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some next =>
                   workRunExact? (machine problem)
                     (count + suffix + 1) next) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih suffix first final hTail with
            ⟨boundary, next, hPrefix, hNext⟩
          refine ⟨boundary, next, ?_, hNext⟩
          rw [show count + 1 = Nat.succ count by omega]
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next =>
                 workRunExact? (machine problem) count next) =
              some boundary
          rw [hStep]
          exact hPrefix

private theorem strictPrefix_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (hFuel : fuel < workSteps problem) :
    workBoundedDecide (machine problem) fuel
        (rawInputWorkTape problem.input) = .timeout := by
  obtain ⟨suffix, hTotal⟩ :
      ∃ suffix, workSteps problem = fuel + suffix + 1 := by
    refine ⟨workSteps problem - fuel - 1, ?_⟩
    omega
  let initial := workStartConfiguration (machine problem)
    (rawInputWorkTape problem.input)
  let final := finalConfiguration problem
  have hExact := workRunExact problem
  change workRunExact? (machine problem) (workSteps problem) initial =
    some final at hExact
  rw [hTotal] at hExact
  rcases workRunExact_prefix_has_step problem fuel suffix initial final hExact
      with ⟨boundary, next, hPrefix, hStep⟩
  have hRun : workRun (machine problem) fuel initial = boundary :=
    workRun_eq_of_workRunExact (machine problem) fuel initial boundary hPrefix
  unfold workBoundedDecide
  change
    (let result := workRun (machine problem) fuel initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  exact verdict_timeout_of_not_halted problem boundary
    (isHalted_false_of_workStep_some
      (machine problem) boundary next hStep)

/-- The inherited first-literal endpoint is globally nonhalting until the
outer bridge launches the second literal. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFourthClauseFirstLiteralPrefix.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  exact strictPrefix_timeout problem _ (by
    unfold workSteps
    omega)

/-- The sign appender endpoint is nonhalting before its cursor bridge. -/
theorem signAppenderEndpoint_before_cursor_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFourthClauseFirstLiteralPrefix.workSteps problem + 1 +
          firstAppenderWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  exact strictPrefix_timeout problem _ (by
    unfold workSteps suffixWorkSteps signTokenCursorWorkSteps
    omega)

/-- The sign cursor endpoint is nonhalting before the first unary unit. -/
theorem signCursorEndpoint_before_firstUnary_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFourthClauseFirstLiteralPrefix.workSteps problem + 1 +
          signTokenCursorWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  exact strictPrefix_timeout problem _ (by
    unfold workSteps suffixWorkSteps
    omega)

/-- The first unary appender endpoint is nonhalting before its cursor. -/
theorem firstUnaryAppenderEndpoint_before_cursor_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFourthClauseFirstLiteralPrefix.workSteps problem + 1 +
          signTokenCursorWorkSteps problem + 1 +
          secondAppenderWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  exact strictPrefix_timeout problem _ (by
    unfold workSteps suffixWorkSteps trueTrueFalseSuffixWorkSteps
      unaryTokenCursorWorkSteps
    omega)

/-- The first unary cursor endpoint is nonhalting before the second unit. -/
theorem firstUnaryCursorEndpoint_before_secondUnary_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFourthClauseFirstLiteralPrefix.workSteps problem + 1 +
          signTokenCursorWorkSteps problem + 1 +
          unaryTokenCursorWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  exact strictPrefix_timeout problem _ (by
    unfold workSteps suffixWorkSteps trueTrueFalseSuffixWorkSteps
    omega)

/-- The second unary appender endpoint is nonhalting before its cursor. -/
theorem secondUnaryAppenderEndpoint_before_cursor_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFourthClauseFirstLiteralPrefix.workSteps problem + 1 +
          signTokenCursorWorkSteps problem + 1 +
          unaryTokenCursorWorkSteps problem + 1 +
          thirdAppenderWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  exact strictPrefix_timeout problem _ (by
    unfold workSteps suffixWorkSteps trueTrueFalseSuffixWorkSteps
      trueFalseSuffixWorkSteps secondUnaryTokenCursorWorkSteps
    omega)

/-- The second unary cursor endpoint is nonhalting before the terminator. -/
theorem secondUnaryCursorEndpoint_before_terminator_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFourthClauseFirstLiteralPrefix.workSteps problem + 1 +
          signTokenCursorWorkSteps problem + 1 +
          unaryTokenCursorWorkSteps problem + 1 +
          secondUnaryTokenCursorWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  exact strictPrefix_timeout problem _ (by
    unfold workSteps suffixWorkSteps trueTrueFalseSuffixWorkSteps
      trueFalseSuffixWorkSteps
    omega)

/-- The terminator appender endpoint is nonhalting before its final cursor. -/
theorem terminatorAppenderEndpoint_before_cursor_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFourthClauseFirstLiteralPrefix.workSteps problem + 1 +
          signTokenCursorWorkSteps problem + 1 +
          unaryTokenCursorWorkSteps problem + 1 +
          secondUnaryTokenCursorWorkSteps problem + 1 +
          fourthAppenderWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  exact strictPrefix_timeout problem _ (by
    unfold workSteps suffixWorkSteps trueTrueFalseSuffixWorkSteps
      trueFalseSuffixWorkSteps terminatorTokenCursorWorkSteps
    omega)

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

private theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) : 0 < workSteps problem := by
  unfold workSteps
  omega

/-- Removing the final successful cursor transition leaves a nonhalting
state, so the exact composed trace cannot accept one work step early. -/
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
    (machine problem) before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun (machine problem) short initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  exact verdict_timeout_of_not_halted problem before hNotHalted

end BuilderFourthClauseSecondLiteralPrefix

end CookLevin

end PNP.Concrete
