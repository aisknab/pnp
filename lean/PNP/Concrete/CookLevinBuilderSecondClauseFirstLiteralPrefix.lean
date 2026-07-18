/-
Copyright (c) 2026 PNP Labs.

The first complete negative literal of the second canonical Cook--Levin
clause.

The machine in this file composes the complete second-clause-separator prefix
with two state-selected false-token appenders and two copies of the existing
unary cursor advance.  Every raw input therefore emits the negative literal
on variable zero and leaves the retained coordinate on the next literal sign.
This is a fixed two-token prefix, not a general schedule decoder, a complete
cursor loop, or a complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderSecondClauseSeparatorStep

namespace PNP.Concrete

namespace CookLevin

namespace BuilderSecondClauseFirstLiteralPrefix

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Selected false-token appenders followed by cursor advances -/

namespace FalseTokenCursor

/-- The complete literal appender table entered at the state selecting
`CNFToken.f`. -/
def appender : WorkMachine :=
  { rules := BuilderTokenAppender.machine.rules
    startState := BuilderTokenAppender.seekInputState .f
    acceptState := BuilderTokenAppender.machine.acceptState
    rejectState := BuilderTokenAppender.machine.rejectState }

/-- One selected false-token append followed by the existing unary cursor
advance.  Only the cursor component supplies global halts. -/
def machine : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine

private theorem appender_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept appender := by
  intro rule hRule
  change rule.sourceState ≠ BuilderTokenAppender.machine.acceptState
  change rule ∈ BuilderTokenAppender.machine.rules at hRule
  decide +revert

private theorem cursor_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      BuilderDynamicTokenCursorStep.CursorAdvance.machine := by
  exact BuilderDynamicTokenCursorStep.CursorAdvance.rule_source_ne_acceptState

theorem rules_length : machine.rules.length = 113 := by
  have hAppender : appender.rules.length = 59 := by
    simpa [appender, BuilderTokenAppender.machine] using
      BuilderTokenAppender.rules_length
  have hCursor :
      BuilderDynamicTokenCursorStep.CursorAdvance.machine.rules.length = 45 := by
    simpa [BuilderDynamicTokenCursorStep.CursorAdvance.machine] using
      BuilderDynamicTokenCursorStep.CursorAdvance.rules_length
  unfold machine BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
    BuilderFirstClausePrefix.WorkChain.bridgeRules
  simp only [List.length_append, List.length_map]
  rw [hAppender, hCursor]
  rfl

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    appender BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (by
      change BuilderTokenAppender.machine.rules.Pairwise
        (fun left right =>
          (left.sourceState, left.readSymbol) ≠
            (right.sourceState, right.readSymbol))
      exact BuilderTokenAppender.rules_pairwise_query_distinct)
    BuilderDynamicTokenCursorStep.CursorAdvance.rules_pairwise_query_distinct
    appender_noRuleAtAccept

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    appender BuilderDynamicTokenCursorStep.CursorAdvance.machine
    BuilderDynamicTokenCursorStep.CursorAdvance.machine_acceptState_ne_rejectState

theorem rule_source_ne_acceptState (rule : WorkRule)
    (hRule : rule ∈ machine.rules) :
    rule.sourceState ≠ machine.acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    appender BuilderDynamicTokenCursorStep.CursorAdvance.machine
    cursor_noRuleAtAccept rule hRule

end FalseTokenCursor

namespace FirstLiteralSuffix

/-- Two collision-free copies of the fixed false-token/cursor transition.
Only the second copy supplies global halts. -/
def machine : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine FalseTokenCursor.machine
    FalseTokenCursor.machine

private theorem first_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      FalseTokenCursor.machine := by
  exact FalseTokenCursor.rule_source_ne_acceptState

private theorem second_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      FalseTokenCursor.machine := by
  exact FalseTokenCursor.rule_source_ne_acceptState

theorem rules_length : machine.rules.length = 235 := by
  have hComponent := FalseTokenCursor.rules_length
  unfold machine BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
    BuilderFirstClausePrefix.WorkChain.bridgeRules
  simp only [List.length_append, List.length_map]
  rw [hComponent]
  rfl

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    FalseTokenCursor.machine FalseTokenCursor.machine
    FalseTokenCursor.rules_pairwise_query_distinct
    FalseTokenCursor.rules_pairwise_query_distinct first_noRuleAtAccept

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    FalseTokenCursor.machine FalseTokenCursor.machine
    FalseTokenCursor.machine_acceptState_ne_rejectState

theorem rule_source_ne_acceptState (rule : WorkRule)
    (hRule : rule ∈ machine.rules) :
    rule.sourceState ≠ machine.acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    FalseTokenCursor.machine FalseTokenCursor.machine
    second_noRuleAtAccept rule hRule

end FirstLiteralSuffix

private theorem predecessor_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderSecondClauseSeparatorStep.machine problem) := by
  exact BuilderSecondClauseSeparatorStep.rule_source_ne_acceptState problem

private theorem suffix_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      FirstLiteralSuffix.machine := by
  exact FirstLiteralSuffix.rule_source_ne_acceptState

/-- One literal finite work machine from raw input through the first complete
negative literal of clause two. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      1610 +
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
            problem.verifier) := by
  have hPrefix := BuilderSecondClauseSeparatorStep.rules_length problem
  have hSuffix := FirstLiteralSuffix.rules_length
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
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine
    (BuilderSecondClauseSeparatorStep.rules_pairwise_query_distinct problem)
    FirstLiteralSuffix.rules_pairwise_query_distinct
    (predecessor_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine
    FirstLiteralSuffix.machine_acceptState_ne_rejectState

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine
    suffix_noRuleAtAccept rule hRule

/-! ### Exact workspace and trace -/

def firstTokenOutput {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  BuilderSecondClauseSeparatorStep.secondClauseStartTokens problem ++ [.f]

def secondClauseFirstLiteralTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  firstTokenOutput problem ++ [.f]

/-- Active cursor word at the first negative sign coordinate. -/
def firstCursorWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderSecondClauseSeparatorStep.cursorWord problem ++
    [BuilderUnaryPolynomial.unitSymbol]

/-- Active cursor word at the unary-zero terminator coordinate. -/
def secondCursorWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  firstCursorWord problem ++ [BuilderUnaryPolynomial.unitSymbol]

private def cursorOutsideTail {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (BuilderSecondClauseSeparatorStep.finalOutside problem).drop
    ((firstCursorWord problem).length + 1)

private theorem predecessor_finalOutside_eq_firstCursor {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderSecondClauseSeparatorStep.finalOutside problem =
      firstCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        cursorOutsideTail problem := by
  unfold cursorOutsideTail firstCursorWord
  simp only [BuilderSecondClauseSeparatorStep.finalOutside,
    List.length_append, List.length_singleton]
  rw [show (BuilderSecondClauseSeparatorStep.cursorWord problem).length + 1 + 1 =
      (BuilderSecondClauseSeparatorStep.cursorWord problem).length + 2 by omega]
  simp [List.append_assoc]

private theorem firstCursorOutside_eq_secondCursor {language : Language}
    (problem : VerifierTableauProblem language) :
    firstCursorWord problem ++ BuilderUnaryPolynomial.unitSymbol ::
        BuilderUnaryPolynomial.scratchEndSymbol ::
          (cursorOutsideTail problem).drop 1 =
      secondCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 1 := by
  simp [secondCursorWord, List.append_assoc]

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  secondCursorWord problem ++ BuilderUnaryPolynomial.unitSymbol ::
    BuilderUnaryPolynomial.scratchEndSymbol ::
      (cursorOutsideTail problem).drop 2

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (secondClauseFirstLiteralTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def firstAppenderWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderTokenAppender.workSteps problem.input
    (BuilderSecondClauseSeparatorStep.secondClauseStartTokens problem)

def firstCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
    (firstCursorWord problem)

def firstFalseTokenCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  firstAppenderWorkSteps problem + 1 + firstCursorWorkSteps problem

def secondAppenderWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderTokenAppender.workSteps problem.input (firstTokenOutput problem)

def secondCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
    (secondCursorWord problem)

def secondFalseTokenCursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  secondAppenderWorkSteps problem + 1 + secondCursorWorkSteps problem

def suffixWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  firstFalseTokenCursorWorkSteps problem + 1 +
    secondFalseTokenCursorWorkSteps problem

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
    suffixWorkSteps problem

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (secondClauseFirstLiteralTokens problem)

private theorem falseAppender_workRunExact
    (input : BitString) (outside : List WorkSymbol)
    (output : List CNFToken) :
    workRunExact? FalseTokenCursor.appender
        (BuilderTokenAppender.workSteps input output)
        (workStartConfiguration FalseTokenCursor.appender
          (BuilderTokenAppender.workspaceTape input outside output)) =
      some
        { state := FalseTokenCursor.appender.acceptState
          tape := BuilderTokenAppender.workspaceTape input outside
            (output ++ [.f]) } := by
  have hRunEq : ∀ steps config,
      workRunExact? FalseTokenCursor.appender steps config =
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
           | some next => workRunExact? FalseTokenCursor.appender steps next) =
          (match workStep? BuilderTokenAppender.machine config with
           | none => none
           | some next => workRunExact? BuilderTokenAppender.machine steps next)
        cases workStep? BuilderTokenAppender.machine config with
        | none => rfl
        | some next => exact ih next
  have hExact := BuilderTokenAppender.appendToken_workRunExact
    input outside output .f
  rw [hRunEq]
  simpa [FalseTokenCursor.appender, BuilderTokenAppender.entryConfiguration,
    BuilderTokenAppender.finalConfiguration, workStartConfiguration] using hExact

def firstAppenderFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := FalseTokenCursor.appender.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (BuilderSecondClauseSeparatorStep.finalOutside problem)
      (firstTokenOutput problem) }

theorem firstAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? FalseTokenCursor.appender (firstAppenderWorkSteps problem)
        (workStartConfiguration FalseTokenCursor.appender
          (BuilderSecondClauseSeparatorStep.finalTape problem)) =
      some (firstAppenderFinalConfiguration problem) := by
  simpa [firstAppenderWorkSteps,
    BuilderSecondClauseSeparatorStep.finalTape,
    firstAppenderFinalConfiguration, firstTokenOutput] using
      falseAppender_workRunExact problem.input
        (BuilderSecondClauseSeparatorStep.finalOutside problem)
        (BuilderSecondClauseSeparatorStep.secondClauseStartTokens problem)

def firstCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (secondCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 1)
      (firstTokenOutput problem) }

private theorem firstCursorWord_symbol {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ symbol ∈ firstCursorWord problem,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
        symbol = BuilderUnaryPolynomial.separatorSymbol := by
  intro symbol hMem
  simp only [firstCursorWord, List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hBase | hUnit
  · exact BuilderUnaryPolynomial.scratchWord_symbol
      (BuilderFirstClausePaddingRun.secondClauseStartPolynomial
        problem.verifier) problem.input.length symbol (by
          simpa [BuilderSecondClauseSeparatorStep.cursorWord] using hBase)
  · exact Or.inl hUnit

private theorem secondCursorWord_symbol {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ symbol ∈ secondCursorWord problem,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
        symbol = BuilderUnaryPolynomial.separatorSymbol := by
  intro symbol hMem
  simp only [secondCursorWord, List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hFirst | hUnit
  · exact firstCursorWord_symbol problem symbol hFirst
  · exact Or.inl hUnit

set_option maxHeartbeats 3000000 in
theorem firstCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderDynamicTokenCursorStep.CursorAdvance.machine
        (firstCursorWorkSteps problem)
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (BuilderTokenAppender.workspaceTape problem.input
            (BuilderSecondClauseSeparatorStep.finalOutside problem)
            (firstTokenOutput problem))) =
      some (firstCursorFinalConfiguration problem) := by
  have hExact :=
    BuilderDynamicTokenCursorStep.CursorAdvance.advance_workRunExact
      problem.input (firstCursorWord problem) (cursorOutsideTail problem)
      (firstTokenOutput problem) (firstCursorWord_symbol problem)
  rw [predecessor_finalOutside_eq_firstCursor]
  rw [firstCursorOutside_eq_secondCursor] at hExact
  simpa only [firstCursorWorkSteps, firstCursorFinalConfiguration] using hExact

theorem firstFalseTokenCursor_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (firstAppenderFinalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (firstAppenderFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (firstAppenderFinalConfiguration problem).tape
  simpa [FalseTokenCursor.machine, firstAppenderFinalConfiguration,
    workStartConfiguration] using hLaunch

def firstFalseTokenCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := FalseTokenCursor.machine.acceptState
    tape := (firstCursorFinalConfiguration problem).tape }

theorem firstFalseTokenCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? FalseTokenCursor.machine
        (firstFalseTokenCursorWorkSteps problem)
        (workStartConfiguration FalseTokenCursor.machine
          (BuilderSecondClauseSeparatorStep.finalTape problem)) =
      some (firstFalseTokenCursorFinalConfiguration problem) := by
  let appenderInitial := workStartConfiguration FalseTokenCursor.appender
    (BuilderSecondClauseSeparatorStep.finalTape problem)
  let appenderFinal := firstAppenderFinalConfiguration problem
  let cursorFinal := firstCursorFinalConfiguration problem
  have hAppender : workRunExact? FalseTokenCursor.appender
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
    FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (firstAppenderWorkSteps problem) (firstCursorWorkSteps problem)
    appenderInitial appenderFinal cursorFinal hAppender rfl hCursor
  simpa [FalseTokenCursor.machine, firstFalseTokenCursorWorkSteps,
    appenderInitial, cursorFinal, firstCursorFinalConfiguration,
    firstFalseTokenCursorFinalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

def secondAppenderFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := FalseTokenCursor.appender.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (secondCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        (cursorOutsideTail problem).drop 1)
      (secondClauseFirstLiteralTokens problem) }

theorem secondAppender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? FalseTokenCursor.appender (secondAppenderWorkSteps problem)
        (workStartConfiguration FalseTokenCursor.appender
          (firstCursorFinalConfiguration problem).tape) =
      some (secondAppenderFinalConfiguration problem) := by
  simpa [secondAppenderWorkSteps, firstCursorFinalConfiguration,
    secondAppenderFinalConfiguration, secondClauseFirstLiteralTokens] using
      falseAppender_workRunExact problem.input
        (secondCursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
          (cursorOutsideTail problem).drop 1)
        (firstTokenOutput problem)

def secondCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.acceptState
    tape := finalTape problem }

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
      (secondClauseFirstLiteralTokens problem)
      (secondCursorWord_symbol problem)
  simpa [secondCursorWorkSteps, secondAppenderFinalConfiguration,
    secondCursorFinalConfiguration, finalTape, finalOutside,
    List.drop_drop, Nat.add_comm] using hExact

theorem secondFalseTokenCursor_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? FalseTokenCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (secondAppenderFinalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (secondAppenderFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (secondAppenderFinalConfiguration problem).tape
  simpa [FalseTokenCursor.machine, secondAppenderFinalConfiguration,
    workStartConfiguration] using hLaunch

def secondFalseTokenCursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := FalseTokenCursor.machine.acceptState
    tape := finalTape problem }

theorem secondFalseTokenCursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? FalseTokenCursor.machine
        (secondFalseTokenCursorWorkSteps problem)
        (workStartConfiguration FalseTokenCursor.machine
          (firstCursorFinalConfiguration problem).tape) =
      some (secondFalseTokenCursorFinalConfiguration problem) := by
  let appenderInitial := workStartConfiguration FalseTokenCursor.appender
    (firstCursorFinalConfiguration problem).tape
  let appenderFinal := secondAppenderFinalConfiguration problem
  let cursorFinal := secondCursorFinalConfiguration problem
  have hAppender : workRunExact? FalseTokenCursor.appender
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
    FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (secondAppenderWorkSteps problem) (secondCursorWorkSteps problem)
    appenderInitial appenderFinal cursorFinal hAppender rfl hCursor
  simpa [FalseTokenCursor.machine, secondFalseTokenCursorWorkSteps,
    appenderInitial, cursorFinal, secondCursorFinalConfiguration,
    secondFalseTokenCursorFinalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

theorem firstLiteralSuffix_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? FirstLiteralSuffix.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (firstFalseTokenCursorFinalConfiguration problem)) =
      some (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration FalseTokenCursor.machine
          (firstFalseTokenCursorFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    FalseTokenCursor.machine FalseTokenCursor.machine
    (firstFalseTokenCursorFinalConfiguration problem).tape
  simpa [FirstLiteralSuffix.machine,
    firstFalseTokenCursorFinalConfiguration, workStartConfiguration] using
      hLaunch

theorem suffix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? FirstLiteralSuffix.machine (suffixWorkSteps problem)
        (workStartConfiguration FirstLiteralSuffix.machine
          (BuilderSecondClauseSeparatorStep.finalTape problem)) =
      some
        { state := FirstLiteralSuffix.machine.acceptState
          tape := finalTape problem } := by
  let firstInitial := workStartConfiguration FalseTokenCursor.machine
    (BuilderSecondClauseSeparatorStep.finalTape problem)
  let firstFinal := firstFalseTokenCursorFinalConfiguration problem
  let secondFinal := secondFalseTokenCursorFinalConfiguration problem
  have hFirst : workRunExact? FalseTokenCursor.machine
      (firstFalseTokenCursorWorkSteps problem) firstInitial = some firstFinal := by
    simpa [firstInitial, firstFinal] using
      firstFalseTokenCursor_workRunExact problem
  have hSecond : workRunExact? FalseTokenCursor.machine
      (secondFalseTokenCursorWorkSteps problem)
      { state := FalseTokenCursor.machine.startState
        tape := firstFinal.tape } = some secondFinal := by
    simpa [firstFinal, firstFalseTokenCursorFinalConfiguration, secondFinal,
      workStartConfiguration] using secondFalseTokenCursor_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    FalseTokenCursor.machine FalseTokenCursor.machine
    (firstFalseTokenCursorWorkSteps problem)
    (secondFalseTokenCursorWorkSteps problem)
    firstInitial firstFinal secondFinal hFirst rfl hSecond
  simpa [FirstLiteralSuffix.machine, suffixWorkSteps, firstInitial,
    secondFinal, secondFalseTokenCursorFinalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderSecondClauseSeparatorStep.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (BuilderSecondClauseSeparatorStep.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderSecondClauseSeparatorStep.machine problem) (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderSecondClauseSeparatorStep.machine problem)
      FirstLiteralSuffix.machine)
    (BuilderSecondClauseSeparatorStep.workSteps problem)
    (workStartConfiguration (BuilderSecondClauseSeparatorStep.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderSecondClauseSeparatorStep.finalConfiguration problem)
    (BuilderSecondClauseSeparatorStep.workRunExact problem)
  simpa [machine, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hTransport

theorem prefixFirstLiteral_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderSecondClauseSeparatorStep.finalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration FirstLiteralSuffix.machine
          (BuilderSecondClauseSeparatorStep.finalTape problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine
    (BuilderSecondClauseSeparatorStep.finalTape problem)
  simpa [machine, BuilderSecondClauseSeparatorStep.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
/-- Every raw input follows the complete separator prefix, appends the two
false tokens of negative variable zero, and advances the retained coordinate
twice. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let prefixInitial := workStartConfiguration
    (BuilderSecondClauseSeparatorStep.machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal := BuilderSecondClauseSeparatorStep.finalConfiguration problem
  let suffixFinal : WorkConfiguration :=
    { state := FirstLiteralSuffix.machine.acceptState
      tape := finalTape problem }
  have hPrefix : workRunExact?
      (BuilderSecondClauseSeparatorStep.machine problem)
      (BuilderSecondClauseSeparatorStep.workSteps problem)
      prefixInitial = some prefixFinal := by
    simpa [prefixInitial, prefixFinal] using
      BuilderSecondClauseSeparatorStep.workRunExact problem
  have hSuffix : workRunExact? FirstLiteralSuffix.machine
      (suffixWorkSteps problem)
      { state := FirstLiteralSuffix.machine.startState
        tape := prefixFinal.tape } = some suffixFinal := by
    simpa [prefixFinal, suffixFinal,
      BuilderSecondClauseSeparatorStep.finalConfiguration,
      workStartConfiguration] using suffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine
    (BuilderSecondClauseSeparatorStep.workSteps problem)
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

private theorem formulaClauseSchedule_starts_shape_pair
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ left right : Fin problem.FormulaWidth, ∃ rest,
      problem.formulaClauseSchedule =
        some (atLeastOneBoundedClause
          (problem.symbolVariables time position)) ::
        some (excludeBoundedPairClause left right) :: rest ∧
      left.val = 0 ∧ right.val = 1 := by
  dsimp
  rcases formulaConstraintSchedule_starts_firstSymbol problem with
    ⟨constraints, hConstraints⟩
  rw [VerifierTableauProblem.formulaClauseSchedule, hConstraints]
  simp only [List.flatMap_cons]
  unfold VerifierTableauProblem.symbolShapeAt
  dsimp [VerifierTableauProblem.scheduledConstraintClauses,
    LocalConstraint.emit, exactlyOneBoundedClauses, FormulaSchedule.pad,
    atMostOneBoundedClauses, excludeBoundedWithClauses]
  refine ⟨_, _, _, rfl, ?_, ?_⟩
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

private theorem formulaClauseTokens_firstRectangle_then_secondFirstLiteral
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest,
      problem.formulaClauseSchedule.flatMap problem.scheduledClauseTokens =
        [some CNFToken.sep,
         some CNFToken.t, some CNFToken.f,
         some CNFToken.t, some CNFToken.t, some CNFToken.f,
         some CNFToken.t, some CNFToken.t, some CNFToken.t,
         some CNFToken.f, some CNFToken.finish] ++
        List.replicate (problem.formulaTokensPerClause - 11) none ++
        some CNFToken.sep :: some CNFToken.f :: some CNFToken.f ::
          some CNFToken.f :: rest := by
  rcases formulaClauseSchedule_starts_shape_pair problem with
    ⟨left, right, clauses, hClauses, hLeft, hRight⟩
  rw [hClauses]
  simp only [List.flatMap_cons]
  dsimp [VerifierTableauProblem.scheduledClauseTokens]
  rw [firstShapeClause_emit_eq]
  simp only [encodeClauseTokens, encodeLiteralListTokens,
    encodeLiteralTokens, encodeUnaryTokens]
  unfold FormulaSchedule.pad
  let pairTail : List (Option CNFToken) :=
    (encodeUnaryTokens right.val ++ [CNFToken.finish]).map some ++
      List.replicate (problem.formulaTokensPerClause -
        (CNFToken.sep ::
          (encodeLiteralListTokens
            (excludeBoundedPairClause left right).emit ++
              [CNFToken.finish])).length) none ++
      clauses.flatMap problem.scheduledClauseTokens
  refine ⟨pairTail, ?_⟩
  simp [pairTail, BoundedClause.emit, excludeBoundedPairClause, falseLiteral,
    BoundedLiteral.emit, encodeLiteralListTokens, encodeLiteralTokens,
    encodeUnaryTokens,
    hLeft, hRight, List.append_assoc]

/-- The finite output is exactly the canonical token prefix through the first
negative literal of the second clause. -/
theorem secondClauseFirstLiteralTokens_eq_canonical_formula_prefix
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest, encodeCNFTokens problem.formula =
      secondClauseFirstLiteralTokens problem ++ rest := by
  rcases formulaClauseTokens_firstRectangle_then_secondFirstLiteral problem with
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
         CNFToken.sep, CNFToken.f, CNFToken.f, CNFToken.f] ++
          FormulaSchedule.emit clauseTail := by
    rw [hClauseTail]
    simp
  refine ⟨CNFToken.f :: FormulaSchedule.emit clauseTail ++
      [CNFToken.finish], ?_⟩
  rw [← problem.formulaTokenSchedule_emit_eq_encodeCNFTokens]
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [FormulaSchedule.emit_append, FormulaSchedule.emit_append,
    FormulaSchedule.emit_pad, hEmit]
  unfold secondClauseFirstLiteralTokens firstTokenOutput
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
through negative variable zero in clause two. -/
theorem finalTokenBits_eq_encodedFormula_secondClauseFirstLiteral
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (secondClauseFirstLiteralTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 15)) := by
  rcases secondClauseFirstLiteralTokens_eq_canonical_formula_prefix problem with
    ⟨rest, hTokens⟩
  have hLength :
      (encodeTokenPairs (secondClauseFirstLiteralTokens problem)).length =
        2 * (problem.FormulaWidth + 15) := by
    rw [encodeTokenPairs_length]
    simp [secondClauseFirstLiteralTokens, firstTokenOutput,
      BuilderSecondClauseSeparatorStep.secondClauseStartTokens,
      BuilderFirstClausePrefix.firstClauseTokens_eq_canonical_prefix,
      encodeUnaryTokens_length]
  let suffix := encodeTokenPairs rest ++ [false]
  have hShape : problem.encodedFormula =
      encodeTokenPairs (secondClauseFirstLiteralTokens problem) ++ suffix := by
    simp only [VerifierTableauProblem.encodedFormula, encodeCNF]
    rw [hTokens, encodeTokenPairs_append_local]
    simp [suffix, List.append_assoc]
  rw [hShape, ← hLength]
  exact List.take_left.symm

def finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFirstClausePaddingRun.secondClauseStart problem + 3

theorem finalTokenSlot_eq_secondClauseStart_add_three
    {language : Language} (problem : VerifierTableauProblem language) :
    finalTokenSlot problem = problem.formulaVariableSlotBound + 1 +
        problem.formulaTokensPerClause + 3 := by
  rw [finalTokenSlot,
    BuilderFirstClausePaddingRun.secondClauseStart_eq]

theorem finalOutside_contains_finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.scratchWord_eq_root
      (BuilderFirstClausePaddingRun.secondClauseStartPolynomial
        problem.verifier) problem.input.length with
    ⟨wordPrefix, hPrefix⟩
  refine ⟨wordPrefix, (cursorOutsideTail problem).drop 2, ?_⟩
  unfold finalOutside secondCursorWord firstCursorWord finalTokenSlot
    BuilderSecondClauseSeparatorStep.cursorWord
  rw [hPrefix]
  rw [show BuilderFirstClausePaddingRun.secondClauseStart problem + 3 =
      ((BuilderFirstClausePaddingRun.secondClauseStart problem + 1) + 1) + 1
      by omega]
  rw [List.replicate_succ', List.replicate_succ', List.replicate_succ']
  simp [BuilderFirstClausePaddingRun.secondClauseStart,
    List.append_assoc]

/-- The predecessor coordinate is the negative sign beginning variable zero. -/
theorem firstLiteralSignSlot_direct_eq_f {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (BuilderFirstClausePaddingRun.secondClauseStart problem + 1) =
      some (some CNFToken.f) := by
  simpa [BuilderSecondClauseSeparatorStep.finalTokenSlot] using
    BuilderSecondClauseSeparatorStep.nextTokenSlot_direct_eq_f problem

/-- The token after the negative sign is the unary-zero terminator. -/
theorem firstLiteralZeroTerminatorSlot_direct_eq_f {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (BuilderFirstClausePaddingRun.secondClauseStart problem + 2) =
      some (some CNFToken.f) := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_firstRectangle_then_secondFirstLiteral problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses, BuilderFirstClausePaddingRun.secondClauseStart_eq]
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
      problem.formulaTokensPerClause + 2 -
      (problem.formulaVariableSlotBound + 1) =
        problem.formulaTokensPerClause + 2 by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause + 2 - 11 =
      (problem.formulaTokensPerClause - 11) + 2 by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  simp

/-- After variable zero is complete, the retained coordinate is the negative
sign beginning variable one. -/
theorem nextTokenSlot_direct_eq_f {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect (finalTokenSlot problem) =
      some (some CNFToken.f) := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_firstRectangle_then_secondFirstLiteral problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses, finalTokenSlot,
    BuilderFirstClausePaddingRun.secondClauseStart_eq]
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
      problem.formulaTokensPerClause + 3 -
      (problem.formulaVariableSlotBound + 1) =
        problem.formulaTokensPerClause + 3 by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause + 3 - 11 =
      (problem.formulaTokensPerClause - 11) + 3 by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  simp

theorem specification_next_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨finalTokenSlot problem⟩ =
      some (some CNFToken.f, ⟨finalTokenSlot problem + 1⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [nextTokenSlot_direct_eq_f]

theorem specification_firstLiteral_sign_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderFirstClausePaddingRun.secondClauseStart problem + 1⟩ =
      some (some CNFToken.f,
        ⟨BuilderFirstClausePaddingRun.secondClauseStart problem + 2⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [firstLiteralSignSlot_direct_eq_f]

theorem specification_firstLiteral_terminator_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderFirstClausePaddingRun.secondClauseStart problem + 2⟩ =
      some (some CNFToken.f,
        ⟨BuilderFirstClausePaddingRun.secondClauseStart problem + 3⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [firstLiteralZeroTerminatorSlot_direct_eq_f]

theorem finalConfiguration_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (finalConfiguration problem).state = (machine problem).acceptState := rfl

private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
  rfl

/-! ### External compiled-time polynomial -/

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

/-- External raw-transition bound for four launches, two selected false-token
appends, and two complete bidirectional cursor scans. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderSecondClauseSeparatorStep.rawTimeBound verifier)
    (.add (.constant 564)
      (.add (scalePolynomial 48 .variable)
        (.add (scalePolynomial 24 (formulaWidthPolynomial verifier))
          (scalePolynomial 24
            (BuilderUnaryPolynomial.registerSpanPolynomial
              (BuilderFirstClausePaddingRun.secondClauseStartPolynomial
                verifier))))))

private theorem predecessorTokens_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderSecondClauseSeparatorStep.secondClauseStartTokens problem).length =
      problem.FormulaWidth + 13 := by
  rw [BuilderSecondClauseSeparatorStep.secondClauseStartTokens,
    List.length_append]
  rw [BuilderFirstClausePrefix.firstClauseTokens_eq_canonical_prefix,
    List.length_append, encodeUnaryTokens_length]
  simp

private theorem firstTokenOutput_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (firstTokenOutput problem).length = problem.FormulaWidth + 14 := by
  rw [firstTokenOutput, List.length_append, predecessorTokens_length]
  simp

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderSecondClauseSeparatorStep.rawTimeBound problem.verifier).eval
          problem.input.length + 564 +
        48 * problem.input.length + 24 * problem.FormulaWidth +
        24 * (BuilderSecondClauseSeparatorStep.cursorWord problem).length := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, NatPolynomial.eval_variable, scalePolynomial]
  have hWidth :
      (formulaWidthPolynomial problem.verifier).eval problem.input.length =
        problem.FormulaWidth := by
    simpa [BitString.size] using problem.formulaWidthPolynomial_eval
  rw [hWidth]
  rw [← BuilderUnaryPolynomial.scratchWord_length
    (BuilderFirstClausePaddingRun.secondClauseStartPolynomial
      problem.verifier) problem.input.length]
  simp only [BuilderSecondClauseSeparatorStep.cursorWord]
  omega

private theorem firstAppenderWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    firstAppenderWorkSteps problem ≤
      4 * problem.input.length + 2 * problem.FormulaWidth + 34 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  unfold firstAppenderWorkSteps BuilderTokenAppender.workSteps
    BuilderTokenAppender.halfSteps
  rw [predecessorTokens_length]
  omega

private theorem secondAppenderWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    secondAppenderWorkSteps problem ≤
      4 * problem.input.length + 2 * problem.FormulaWidth + 36 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  unfold secondAppenderWorkSteps BuilderTokenAppender.workSteps
    BuilderTokenAppender.halfSteps
  rw [firstTokenOutput_length]
  omega

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := BuilderSecondClauseSeparatorStep.rawTimeBound_le problem
  have hFirstAppender := firstAppenderWorkSteps_le problem
  have hSecondAppender := secondAppenderWorkSteps_le problem
  have hFirstCursorLength :
      (firstCursorWord problem).length =
        (BuilderSecondClauseSeparatorStep.cursorWord problem).length + 1 := by
    simp [firstCursorWord]
  have hSecondCursorLength :
      (secondCursorWord problem).length =
        (BuilderSecondClauseSeparatorStep.cursorWord problem).length + 2 := by
    simp [secondCursorWord, hFirstCursorLength]
  rw [rawTimeBound_eval]
  unfold workSteps suffixWorkSteps firstFalseTokenCursorWorkSteps
    secondFalseTokenCursorWorkSteps firstCursorWorkSteps secondCursorWorkSteps
    BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
  rw [hFirstCursorLength, hSecondCursorLength]
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

private theorem globalSuffix_stuck_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (config : WorkConfiguration)
    (hLocalHalted : FirstLiteralSuffix.machine.isHalted config = false)
    (hLocalStep : workStep? FirstLiteralSuffix.machine config = none) :
    (let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState config
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let global := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState config
  have hGlobalStep : workStep? (machine problem) global = none := by
    have hStep := second_workStep_none_of_local
      (BuilderSecondClauseSeparatorStep.machine problem)
      FirstLiteralSuffix.machine config hLocalHalted hLocalStep
    simpa [machine, global] using hStep
  have hGlobalHalted : (machine problem).isHalted global = false := by
    have hHalted :=
      BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
        (BuilderSecondClauseSeparatorStep.machine problem)
        FirstLiteralSuffix.machine config hLocalHalted
    simpa [machine, global] using hHalted
  exact stuck_timeout problem fuel global hGlobalHalted hGlobalStep

private theorem firstFalseTokenCursor_stuck_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (config : WorkConfiguration)
    (hLocalHalted : FalseTokenCursor.machine.isHalted config = false)
    (hLocalStep : workStep? FalseTokenCursor.machine config = none) :
    (let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState config
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let suffix := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.firstState config
  have hAccept := state_ne_accept_of_not_halted
    FalseTokenCursor.machine config hLocalHalted
  have hSuffixStep : workStep? FirstLiteralSuffix.machine suffix = none := by
    have hStep := first_workStep_none_of_local FalseTokenCursor.machine
      FalseTokenCursor.machine config hAccept hLocalHalted hLocalStep
    simpa [FirstLiteralSuffix.machine, suffix] using hStep
  have hSuffixHalted : FirstLiteralSuffix.machine.isHalted suffix = false := by
    have hHalted :=
      BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
        FalseTokenCursor.machine FalseTokenCursor.machine config
    simpa [FirstLiteralSuffix.machine, suffix] using hHalted
  exact globalSuffix_stuck_timeout problem fuel suffix hSuffixHalted hSuffixStep

private theorem secondFalseTokenCursor_stuck_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (config : WorkConfiguration)
    (hLocalHalted : FalseTokenCursor.machine.isHalted config = false)
    (hLocalStep : workStep? FalseTokenCursor.machine config = none) :
    (let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState config
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let suffix := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState config
  have hSuffixStep : workStep? FirstLiteralSuffix.machine suffix = none := by
    have hStep := second_workStep_none_of_local FalseTokenCursor.machine
      FalseTokenCursor.machine config hLocalHalted hLocalStep
    simpa [FirstLiteralSuffix.machine, suffix] using hStep
  have hSuffixHalted : FirstLiteralSuffix.machine.isHalted suffix = false := by
    have hHalted :=
      BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
        FalseTokenCursor.machine FalseTokenCursor.machine config hLocalHalted
    simpa [FirstLiteralSuffix.machine, suffix] using hHalted
  exact globalSuffix_stuck_timeout problem fuel suffix hSuffixHalted hSuffixStep

private theorem selectedAppender_stuck_timeout_first {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (bad : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted bad = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine bad = none) :
    (let component := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState bad
     let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState component
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let component := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.firstState bad
  have hSelectedHalted : FalseTokenCursor.appender.isHalted bad = false := by
    change BuilderTokenAppender.machine.isHalted bad = false
    exact hLocalHalted
  have hSelectedStep : workStep? FalseTokenCursor.appender bad = none := by
    change workStep? BuilderTokenAppender.machine bad = none
    exact hLocalStep
  have hAccept := state_ne_accept_of_not_halted
    FalseTokenCursor.appender bad hSelectedHalted
  have hComponentStep : workStep? FalseTokenCursor.machine component = none := by
    have hStep := first_workStep_none_of_local FalseTokenCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine bad hAccept
      hSelectedHalted hSelectedStep
    simpa [FalseTokenCursor.machine, component] using hStep
  have hComponentHalted : FalseTokenCursor.machine.isHalted component = false := by
    have hHalted :=
      BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
        FalseTokenCursor.appender
        BuilderDynamicTokenCursorStep.CursorAdvance.machine bad
    simpa [FalseTokenCursor.machine, component] using hHalted
  exact firstFalseTokenCursor_stuck_timeout problem fuel component
    hComponentHalted hComponentStep

private theorem selectedAppender_stuck_timeout_second {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (bad : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted bad = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine bad = none) :
    (let component := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState bad
     let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState component
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let component := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.firstState bad
  have hSelectedHalted : FalseTokenCursor.appender.isHalted bad = false := by
    change BuilderTokenAppender.machine.isHalted bad = false
    exact hLocalHalted
  have hSelectedStep : workStep? FalseTokenCursor.appender bad = none := by
    change workStep? BuilderTokenAppender.machine bad = none
    exact hLocalStep
  have hAccept := state_ne_accept_of_not_halted
    FalseTokenCursor.appender bad hSelectedHalted
  have hComponentStep : workStep? FalseTokenCursor.machine component = none := by
    have hStep := first_workStep_none_of_local FalseTokenCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine bad hAccept
      hSelectedHalted hSelectedStep
    simpa [FalseTokenCursor.machine, component] using hStep
  have hComponentHalted : FalseTokenCursor.machine.isHalted component = false := by
    have hHalted :=
      BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
        FalseTokenCursor.appender
        BuilderDynamicTokenCursorStep.CursorAdvance.machine bad
    simpa [FalseTokenCursor.machine, component] using hHalted
  exact secondFalseTokenCursor_stuck_timeout problem fuel component
    hComponentHalted hComponentStep

theorem malformedFirstAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedTallyConfiguration
        request left right
     let component := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState bad
     let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState component
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedTallyConfiguration
    request left right
  exact selectedAppender_stuck_timeout_first problem fuel bad
    (BuilderTokenAppender.malformedTallySymbol_isHalted_false
      request left right)
    (BuilderTokenAppender.malformedTallySymbol_workStep_none
      request left right)

theorem malformedSecondAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedTallyConfiguration
        request left right
     let component := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState bad
     let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState component
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedTallyConfiguration
    request left right
  exact selectedAppender_stuck_timeout_second problem fuel bad
    (BuilderTokenAppender.malformedTallySymbol_isHalted_false
      request left right)
    (BuilderTokenAppender.malformedTallySymbol_workStep_none
      request left right)

theorem malformedFirstAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedOutputConfiguration
        request left right
     let component := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState bad
     let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState component
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedOutputConfiguration
    request left right
  exact selectedAppender_stuck_timeout_first problem fuel bad
    (BuilderTokenAppender.malformedOutputSymbol_isHalted_false
      request left right)
    (BuilderTokenAppender.malformedOutputSymbol_workStep_none
      request left right)

theorem malformedSecondAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let bad := BuilderTokenAppender.malformedOutputConfiguration
        request left right
     let component := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState bad
     let suffix := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState component
     let global := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState suffix
     let result := workRun (machine problem) fuel global
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedOutputConfiguration
    request left right
  exact selectedAppender_stuck_timeout_second problem fuel bad
    (BuilderTokenAppender.malformedOutputSymbol_isHalted_false
      request left right)
    (BuilderTokenAppender.malformedOutputSymbol_workStep_none
      request left right)

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

def firstCursorGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        config))

def secondCursorGlobalConfiguration {language : Language}
    (_problem : VerifierTableauProblem language)
    (config : WorkConfiguration) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        config))

private theorem firstCursorGlobal_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderDynamicTokenCursorStep.CursorAdvance.machine
      config = some next) :
    workStep? (machine problem) (firstCursorGlobalConfiguration problem config) =
      some (firstCursorGlobalConfiguration problem next) := by
  have hComponent := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine config next hStep
  have hSuffix := BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
    FalseTokenCursor.machine FalseTokenCursor.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState config)
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState next)
    (by simpa [FalseTokenCursor.machine] using hComponent)
  have hGlobal := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        config))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        next))
    (by simpa [FirstLiteralSuffix.machine] using hSuffix)
  simpa [machine, firstCursorGlobalConfiguration] using hGlobal

private theorem secondCursorGlobal_workStep_of_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? BuilderDynamicTokenCursorStep.CursorAdvance.machine
      config = some next) :
    workStep? (machine problem) (secondCursorGlobalConfiguration problem config) =
      some (secondCursorGlobalConfiguration problem next) := by
  have hComponent := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    FalseTokenCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine config next hStep
  have hSuffix := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    FalseTokenCursor.machine FalseTokenCursor.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState config)
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState next)
    (by simpa [FalseTokenCursor.machine] using hComponent)
  have hGlobal := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        config))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        next))
    (by simpa [FirstLiteralSuffix.machine] using hSuffix)
  simpa [machine, secondCursorGlobalConfiguration] using hGlobal

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

theorem malformedFirstCursorScratch_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (left right : List WorkSymbol) :
    (let bad := firstCursorGlobalConfiguration problem
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
  let bad := firstCursorGlobalConfiguration problem localBad
  let dead := firstCursorGlobalConfiguration problem localDead
  have hBadStep : workStep? (machine problem) bad = some dead := by
    simpa [bad, dead, localBad, localDead] using
      firstCursorGlobal_workStep_of_some problem localBad localDead
        (cursorMalformed_workStep left right)
  have hDeadStep : workStep? (machine problem) dead = some dead := by
    simpa [dead, localDead] using
      firstCursorGlobal_workStep_of_some problem localDead localDead
        (cursorDead_workStep localBad.tape)
  cases fuel with
  | zero =>
      exact verdict_timeout_of_not_halted problem bad
        (isHalted_false_of_workStep_some (machine problem) bad dead hBadStep)
  | succ fuel =>
      have hRun := workRun_succ_eq_of_step_and_loop
        (machine problem) fuel bad dead hBadStep hDeadStep
      change
        (let result := workRun (machine problem) (fuel + 1) bad
         if result.state == (machine problem).acceptState then WorkVerdict.accept
         else if result.state == (machine problem).rejectState then
           WorkVerdict.reject
         else WorkVerdict.timeout) = WorkVerdict.timeout
      rw [hRun]
      exact verdict_timeout_of_not_halted problem dead
        (isHalted_false_of_workStep_some (machine problem) dead dead hDeadStep)

theorem malformedSecondCursorScratch_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (left right : List WorkSymbol) :
    (let bad := secondCursorGlobalConfiguration problem
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
  let bad := secondCursorGlobalConfiguration problem localBad
  let dead := secondCursorGlobalConfiguration problem localDead
  have hBadStep : workStep? (machine problem) bad = some dead := by
    simpa [bad, dead, localBad, localDead] using
      secondCursorGlobal_workStep_of_some problem localBad localDead
        (cursorMalformed_workStep left right)
  have hDeadStep : workStep? (machine problem) dead = some dead := by
    simpa [dead, localDead] using
      secondCursorGlobal_workStep_of_some problem localDead localDead
        (cursorDead_workStep localBad.tape)
  cases fuel with
  | zero =>
      exact verdict_timeout_of_not_halted problem bad
        (isHalted_false_of_workStep_some (machine problem) bad dead hBadStep)
  | succ fuel =>
      have hRun := workRun_succ_eq_of_step_and_loop
        (machine problem) fuel bad dead hBadStep hDeadStep
      change
        (let result := workRun (machine problem) (fuel + 1) bad
         if result.state == (machine problem).acceptState then WorkVerdict.accept
         else if result.state == (machine problem).rejectState then
           WorkVerdict.reject
         else WorkVerdict.timeout) = WorkVerdict.timeout
      rw [hRun]
      exact verdict_timeout_of_not_halted problem dead
        (isHalted_false_of_workStep_some (machine problem) dead dead hDeadStep)

private theorem machine_isHalted_predecessor_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          config) = false := by
  have hHalted :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      (BuilderSecondClauseSeparatorStep.machine problem)
      FirstLiteralSuffix.machine config
  simpa [machine] using hHalted

/-- The predecessor endpoint is still globally nonhalting until the outer
bridge launches the first false-token component. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderSecondClauseSeparatorStep.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderSecondClauseSeparatorStep.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (BuilderSecondClauseSeparatorStep.finalConfiguration problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_predecessor_false problem
      (BuilderSecondClauseSeparatorStep.finalConfiguration problem))

private theorem workRunExact_one_of_workStep {language : Language}
    (problem : VerifierTableauProblem language)
    (start next : WorkConfiguration)
    (hStep : workStep? (machine problem) start = some next) :
    workRunExact? (machine problem) 1 start = some next := by
  change
    (match workStep? (machine problem) start with
     | none => none
     | some result => workRunExact? (machine problem) 0 result) = some next
  rw [hStep]
  rfl

private def firstAppenderGlobalEndpoint {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (firstAppenderFinalConfiguration problem)))

private theorem firstAppenderEndpoint_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
          firstAppenderWorkSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (firstAppenderGlobalEndpoint problem) := by
  let initial := workStartConfiguration (machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderSecondClauseSeparatorStep.finalConfiguration problem)
  let suffixInitial := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState
    (workStartConfiguration FirstLiteralSuffix.machine
      (BuilderSecondClauseSeparatorStep.finalTape problem))
  have hPrefix : workRunExact? (machine problem)
      (BuilderSecondClauseSeparatorStep.workSteps problem) initial =
        some prefixFinal := by
    simpa [initial, prefixFinal] using prefix_workRunExact problem
  have hLaunch : workRunExact? (machine problem) 1 prefixFinal =
      some suffixInitial := by
    apply workRunExact_one_of_workStep problem
    simpa [prefixFinal, suffixInitial] using
      prefixFirstLiteral_launch_workStep problem
  have hComponent := PipelineStageBridges.workRunExact?_transport
    FalseTokenCursor.appender FalseTokenCursor.machine
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      FalseTokenCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine)
    (firstAppenderWorkSteps problem)
    (workStartConfiguration FalseTokenCursor.appender
      (BuilderSecondClauseSeparatorStep.finalTape problem))
    (firstAppenderFinalConfiguration problem)
    (firstAppender_workRunExact problem)
  have hSuffix := PipelineStageBridges.workRunExact?_transport
    FalseTokenCursor.machine FirstLiteralSuffix.machine
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      FalseTokenCursor.machine FalseTokenCursor.machine)
    (firstAppenderWorkSteps problem)
    (workStartConfiguration FalseTokenCursor.machine
      (BuilderSecondClauseSeparatorStep.finalTape problem))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (firstAppenderFinalConfiguration problem)) (by
        simpa [FalseTokenCursor.machine,
          BuilderFirstClausePrefix.WorkChain.machine,
          workStartConfiguration, renameConfiguration] using hComponent)
  have hGlobal := PipelineStageBridges.workRunExact?_transport
    FirstLiteralSuffix.machine (machine problem)
    BuilderFirstClausePrefix.WorkChain.secondState
    (BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
      (BuilderSecondClauseSeparatorStep.machine problem)
      FirstLiteralSuffix.machine)
    (firstAppenderWorkSteps problem)
    (workStartConfiguration FirstLiteralSuffix.machine
      (BuilderSecondClauseSeparatorStep.finalTape problem))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (firstAppenderFinalConfiguration problem))) (by
        simpa [FirstLiteralSuffix.machine,
          BuilderFirstClausePrefix.WorkChain.machine,
          workStartConfiguration, renameConfiguration] using hSuffix)
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderSecondClauseSeparatorStep.workSteps problem) 1
    initial prefixFinal suffixInitial hPrefix hLaunch
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderSecondClauseSeparatorStep.workSteps problem + 1)
    (firstAppenderWorkSteps problem) initial suffixInitial
    (firstAppenderGlobalEndpoint problem) h01 (by
      simpa [suffixInitial, firstAppenderGlobalEndpoint] using hGlobal)
  simpa [initial, Nat.add_assoc] using h02

private theorem machine_isHalted_firstAppender_false {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (firstAppenderGlobalEndpoint problem) = false := by
  have hComponent :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      FalseTokenCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine
      (firstAppenderFinalConfiguration problem)
  have hSuffix :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      FalseTokenCursor.machine FalseTokenCursor.machine
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (firstAppenderFinalConfiguration problem))
  have hGlobal :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      (BuilderSecondClauseSeparatorStep.machine problem)
      FirstLiteralSuffix.machine
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (firstAppenderFinalConfiguration problem))) (by
        simpa [FirstLiteralSuffix.machine, FalseTokenCursor.machine] using
          hSuffix)
  simpa [machine, firstAppenderGlobalEndpoint] using hGlobal

/-- The first false-token appender endpoint remains globally nonhalting until
its cursor bridge fires. -/
theorem firstAppenderEndpoint_before_cursor_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
          firstAppenderWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
      firstAppenderWorkSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (firstAppenderGlobalEndpoint problem)
    (firstAppenderEndpoint_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_firstAppender_false problem)

private def firstCursorGlobalEndpoint {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (firstCursorFinalConfiguration problem)))

private theorem firstCursorEndpoint_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
          firstAppenderWorkSteps problem + 1 + firstCursorWorkSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (firstCursorGlobalEndpoint problem) := by
  let appenderEndpoint := firstAppenderGlobalEndpoint problem
  let cursorInitial := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (firstAppenderFinalConfiguration problem).tape)))
  have hAppender : workRunExact? (machine problem)
      (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
        firstAppenderWorkSteps problem)
      (workStartConfiguration (machine problem)
        (rawInputWorkTape problem.input)) = some appenderEndpoint := by
    simpa [appenderEndpoint] using firstAppenderEndpoint_workRunExact problem
  have hComponentStep := firstFalseTokenCursor_launch_workStep problem
  have hSuffixStep := BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
    FalseTokenCursor.machine FalseTokenCursor.machine _ _ hComponentStep
  have hGlobalStep := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine _ _ (by
      simpa [FirstLiteralSuffix.machine] using hSuffixStep)
  have hLaunch : workRunExact? (machine problem) 1 appenderEndpoint =
      some cursorInitial := by
    apply workRunExact_one_of_workStep problem
    simpa [machine, appenderEndpoint, firstAppenderGlobalEndpoint,
      cursorInitial] using hGlobalStep
  have hComponent := PipelineStageBridges.workRunExact?_transport
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    FalseTokenCursor.machine BuilderFirstClausePrefix.WorkChain.secondState
    (BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
      FalseTokenCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine)
    (firstCursorWorkSteps problem)
    (workStartConfiguration
      BuilderDynamicTokenCursorStep.CursorAdvance.machine
      (firstAppenderFinalConfiguration problem).tape)
    (firstCursorFinalConfiguration problem) (by
      simpa [firstAppenderFinalConfiguration, workStartConfiguration] using
        firstCursor_workRunExact problem)
  have hSuffix := PipelineStageBridges.workRunExact?_transport
    FalseTokenCursor.machine FirstLiteralSuffix.machine
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      FalseTokenCursor.machine FalseTokenCursor.machine)
    (firstCursorWorkSteps problem)
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (workStartConfiguration
        BuilderDynamicTokenCursorStep.CursorAdvance.machine
        (firstAppenderFinalConfiguration problem).tape))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (firstCursorFinalConfiguration problem)) (by
        simpa [FalseTokenCursor.machine,
          BuilderFirstClausePrefix.WorkChain.machine,
          workStartConfiguration, renameConfiguration] using hComponent)
  have hGlobal := PipelineStageBridges.workRunExact?_transport
    FirstLiteralSuffix.machine (machine problem)
    BuilderFirstClausePrefix.WorkChain.secondState
    (BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
      (BuilderSecondClauseSeparatorStep.machine problem)
      FirstLiteralSuffix.machine)
    (firstCursorWorkSteps problem)
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (firstAppenderFinalConfiguration problem).tape)))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (firstCursorFinalConfiguration problem))) (by
        simpa [FirstLiteralSuffix.machine,
          BuilderFirstClausePrefix.WorkChain.machine,
          workStartConfiguration, renameConfiguration] using hSuffix)
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
      firstAppenderWorkSteps problem) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input)) appenderEndpoint cursorInitial
    hAppender hLaunch
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
      firstAppenderWorkSteps problem + 1)
    (firstCursorWorkSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input)) cursorInitial
    (firstCursorGlobalEndpoint problem) h01 (by
      simpa [cursorInitial, firstCursorGlobalEndpoint] using hGlobal)
  simpa [Nat.add_assoc] using h02

private theorem machine_isHalted_firstCursor_false {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (firstCursorGlobalEndpoint problem) = false := by
  let component := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState
    (firstCursorFinalConfiguration problem)
  have hSuffix :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      FalseTokenCursor.machine FalseTokenCursor.machine component
  have hGlobal :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      (BuilderSecondClauseSeparatorStep.machine problem)
      FirstLiteralSuffix.machine
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        component) (by simpa [FirstLiteralSuffix.machine] using hSuffix)
  simpa [machine, firstCursorGlobalEndpoint, component] using hGlobal

/-- The completed first cursor advance remains a timeout until the bridge to
the second false-token component fires. -/
theorem firstCursorEndpoint_before_secondAppender_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
          firstAppenderWorkSteps problem + 1 + firstCursorWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
      firstAppenderWorkSteps problem + 1 + firstCursorWorkSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (firstCursorGlobalEndpoint problem)
    (firstCursorEndpoint_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_firstCursor_false problem)

private def secondAppenderGlobalEndpoint {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (secondAppenderFinalConfiguration problem)))

private theorem secondAppenderEndpoint_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
          firstFalseTokenCursorWorkSteps problem + 1 +
          secondAppenderWorkSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (secondAppenderGlobalEndpoint problem) := by
  let cursorEndpoint := firstCursorGlobalEndpoint problem
  let secondInitial := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (workStartConfiguration FalseTokenCursor.machine
        (firstCursorFinalConfiguration problem).tape))
  have hCursor : workRunExact? (machine problem)
      (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
        firstAppenderWorkSteps problem + 1 + firstCursorWorkSteps problem)
      (workStartConfiguration (machine problem)
        (rawInputWorkTape problem.input)) = some cursorEndpoint := by
    simpa [cursorEndpoint] using firstCursorEndpoint_workRunExact problem
  have hSuffixStep := firstLiteralSuffix_launch_workStep problem
  have hGlobalStep := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderSecondClauseSeparatorStep.machine problem)
    FirstLiteralSuffix.machine _ _ hSuffixStep
  have hFirstFinal : firstFalseTokenCursorFinalConfiguration problem =
      renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (firstCursorFinalConfiguration problem) := by
    unfold firstFalseTokenCursorFinalConfiguration FalseTokenCursor.machine
      BuilderFirstClausePrefix.WorkChain.machine
    rfl
  rw [hFirstFinal] at hGlobalStep
  have hLaunch : workRunExact? (machine problem) 1 cursorEndpoint =
      some secondInitial := by
    apply workRunExact_one_of_workStep problem
    simpa [machine, cursorEndpoint, firstCursorGlobalEndpoint,
      secondInitial, renameConfiguration] using hGlobalStep
  have hComponent := PipelineStageBridges.workRunExact?_transport
    FalseTokenCursor.appender FalseTokenCursor.machine
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      FalseTokenCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine)
    (secondAppenderWorkSteps problem)
    (workStartConfiguration FalseTokenCursor.appender
      (firstCursorFinalConfiguration problem).tape)
    (secondAppenderFinalConfiguration problem)
    (secondAppender_workRunExact problem)
  have hSuffix := PipelineStageBridges.workRunExact?_transport
    FalseTokenCursor.machine FirstLiteralSuffix.machine
    BuilderFirstClausePrefix.WorkChain.secondState
    (BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
      FalseTokenCursor.machine FalseTokenCursor.machine)
    (secondAppenderWorkSteps problem)
    (workStartConfiguration FalseTokenCursor.machine
      (firstCursorFinalConfiguration problem).tape)
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (secondAppenderFinalConfiguration problem)) (by
        simpa [FalseTokenCursor.machine,
          BuilderFirstClausePrefix.WorkChain.machine,
          workStartConfiguration, renameConfiguration] using hComponent)
  have hGlobal := PipelineStageBridges.workRunExact?_transport
    FirstLiteralSuffix.machine (machine problem)
    BuilderFirstClausePrefix.WorkChain.secondState
    (BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
      (BuilderSecondClauseSeparatorStep.machine problem)
      FirstLiteralSuffix.machine)
    (secondAppenderWorkSteps problem)
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (workStartConfiguration FalseTokenCursor.machine
        (firstCursorFinalConfiguration problem).tape))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (secondAppenderFinalConfiguration problem))) (by
        simpa [FirstLiteralSuffix.machine,
          BuilderFirstClausePrefix.WorkChain.machine,
          firstFalseTokenCursorFinalConfiguration,
          workStartConfiguration, renameConfiguration] using hSuffix)
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
      firstAppenderWorkSteps problem + 1 + firstCursorWorkSteps problem) 1
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input)) cursorEndpoint secondInitial
    hCursor hLaunch
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
      firstAppenderWorkSteps problem + 1 + firstCursorWorkSteps problem + 1)
    (secondAppenderWorkSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input)) secondInitial
    (secondAppenderGlobalEndpoint problem) h01 (by
      simpa [secondInitial, secondAppenderGlobalEndpoint] using hGlobal)
  simpa [firstFalseTokenCursorWorkSteps, Nat.add_assoc] using h02

private theorem machine_isHalted_secondAppender_false {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (secondAppenderGlobalEndpoint problem) = false := by
  have hComponent :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      FalseTokenCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine
      (secondAppenderFinalConfiguration problem)
  have hSuffix :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      FalseTokenCursor.machine FalseTokenCursor.machine
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (secondAppenderFinalConfiguration problem)) (by
        simpa [FalseTokenCursor.machine] using hComponent)
  have hGlobal :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      (BuilderSecondClauseSeparatorStep.machine problem)
      FirstLiteralSuffix.machine
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (secondAppenderFinalConfiguration problem))) (by
        simpa [FirstLiteralSuffix.machine] using hSuffix)
  simpa [machine, secondAppenderGlobalEndpoint] using hGlobal

/-- The second false-token appender endpoint remains globally nonhalting until
its final cursor bridge fires. -/
theorem secondAppenderEndpoint_before_cursor_launch_timeout
    {language : Language} (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
          firstFalseTokenCursorWorkSteps problem + 1 +
          secondAppenderWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderSecondClauseSeparatorStep.workSteps problem + 1 +
      firstFalseTokenCursorWorkSteps problem + 1 +
      secondAppenderWorkSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (secondAppenderGlobalEndpoint problem)
    (secondAppenderEndpoint_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_secondAppender_false problem)

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

end BuilderSecondClauseFirstLiteralPrefix

end CookLevin

end PNP.Concrete
