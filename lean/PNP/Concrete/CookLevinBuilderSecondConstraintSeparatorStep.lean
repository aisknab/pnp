/-
Copyright (c) 2026 PNP Labs.

One populated token-cursor transition at the beginning of the second
canonical Cook--Levin constraint.

The machine in this file composes the complete first-constraint padding run with
the already-audited selected separator appender and unary cursor advance.
Every raw input therefore emits the separator beginning constraint two and leaves
the retained coordinate on that constraint's first literal sign.  This is one
fixed populated transition, not a general schedule decoder, a complete cursor
loop, or a complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderFirstConstraintPaddingRun

namespace PNP.Concrete

namespace CookLevin

namespace BuilderSecondConstraintSeparatorStep

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ### Reused selected separator/cursor suffix -/

private theorem predecessor_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderFirstConstraintPaddingRun.machine problem) := by
  exact BuilderFirstConstraintPaddingRun.rule_source_ne_acceptState problem

private theorem suffix_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      BuilderSecondClauseSeparatorStep.SeparatorCursor.machine := by
  exact BuilderSecondClauseSeparatorStep.SeparatorCursor.rule_source_ne_acceptState

/-- One literal finite work machine from raw input through the populated
separator transition at the beginning of constraint two. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderFirstConstraintPaddingRun.machine problem)
    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      4554 +
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
          (BuilderFirstConstraintPaddingRun.paddingPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial
            problem.verifier) := by
  have hPrefix := BuilderFirstConstraintPaddingRun.rules_length problem
  have hSuffix :=
    BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_length
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
    (BuilderFirstConstraintPaddingRun.machine problem)
    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
    (BuilderFirstConstraintPaddingRun.rules_pairwise_query_distinct problem)
    BuilderSecondClauseSeparatorStep.SeparatorCursor.rules_pairwise_query_distinct
    (predecessor_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderFirstConstraintPaddingRun.machine problem)
    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine_acceptState_ne_rejectState

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderFirstConstraintPaddingRun.machine problem)
    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
    suffix_noRuleAtAccept rule hRule

/-! ### Exact workspace and trace -/

def secondConstraintStartTokens {language : Language}
    (problem : VerifierTableauProblem language) : List CNFToken :=
  BuilderFourthClausePrefix.fourthClauseTokens problem ++ [.sep]

def cursorWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.scratchWord
    (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial
      problem.verifier) problem.input.length

private def cursorOutsideTail {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (BuilderFirstConstraintPaddingRun.countdownFinalOutside problem).drop
    ((cursorWord problem).length + 1)

private theorem predecessor_finalOutside_eq_cursor {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstConstraintPaddingRun.finalOutside problem =
      cursorWord problem ++ BuilderUnaryPolynomial.scratchEndSymbol ::
        cursorOutsideTail problem := by
  unfold BuilderFirstConstraintPaddingRun.finalOutside
    BuilderUnaryPolynomial.finalOutsideLeft
    BuilderUnaryPolynomial.overlayScratch cursorWord cursorOutsideTail
  rfl

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  cursorWord problem ++ BuilderUnaryPolynomial.unitSymbol ::
    BuilderUnaryPolynomial.scratchEndSymbol ::
      (cursorOutsideTail problem).drop 1

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (secondConstraintStartTokens problem)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def appenderWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderTokenAppender.workSteps problem.input
    (BuilderFourthClausePrefix.fourthClauseTokens problem)

def cursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
    (cursorWord problem)

def suffixWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  appenderWorkSteps problem + 1 + cursorWorkSteps problem

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFirstConstraintPaddingRun.workSteps problem + 1 +
    suffixWorkSteps problem

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (secondConstraintStartTokens problem)

def appenderFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := BuilderSecondClauseSeparatorStep.SeparatorCursor.appender.acceptState
    tape := BuilderTokenAppender.workspaceTape problem.input
      (BuilderFirstConstraintPaddingRun.finalOutside problem)
      (secondConstraintStartTokens problem) }

theorem appender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderSecondClauseSeparatorStep.SeparatorCursor.appender (appenderWorkSteps problem)
        (workStartConfiguration BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
          (BuilderFirstConstraintPaddingRun.finalTape problem)) =
      some (appenderFinalConfiguration problem) := by
  have hRunEq : ∀ steps config,
      workRunExact? BuilderSecondClauseSeparatorStep.SeparatorCursor.appender steps config =
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
           | some next => workRunExact? BuilderSecondClauseSeparatorStep.SeparatorCursor.appender steps next) =
          (match workStep? BuilderTokenAppender.machine config with
           | none => none
           | some next => workRunExact? BuilderTokenAppender.machine steps next)
        cases workStep? BuilderTokenAppender.machine config with
        | none => rfl
        | some next => exact ih next
  have hExact := BuilderTokenAppender.appendToken_workRunExact
    problem.input (BuilderFirstConstraintPaddingRun.finalOutside problem)
    (BuilderFourthClausePrefix.fourthClauseTokens problem) .sep
  rw [hRunEq]
  simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.appender, appenderWorkSteps,
    BuilderFirstConstraintPaddingRun.finalTape,
    BuilderTokenAppender.entryConfiguration,
    BuilderTokenAppender.finalConfiguration,
    appenderFinalConfiguration, secondConstraintStartTokens,
    workStartConfiguration] using hExact

def cursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.acceptState
    tape := finalTape problem }

theorem cursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderDynamicTokenCursorStep.CursorAdvance.machine
        (cursorWorkSteps problem)
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (BuilderTokenAppender.workspaceTape problem.input
            (BuilderFirstConstraintPaddingRun.finalOutside problem)
            (secondConstraintStartTokens problem))) =
      some (cursorFinalConfiguration problem) := by
  have hWord : ∀ symbol ∈ cursorWord problem,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol := by
    intro symbol hMem
    exact BuilderUnaryPolynomial.scratchWord_symbol
      (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial
        problem.verifier) problem.input.length symbol (by
          simpa [cursorWord] using hMem)
  have hExact :=
    BuilderDynamicTokenCursorStep.CursorAdvance.advance_workRunExact
      problem.input (cursorWord problem) (cursorOutsideTail problem)
      (secondConstraintStartTokens problem) hWord
  rw [predecessor_finalOutside_eq_cursor]
  simpa [cursorWorkSteps, cursorFinalConfiguration, finalTape, finalOutside]
    using hExact

theorem separatorCursor_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (appenderFinalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration
          BuilderDynamicTokenCursorStep.CursorAdvance.machine
          (appenderFinalConfiguration problem).tape)) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (appenderFinalConfiguration problem).tape
  simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine, appenderFinalConfiguration,
    workStartConfiguration] using hLaunch

theorem suffix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? BuilderSecondClauseSeparatorStep.SeparatorCursor.machine (suffixWorkSteps problem)
        (workStartConfiguration BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
          (BuilderFirstConstraintPaddingRun.finalTape problem)) =
      some
        { state := BuilderSecondClauseSeparatorStep.SeparatorCursor.machine.acceptState
          tape := finalTape problem } := by
  let appenderInitial := workStartConfiguration BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
    (BuilderFirstConstraintPaddingRun.finalTape problem)
  let appenderFinal := appenderFinalConfiguration problem
  let cursorFinal := cursorFinalConfiguration problem
  have hAppender : workRunExact? BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
      (appenderWorkSteps problem) appenderInitial = some appenderFinal := by
    simpa [appenderInitial, appenderFinal] using appender_workRunExact problem
  have hCursor : workRunExact?
      BuilderDynamicTokenCursorStep.CursorAdvance.machine
      (cursorWorkSteps problem)
      { state := BuilderDynamicTokenCursorStep.CursorAdvance.machine.startState
        tape := appenderFinal.tape } = some cursorFinal := by
    simpa [appenderFinal, appenderFinalConfiguration, cursorFinal,
      workStartConfiguration] using cursor_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (appenderWorkSteps problem) (cursorWorkSteps problem)
    appenderInitial appenderFinal cursorFinal hAppender rfl hCursor
  simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine, suffixWorkSteps, appenderInitial,
    cursorFinal, cursorFinalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderFirstConstraintPaddingRun.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (BuilderFirstConstraintPaddingRun.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderFirstConstraintPaddingRun.machine problem) (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderFirstConstraintPaddingRun.machine problem)
        BuilderSecondClauseSeparatorStep.SeparatorCursor.machine)
    (BuilderFirstConstraintPaddingRun.workSteps problem)
    (workStartConfiguration (BuilderFirstConstraintPaddingRun.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderFirstConstraintPaddingRun.finalConfiguration problem)
    (BuilderFirstConstraintPaddingRun.workRunExact problem)
  simpa [machine, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hTransport

theorem prefixSeparator_launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderFirstConstraintPaddingRun.finalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
          (BuilderFirstConstraintPaddingRun.finalTape problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderFirstConstraintPaddingRun.machine problem)
    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
    (BuilderFirstConstraintPaddingRun.finalTape problem)
  simpa [machine, BuilderFirstConstraintPaddingRun.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
/-- Every raw input follows the complete first-constraint padding trace, appends
the constraint-two separator, and advances the retained unary coordinate once. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let prefixInitial := workStartConfiguration
    (BuilderFirstConstraintPaddingRun.machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal := BuilderFirstConstraintPaddingRun.finalConfiguration problem
  let suffixFinal : WorkConfiguration :=
    { state := BuilderSecondClauseSeparatorStep.SeparatorCursor.machine.acceptState
      tape := finalTape problem }
  have hPrefix : workRunExact?
      (BuilderFirstConstraintPaddingRun.machine problem)
      (BuilderFirstConstraintPaddingRun.workSteps problem)
      prefixInitial = some prefixFinal := by
    simpa [prefixInitial, prefixFinal] using
      BuilderFirstConstraintPaddingRun.workRunExact problem
  have hSuffix : workRunExact? BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
      (suffixWorkSteps problem)
      { state := BuilderSecondClauseSeparatorStep.SeparatorCursor.machine.startState
        tape := prefixFinal.tape } = some suffixFinal := by
    simpa [prefixFinal, suffixFinal,
      BuilderFirstConstraintPaddingRun.finalConfiguration,
      workStartConfiguration] using suffix_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderFirstConstraintPaddingRun.machine problem)
    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
    (BuilderFirstConstraintPaddingRun.workSteps problem)
    (suffixWorkSteps problem) prefixInitial prefixFinal suffixFinal
    hPrefix rfl hSuffix
  simpa [machine, workSteps, prefixInitial, suffixFinal,
    finalConfiguration, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

/-! ### Exact schedule semantics -/

/-- The populated opportunity executed by the suffix agrees with the direct
formula-token cursor specification. -/
theorem specification_separator_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderFirstConstraintPaddingRun.secondConstraintStart problem⟩ =
      some (some CNFToken.sep,
        ⟨BuilderFirstConstraintPaddingRun.secondConstraintStart problem + 1⟩) :=
  BuilderFirstConstraintPaddingRun.specification_target_step problem

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

private theorem scheduledShapeConstraint_entry_exactlyOne_nonempty
    {language : Language} (problem : VerifierTableauProblem language)
    (entry : Option (LocalConstraint problem.FormulaWidth))
    (hEntry : entry ∈ problem.scheduledShapeConstraints) :
    ∃ variables : List (Fin problem.FormulaWidth),
      entry = some (.exactlyOne variables) ∧ variables ≠ [] := by
  unfold VerifierTableauProblem.scheduledShapeConstraints at hEntry
  simp only [List.mem_flatMap] at hEntry
  rcases hEntry with ⟨time, _hTime, hRow⟩
  rw [List.mem_append] at hRow
  rcases hRow with hSymbol | hHeadState
  · rcases List.mem_map.mp hSymbol with ⟨position, _hPosition, hEqual⟩
    subst entry
    refine ⟨problem.symbolVariables time position, rfl, ?_⟩
    simp [VerifierTableauProblem.symbolVariables, tapeSymbols]
  · simp at hHeadState
    rcases hHeadState with hHead | hState
    · subst entry
      refine ⟨problem.headVariables time, rfl, ?_⟩
      intro hEmpty
      have hLength := congrArg List.length hEmpty
      rw [problem.headVariables_length] at hLength
      simp only [List.length_nil] at hLength
      exact Nat.ne_of_gt
        (problem.dimensions.tapeWidth_positive problem.tableauInputMode)
        hLength
    · subst entry
      refine ⟨problem.stateVariables time, rfl, ?_⟩
      intro hEmpty
      have hLength := congrArg List.length hEmpty
      rw [problem.stateVariables_length] at hLength
      simp only [List.length_nil] at hLength
      have hStateBound : 0 < problem.dimensions.stateBound := by
        change 0 < machineStateBound problem.rawMachine
        unfold machineStateBound
        exact Nat.zero_lt_succ _
      exact Nat.ne_of_gt hStateBound hLength

private theorem scheduledShapeConstraints_starts_twoExactlyOne_nonempty
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ nextVariable nextVariables rest,
      problem.scheduledShapeConstraints =
        some (problem.symbolShapeAt time position) ::
          some (.exactlyOne (nextVariable :: nextVariables)) :: rest := by
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
      rcases scheduledShapeConstraint_entry_exactlyOne_nonempty problem next
          hNextMem with ⟨variables, hNext, hNonempty⟩
      subst next
      cases variables with
      | nil => exact False.elim (hNonempty rfl)
      | cons nextVariable nextVariables =>
          exact ⟨nextVariable, nextVariables, tail, hRest⟩

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

private theorem formulaConstraintSchedule_starts_twoExactlyOne_nonempty
    {language : Language} (problem : VerifierTableauProblem language) :
    let time : Fin problem.dimensions.timeCount :=
      ⟨0, problem.dimensions.timeCount_positive⟩
    let position : Fin
        (problem.dimensions.tapeWidth problem.tableauInputMode) :=
      ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
    ∃ nextVariable nextVariables rest,
      problem.formulaConstraintSchedule =
        some (problem.symbolShapeAt time position) ::
          some (.exactlyOne (nextVariable :: nextVariables)) :: rest := by
  dsimp
  rcases scheduledShapeConstraints_starts_twoExactlyOne_nonempty problem with
    ⟨nextVariable, nextVariables, rest, hRest⟩
  refine ⟨nextVariable, nextVariables,
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
        Fin problem.FormulaWidth, ∃ nextVariable nextVariables rest,
      problem.formulaClauseSchedule =
        some (atLeastOneBoundedClause
          (problem.symbolVariables time position)) ::
        some (excludeBoundedPairClause left right) ::
        some (excludeBoundedPairClause thirdLeft thirdRight) ::
        some (excludeBoundedPairClause fourthLeft fourthRight) ::
        List.replicate
          (problem.formulaClauseSlotsPerConstraint - 4) none ++
        some (atLeastOneBoundedClause
          (nextVariable :: nextVariables)) :: rest ∧
      left.val = 0 ∧ right.val = 1 ∧
        thirdLeft.val = 0 ∧ thirdRight.val = 2 ∧
        fourthLeft.val = 1 ∧ fourthRight.val = 2 := by
  dsimp
  rcases formulaConstraintSchedule_starts_twoExactlyOne_nonempty problem with
    ⟨nextVariable, nextVariables, constraints, hConstraints⟩
  rcases scheduledExactlyOneClauses_starts_atLeast problem
      (nextVariable :: nextVariables) with
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
    zeroIndex, oneIndex, nextVariable, nextVariables, rest,
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

private theorem scheduledAtLeastOneClauseTokens_starts_sep_t
    {language : Language} (problem : VerifierTableauProblem language)
    (first : Fin problem.FormulaWidth)
    (variables : List (Fin problem.FormulaWidth)) :
    ∃ rest,
      problem.scheduledClauseTokens
          (some (atLeastOneBoundedClause (first :: variables))) =
        some CNFToken.sep :: some CNFToken.t :: rest := by
  let rest :=
    (encodeUnaryTokens first.val ++
      encodeLiteralListTokens
        (BoundedClause.emit (atLeastOneBoundedClause variables)) ++
      [CNFToken.finish]).map some ++
    List.replicate
      (problem.formulaTokensPerClause -
        (encodeClauseTokens
          (BoundedClause.emit
            (atLeastOneBoundedClause (first :: variables)))).length) none
  refine ⟨rest, ?_⟩
  simp [VerifierTableauProblem.scheduledClauseTokens, FormulaSchedule.pad,
    encodeClauseTokens, encodeLiteralListTokens, encodeLiteralTokens,
    BoundedClause.emit, atLeastOneBoundedClause, trueLiteral,
    BoundedLiteral.emit, rest, List.append_assoc]

private theorem formulaClauseTokens_firstConstraint_padding_then_sep_t
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
        some CNFToken.sep :: some CNFToken.t :: rest := by
  rcases formulaClauseSchedule_starts_firstConstraint_then_nextClause problem with
    ⟨left, right, thirdLeft, thirdRight, fourthLeft, fourthRight,
      nextVariable, nextVariables, clauses, hClauses,
      hLeft, hRight, hThirdLeft, hThirdRight,
      hFourthLeft, hFourthRight⟩
  rcases scheduledAtLeastOneClauseTokens_starts_sep_t problem
      nextVariable nextVariables with
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

/-- The finite output is exactly the canonical token prefix through the
separator beginning the second constraint. -/
theorem secondConstraintStartTokens_eq_canonical_formula_prefix
    {language : Language} (problem : VerifierTableauProblem language) :
    ∃ rest, encodeCNFTokens problem.formula =
      secondConstraintStartTokens problem ++ rest := by
  rcases formulaClauseTokens_firstConstraint_padding_then_sep_t problem with
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
         CNFToken.finish, CNFToken.sep, CNFToken.t] ++
          FormulaSchedule.emit clauseTail := by
    rw [hClauseTail]
    simp
  refine ⟨CNFToken.t :: FormulaSchedule.emit clauseTail ++
      [CNFToken.finish], ?_⟩
  rw [← problem.formulaTokenSchedule_emit_eq_encodeCNFTokens]
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [FormulaSchedule.emit_append, FormulaSchedule.emit_append,
    FormulaSchedule.emit_pad, hEmit]
  unfold secondConstraintStartTokens
    BuilderFourthClausePrefix.fourthClauseTokens
    BuilderFourthClauseSecondLiteralPrefix.fourthClauseSecondLiteralTokens
    BuilderFourthClauseSecondLiteralPrefix.secondUnaryTokenOutput
    BuilderFourthClauseSecondLiteralPrefix.firstUnaryTokenOutput
    BuilderFourthClauseSecondLiteralPrefix.signTokenOutput
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
through the second-constraint separator. -/
theorem finalTokenBits_eq_encodedFormula_secondConstraintStart
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (secondConstraintStartTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 37)) := by
  rcases secondConstraintStartTokens_eq_canonical_formula_prefix problem with
    ⟨rest, hTokens⟩
  have hLength :
      (encodeTokenPairs (secondConstraintStartTokens problem)).length =
        2 * (problem.FormulaWidth + 37) := by
    rw [encodeTokenPairs_length, secondConstraintStartTokens,
      List.length_append,
      BuilderFourthClausePrefix.fourthClauseTokens]
    simp [BuilderFourthClauseSecondLiteralPrefix.fourthClauseSecondLiteralTokens,
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
  let suffix := encodeTokenPairs rest ++ [false]
  have hShape : problem.encodedFormula =
      encodeTokenPairs (secondConstraintStartTokens problem) ++ suffix := by
    simp only [VerifierTableauProblem.encodedFormula, encodeCNF]
    rw [hTokens, encodeTokenPairs_append_local]
    simp [suffix, List.append_assoc]
  rw [hShape, ← hLength]
  exact List.take_left.symm

def finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFirstConstraintPaddingRun.secondConstraintStart problem + 1

theorem finalTokenSlot_eq_secondConstraintStart_add_one
    {language : Language} (problem : VerifierTableauProblem language) :
    finalTokenSlot problem = problem.formulaVariableSlotBound + 1 +
        problem.formulaClauseSlotsPerConstraint *
          problem.formulaTokensPerClause + 1 := by
  rw [finalTokenSlot,
    BuilderFirstConstraintPaddingRun.secondConstraintStart_eq]

theorem finalOutside_contains_finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.scratchWord_eq_root
      (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial
        problem.verifier) problem.input.length with
    ⟨wordPrefix, hPrefix⟩
  refine ⟨wordPrefix, (cursorOutsideTail problem).drop 1, ?_⟩
  unfold finalOutside cursorWord finalTokenSlot
  rw [hPrefix, List.replicate_succ']
  simp [BuilderFirstConstraintPaddingRun.secondConstraintStart,
    List.append_assoc]

/-- The coordinate retained after the separator transition is the positive
sign token beginning the first literal of constraint two. -/
theorem nextTokenSlot_direct_eq_t {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect (finalTokenSlot problem) =
      some (some CNFToken.t) := by
  rw [problem.formulaTokenSlotDirect_eq]
  rcases formulaClauseTokens_firstConstraint_padding_then_sep_t problem with
    ⟨rest, hClauses⟩
  unfold VerifierTableauProblem.formulaTokenSchedule
  rw [hClauses, finalTokenSlot,
    BuilderFirstConstraintPaddingRun.secondConstraintStart_eq]
  have hHeader :
      (FormulaSchedule.pad (problem.formulaVariableSlotBound + 1)
        (encodeUnaryTokens problem.FormulaWidth)).length =
          problem.formulaVariableSlotBound + 1 := by
    apply FormulaSchedule.pad_length
    rw [encodeUnaryTokens_length]
    exact Nat.add_le_add_right
      problem.formulaWidth_le_formulaVariableCountPolynomial 1
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
          problem.formulaTokensPerClause + 1 -
      (problem.formulaVariableSlotBound + 1) =
        4 * problem.formulaTokensPerClause + emptyCount + 1 by
          rw [hDecompose]
          omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 4 * problem.formulaTokensPerClause + emptyCount + 1 - 11 =
      (problem.formulaTokensPerClause - 11) +
        3 * problem.formulaTokensPerClause + emptyCount + 1 by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 11) +
      3 * problem.formulaTokensPerClause + emptyCount + 1 -
      (problem.formulaTokensPerClause - 11) =
        3 * problem.formulaTokensPerClause + emptyCount + 1 by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 3 * problem.formulaTokensPerClause + emptyCount + 1 - 7 =
      (problem.formulaTokensPerClause - 7) +
        2 * problem.formulaTokensPerClause + emptyCount + 1 by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 7) +
      2 * problem.formulaTokensPerClause + emptyCount + 1 -
      (problem.formulaTokensPerClause - 7) =
        2 * problem.formulaTokensPerClause + emptyCount + 1 by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show 2 * problem.formulaTokensPerClause + emptyCount + 1 - 8 =
      (problem.formulaTokensPerClause - 8) +
        problem.formulaTokensPerClause + emptyCount + 1 by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 8) +
      problem.formulaTokensPerClause + emptyCount + 1 -
      (problem.formulaTokensPerClause - 8) =
        problem.formulaTokensPerClause + emptyCount + 1 by omega]
  rw [List.getElem?_append]
  simp only [List.length_cons, List.length_nil]
  rw [if_neg (by omega)]
  rw [show problem.formulaTokensPerClause + emptyCount + 1 - 9 =
      (problem.formulaTokensPerClause - 9) + emptyCount + 1 by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [if_neg (by omega)]
  rw [show (problem.formulaTokensPerClause - 9) + emptyCount + 1 -
      (problem.formulaTokensPerClause - 9) = emptyCount + 1 by omega]
  rw [List.getElem?_append, List.length_replicate]
  rw [show (problem.formulaClauseSlotsPerConstraint - 4) *
      problem.formulaTokensPerClause = emptyCount by rfl]
  rw [if_neg (by omega)]
  rw [show emptyCount + 1 - emptyCount = 1 by omega]
  simp

theorem specification_next_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨finalTokenSlot problem⟩ =
      some (some CNFToken.t, ⟨finalTokenSlot problem + 1⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [nextTokenSlot_direct_eq_t]

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

/-- External raw-transition bound for both new bridges, the selected
separator append, and the complete bidirectional cursor scan. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderFirstConstraintPaddingRun.rawTimeBound verifier)
    (.add (.constant 534)
      (.add (scalePolynomial 24 .variable)
        (.add (scalePolynomial 12 (formulaWidthPolynomial verifier))
          (scalePolynomial 12
            (BuilderUnaryPolynomial.registerSpanPolynomial
              (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial
                verifier))))))

private theorem fourthClauseTokens_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (BuilderFourthClausePrefix.fourthClauseTokens problem).length =
      problem.FormulaWidth + 36 := by
  simp [BuilderFourthClausePrefix.fourthClauseTokens,
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

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderFirstConstraintPaddingRun.rawTimeBound problem.verifier).eval
          problem.input.length + 534 +
        24 * problem.input.length + 12 * problem.FormulaWidth +
        12 * (cursorWord problem).length := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, NatPolynomial.eval_variable, scalePolynomial]
  have hWidth :
      (formulaWidthPolynomial problem.verifier).eval problem.input.length =
        problem.FormulaWidth := by
    simpa [BitString.size] using problem.formulaWidthPolynomial_eval
  rw [hWidth]
  rw [← BuilderUnaryPolynomial.scratchWord_length
    (BuilderFirstConstraintPaddingRun.secondConstraintStartPolynomial
      problem.verifier) problem.input.length]
  simp only [cursorWord]
  omega

private theorem appenderWorkSteps_le {language : Language}
    (problem : VerifierTableauProblem language) :
    appenderWorkSteps problem ≤
      4 * problem.input.length + 2 * problem.FormulaWidth + 80 := by
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  unfold appenderWorkSteps BuilderTokenAppender.workSteps
    BuilderTokenAppender.halfSteps
  rw [fourthClauseTokens_length]
  omega

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := BuilderFirstConstraintPaddingRun.rawTimeBound_le problem
  have hAppender := appenderWorkSteps_le problem
  rw [rawTimeBound_eval]
  unfold workSteps suffixWorkSteps cursorWorkSteps
    BuilderDynamicTokenCursorStep.CursorAdvance.advanceWorkSteps
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

private theorem machine_isHalted_predecessor_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          config) = false := by
  have hHalted :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      (BuilderFirstConstraintPaddingRun.machine problem)
      BuilderSecondClauseSeparatorStep.SeparatorCursor.machine config
  simpa [machine] using hHalted

/-- The complete second-clause padding endpoint is still globally nonhalting
until the outer bridge launches the selected separator appender. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFirstConstraintPaddingRun.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderFirstConstraintPaddingRun.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (BuilderFirstConstraintPaddingRun.finalConfiguration problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_predecessor_false problem
      (BuilderFirstConstraintPaddingRun.finalConfiguration problem))

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

private theorem appenderEndpoint_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderFirstConstraintPaddingRun.workSteps problem + 1 +
          appenderWorkSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration
          BuilderFirstClausePrefix.WorkChain.firstState
          (appenderFinalConfiguration problem))) := by
  let initial := workStartConfiguration (machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstConstraintPaddingRun.finalConfiguration problem)
  let suffixInitial := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState
    (workStartConfiguration BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
      (BuilderFirstConstraintPaddingRun.finalTape problem))
  let appenderFinal := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (appenderFinalConfiguration problem))
  have hPrefix : workRunExact? (machine problem)
      (BuilderFirstConstraintPaddingRun.workSteps problem) initial =
        some prefixFinal := by
    simpa [initial, prefixFinal] using prefix_workRunExact problem
  have hLaunch : workRunExact? (machine problem) 1 prefixFinal =
      some suffixInitial := by
    apply workRunExact_one_of_workStep problem
    simpa [prefixFinal, suffixInitial] using
      prefixSeparator_launch_workStep problem
  have hInner := PipelineStageBridges.workRunExact?_transport
    BuilderSecondClauseSeparatorStep.SeparatorCursor.appender BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine)
    (appenderWorkSteps problem)
    (workStartConfiguration BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
      (BuilderFirstConstraintPaddingRun.finalTape problem))
    (appenderFinalConfiguration problem) (appender_workRunExact problem)
  have hGlobal := PipelineStageBridges.workRunExact?_transport
    BuilderSecondClauseSeparatorStep.SeparatorCursor.machine (machine problem)
    BuilderFirstClausePrefix.WorkChain.secondState
    (BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
      (BuilderFirstConstraintPaddingRun.machine problem) BuilderSecondClauseSeparatorStep.SeparatorCursor.machine)
    (appenderWorkSteps problem)
    (workStartConfiguration BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
      (BuilderFirstConstraintPaddingRun.finalTape problem))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (appenderFinalConfiguration problem)) (by
        simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine,
          BuilderFirstClausePrefix.WorkChain.machine,
          workStartConfiguration, renameConfiguration] using hInner)
  have h01 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem) (BuilderFirstConstraintPaddingRun.workSteps problem) 1
    initial prefixFinal suffixInitial hPrefix hLaunch
  have h02 := PipelineMachineSimulation.workRunExact?_compose
    (machine problem)
    (BuilderFirstConstraintPaddingRun.workSteps problem + 1)
    (appenderWorkSteps problem) initial suffixInitial appenderFinal h01 (by
      simpa [suffixInitial, appenderFinal] using hGlobal)
  simpa [initial, appenderFinal, Nat.add_assoc] using h02

private theorem machine_isHalted_appender_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
            config)) = false := by
  have hInner :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine config
  have hGlobal :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      (BuilderFirstConstraintPaddingRun.machine problem) BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        config) (by simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine] using hInner)
  simpa [machine] using hGlobal

/-- The selected separator appender endpoint remains a timeout until the
inner bridge launches the cursor-advance table. -/
theorem appenderEndpoint_before_cursor_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFirstConstraintPaddingRun.workSteps problem + 1 +
          appenderWorkSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderFirstConstraintPaddingRun.workSteps problem + 1 +
      appenderWorkSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
        (appenderFinalConfiguration problem)))
    (appenderEndpoint_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_appender_false problem
      (appenderFinalConfiguration problem))

private theorem selectedAppender_stuck_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (bad : WorkConfiguration)
    (hLocalHalted : BuilderTokenAppender.machine.isHalted bad = false)
    (hLocalStep : workStep? BuilderTokenAppender.machine bad = none) :
    (let config := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState bad)
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let innerConfig := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.firstState bad
  let globalConfig := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState innerConfig
  have hSelectedHalted : BuilderSecondClauseSeparatorStep.SeparatorCursor.appender.isHalted bad = false := by
    change BuilderTokenAppender.machine.isHalted bad = false
    exact hLocalHalted
  have hSelectedStep : workStep? BuilderSecondClauseSeparatorStep.SeparatorCursor.appender bad = none := by
    change workStep? BuilderTokenAppender.machine bad = none
    exact hLocalStep
  have hAccept := state_ne_accept_of_not_halted
    BuilderSecondClauseSeparatorStep.SeparatorCursor.appender bad hSelectedHalted
  have hInnerStep : workStep? BuilderSecondClauseSeparatorStep.SeparatorCursor.machine innerConfig = none := by
    have hStep := first_workStep_none_of_local BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
        BuilderDynamicTokenCursorStep.CursorAdvance.machine bad hAccept
        hSelectedHalted hSelectedStep
    simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine, innerConfig] using hStep
  have hInnerHalted : BuilderSecondClauseSeparatorStep.SeparatorCursor.machine.isHalted innerConfig = false := by
    have hHalted :=
      BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
        BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
        BuilderDynamicTokenCursorStep.CursorAdvance.machine bad
    simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine, innerConfig] using hHalted
  have hGlobalStep : workStep? (machine problem) globalConfig = none := by
    have hStep := second_workStep_none_of_local
        (BuilderFirstConstraintPaddingRun.machine problem) BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
        innerConfig hInnerHalted hInnerStep
    simpa [machine, globalConfig] using hStep
  have hGlobalHalted : (machine problem).isHalted globalConfig = false := by
    have hHalted :=
      BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
        (BuilderFirstConstraintPaddingRun.machine problem) BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
        innerConfig hInnerHalted
    simpa [machine, globalConfig] using hHalted
  exact stuck_timeout problem fuel globalConfig hGlobalHalted hGlobalStep

/-- A malformed tally-phase symbol in the selected separator appender is
globally stuck and nonhalting for every fuel budget. -/
theorem malformedAppenderTally_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderTokenAppender.malformedTallyConfiguration
            request left right))
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedTallyConfiguration
    request left right
  exact selectedAppender_stuck_timeout problem fuel bad
    (BuilderTokenAppender.malformedTallySymbol_isHalted_false
      request left right)
    (BuilderTokenAppender.malformedTallySymbol_workStep_none
      request left right)

/-- A malformed output-phase symbol in the selected separator appender also
cannot fall through to either global halt. -/
theorem malformedAppenderOutput_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (request : CNFToken) (left right : List WorkSymbol) :
    (let config := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderTokenAppender.malformedOutputConfiguration
            request left right))
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := BuilderTokenAppender.malformedOutputConfiguration
    request left right
  exact selectedAppender_stuck_timeout problem fuel bad
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

private theorem globalCursorMalformed_workStep {language : Language}
    (problem : VerifierTableauProblem language)
    (left right : List WorkSymbol) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
            (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
              left right))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (cursorDeadConfiguration
            (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
              left right).tape))) := by
  let bad :=
    BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
      left right
  let dead := cursorDeadConfiguration bad.tape
  have hInner := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine bad dead (by
      simpa [bad, dead] using cursorMalformed_workStep left right)
  have hGlobal := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderFirstConstraintPaddingRun.machine problem) BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState bad)
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState dead)
    (by simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine] using hInner)
  simpa [machine, bad, dead] using hGlobal

private theorem globalCursorDead_workStep {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
            (cursorDeadConfiguration tape))) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (cursorDeadConfiguration tape))) := by
  have hInner := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
    BuilderDynamicTokenCursorStep.CursorAdvance.machine
    (cursorDeadConfiguration tape) (cursorDeadConfiguration tape)
    (cursorDead_workStep tape)
  have hGlobal := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderFirstConstraintPaddingRun.machine problem) BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (cursorDeadConfiguration tape))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
      (cursorDeadConfiguration tape)) (by
        simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine] using hInner)
  simpa [machine] using hGlobal

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

private theorem localCursorMalformed_isHalted_false
    (left right : List WorkSymbol) :
    BuilderDynamicTokenCursorStep.CursorAdvance.machine.isHalted
      (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
        left right) = false := by
  rfl

private theorem localCursorDead_isHalted_false (tape : WorkTape) :
    BuilderDynamicTokenCursorStep.CursorAdvance.machine.isHalted
      (cursorDeadConfiguration tape) = false := by
  rfl

private theorem globalCursorMalformed_isHalted_false {language : Language}
    (problem : VerifierTableauProblem language)
    (left right : List WorkSymbol) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
            (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
              left right))) = false := by
  let bad :=
    BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
      left right
  have hInner :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine bad (by
        simpa [bad] using localCursorMalformed_isHalted_false left right)
  have hGlobal :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      (BuilderFirstConstraintPaddingRun.machine problem) BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState bad)
      (by simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine] using hInner)
  simpa [machine, bad] using hGlobal

private theorem globalCursorDead_isHalted_false {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
            (cursorDeadConfiguration tape))) = false := by
  have hInner :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      BuilderSecondClauseSeparatorStep.SeparatorCursor.appender
      BuilderDynamicTokenCursorStep.CursorAdvance.machine
      (cursorDeadConfiguration tape) (localCursorDead_isHalted_false tape)
  have hGlobal :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      (BuilderFirstConstraintPaddingRun.machine problem) BuilderSecondClauseSeparatorStep.SeparatorCursor.machine
      (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (cursorDeadConfiguration tape)) (by
          simpa [BuilderSecondClauseSeparatorStep.SeparatorCursor.machine] using hInner)
  simpa [machine] using hGlobal

/-- A malformed cursor scratch symbol enters the explicit nonhalting dead
state and remains timeout for every fuel budget. -/
theorem malformedCursorScratch_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (left right : List WorkSymbol) :
    (let config := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
            left right))
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad :=
    BuilderDynamicTokenCursorStep.CursorAdvance.malformedScratchConfiguration
      left right
  let dead := cursorDeadConfiguration bad.tape
  let globalBad := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState bad)
  let globalDead := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState dead)
  cases fuel with
  | zero =>
      change
        (if globalBad.state == (machine problem).acceptState then
          WorkVerdict.accept
         else if globalBad.state == (machine problem).rejectState then
          WorkVerdict.reject
         else WorkVerdict.timeout) = WorkVerdict.timeout
      exact verdict_timeout_of_not_halted problem globalBad (by
        simpa [globalBad, bad] using
          globalCursorMalformed_isHalted_false problem left right)
  | succ fuel =>
      have hRun : workRun (machine problem) (fuel + 1) globalBad =
          globalDead := by
        exact workRun_succ_eq_of_step_and_loop
          (machine problem) fuel globalBad globalDead (by
            simpa [globalBad, globalDead, bad, dead] using
              globalCursorMalformed_workStep problem left right) (by
            simpa [globalDead, dead] using
              globalCursorDead_workStep problem bad.tape)
      change
        (let result := workRun (machine problem) (fuel + 1) globalBad
         if result.state == (machine problem).acceptState then
           WorkVerdict.accept
         else if result.state == (machine problem).rejectState then
           WorkVerdict.reject
         else WorkVerdict.timeout) = WorkVerdict.timeout
      rw [hRun]
      exact verdict_timeout_of_not_halted problem globalDead (by
        simpa [globalDead, dead] using
          globalCursorDead_isHalted_false problem bad.tape)

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

end BuilderSecondConstraintSeparatorStep

end CookLevin

end PNP.Concrete
