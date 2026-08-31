/-
Copyright (c) 2026 PNP Labs.

All-coordinate executable orchestration from M214's literal post-divider
classifier into the existing fixed token appender.

For every post-header schedule coordinate, this module derives the exact
padding, body-token, or final `Finish` action from the canonical direct
schedule, retains M214's physical classifier evidence, and runs the fixed
59-rule appender exactly when that derived action contains a token.  The
result is the next canonical emitted-token prefix, with exact compiled and
one-step-short evidence and one source-size polynomial bound.

The handoff that chooses the appender state is executable Lean orchestration,
not yet a literal tape-to-tape selector.  This module does not iterate the
schedule, construct the complete raw formula, prove builder `RawRefinement`,
package the Cook--Levin reduction, prove `CNFSAT` in `P`, or prove `P = NP`.
-/

import PNP.Concrete.CookLevinBuilderPostDividerRawRouteClassifier
import PNP.Concrete.CookLevinBuilderTokenAppender

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPostDividerSelectedTokenLaunch

open BuilderArbitrarySlotHeaderRouter
  BuilderArbitrarySlotPostHeaderDecoder

abbrev appenderMachine : WorkMachine := BuilderTokenAppender.machine

/-- Embed one post-header coordinate into the complete token schedule. -/
def scheduleCoordinate {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Fin (BuilderFullScheduleCursorController.terminalSlot problem) :=
  ⟨BuilderFullScheduleCursorController.firstBodySlot problem + index.val, by
    rw [← BuilderFullScheduleCursorController.firstBodySlot_add_bodySlotCount
      problem]
    omega⟩

/-- Tokens emitted strictly before one post-header coordinate.  Empty
schedule opportunities disappear exactly as in the canonical formula
encoding. -/
def emittedPrefix {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    List CNFToken :=
  FormulaSchedule.emit
    (problem.formulaTokenSchedule.take
      (BuilderFullScheduleCursorController.firstBodySlot problem + index))

/-- M210's typed post-header interpreter supplies either an invalid outer
coordinate, one valid padding opportunity, or one selected token. -/
def selectedEntry? {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option CNFToken) :=
  (postHeaderRoute problem index).token?

theorem scheduleCoordinate_outerRoute {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    outerRoute problem (scheduleCoordinate problem index).val =
      .postHeader index.val := by
  apply (outerRoute_eq_postHeader_iff problem
    (scheduleCoordinate problem index).val index.val).2
  dsimp [scheduleCoordinate]
  constructor <;> omega

/-- The selected post-header entry is exactly the complete direct lookup at
the corresponding global schedule coordinate. -/
theorem selectedEntry?_eq_formulaTokenSlotDirect {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    selectedEntry? problem index.val =
      problem.formulaTokenSlotDirect (scheduleCoordinate problem index).val := by
  rw [BuilderArbitrarySlotPostHeaderDecoder.formulaTokenSlotDirect_decoded
    problem]
  unfold selectedEntry?
    BuilderArbitrarySlotPostHeaderDecoder.decodedTokenSlotDirect
  rw [scheduleCoordinate_outerRoute]

theorem selectedEntry?_eq_schedule_getElem? {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    selectedEntry? problem index.val =
      problem.formulaTokenSchedule[(scheduleCoordinate problem index).val]? := by
  rw [selectedEntry?_eq_formulaTokenSlotDirect,
    problem.formulaTokenSlotDirect_eq]

theorem scheduleCoordinate_lt_schedule_length {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    (scheduleCoordinate problem index).val <
      problem.formulaTokenSchedule.length := by
  simpa only
      [← BuilderFullScheduleCursorController.finalTokenSlot_eq_complete_schedule
        problem] using (scheduleCoordinate problem index).isLt

/-- The proof-carrying entry at one valid embedded post-header coordinate. -/
def scheduleEntry {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Option CNFToken :=
  problem.formulaTokenSchedule[(scheduleCoordinate problem index).val]'
    (scheduleCoordinate_lt_schedule_length problem index)

/-- Every post-header coordinate selected by the complete controller has a
valid schedule entry.  The inner option alone records padding versus a
token; no token or success witness is supplied to the theorem. -/
theorem selectedEntry?_eq_some_getElem {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    selectedEntry? problem index.val = some (scheduleEntry problem index) := by
  rw [selectedEntry?_eq_schedule_getElem?, List.getElem?_eq_getElem
    (scheduleCoordinate_lt_schedule_length problem index)]
  rfl

theorem selectedEntry?_body {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : postHeaderRoute problem index =
      .body clauseCoordinate tokenCoordinate) :
    selectedEntry? problem index =
      problem.clauseTokenBlockSlotDirect clauseCoordinate
        tokenCoordinate.val := by
  simp [selectedEntry?, hRoute, PostHeaderRoute.token?]

theorem selectedEntry?_finish {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (hRoute : postHeaderRoute problem index = .finish) :
    selectedEntry? problem index = some (some .finish) := by
  simp [selectedEntry?, hRoute, PostHeaderRoute.token?]

/-- Emitting the next populated schedule entry either preserves the prefix
at padding or appends exactly the selected token. -/
theorem emittedPrefix_succ {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    emittedPrefix problem (index.val + 1) =
      match scheduleEntry problem index with
      | none => emittedPrefix problem index.val
      | some token => emittedPrefix problem index.val ++ [token] := by
  have hCoordinate := scheduleCoordinate_lt_schedule_length problem index
  unfold emittedPrefix
  have hCurrent :
      BuilderFullScheduleCursorController.firstBodySlot problem + index.val =
        (scheduleCoordinate problem index).val := by
    rfl
  have hNext :
      BuilderFullScheduleCursorController.firstBodySlot problem +
          (index.val + 1) =
        (scheduleCoordinate problem index).val + 1 := by
    dsimp [scheduleCoordinate]
    omega
  rw [hCurrent, hNext,
    List.take_succ_eq_append_getElem hCoordinate,
    FormulaSchedule.emit_append]
  unfold scheduleEntry
  cases problem.formulaTokenSchedule[(scheduleCoordinate problem index).val]'hCoordinate <;>
    simp

/-- Final staged configuration after skipping padding or appending the
schedule-selected token. -/
def launch? {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) : Option WorkConfiguration :=
  match selectedEntry? problem index.val with
  | none => none
  | some none =>
      some (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
        (emittedPrefix problem index.val))
  | some (some token) =>
      some (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
        (emittedPrefix problem index.val ++ [token]))

theorem launch?_eq_nextPrefix {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) :
    launch? problem index outsideLeft =
      some (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
        (emittedPrefix problem (index.val + 1))) := by
  unfold launch?
  rw [selectedEntry?_eq_some_getElem, emittedPrefix_succ]
  cases scheduleEntry problem index <;>
    rfl

private theorem emit_length_le (schedule : List (Option α)) :
    (FormulaSchedule.emit schedule).length <= schedule.length := by
  induction schedule with
  | nil => exact Nat.le_refl 0
  | cons entry rest ih =>
      cases entry with
      | none =>
          simp only [FormulaSchedule.emit_none, List.length_cons]
          exact Nat.le_trans ih (Nat.le_succ _)
      | some item =>
          simp only [FormulaSchedule.emit_some, List.length_cons]
          exact Nat.succ_le_succ ih

theorem emittedPrefix_length_le_terminalSlot {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    (emittedPrefix problem index).length <=
      BuilderFullScheduleCursorController.terminalSlot problem := by
  unfold emittedPrefix
  calc
    (FormulaSchedule.emit
      (problem.formulaTokenSchedule.take
        (BuilderFullScheduleCursorController.firstBodySlot problem + index))).length <=
        (problem.formulaTokenSchedule.take
          (BuilderFullScheduleCursorController.firstBodySlot problem + index)).length :=
      emit_length_le _
    _ <= problem.formulaTokenSchedule.length := List.length_take_le' _ _
    _ = BuilderFullScheduleCursorController.terminalSlot problem :=
      (BuilderFullScheduleCursorController.finalTokenSlot_eq_complete_schedule
        problem).symm

theorem appender_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) (request : CNFToken) :
    workRunExact? appenderMachine
        (BuilderTokenAppender.workSteps problem.input
          (emittedPrefix problem index.val))
        (BuilderTokenAppender.entryConfiguration request
          (BuilderTokenAppender.workspaceTape problem.input outsideLeft
            (emittedPrefix problem index.val))) =
      some (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
        (emittedPrefix problem index.val ++ [request])) := by
  exact BuilderTokenAppender.appendToken_workRunExact problem.input
    outsideLeft (emittedPrefix problem index.val) request

theorem appender_run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) (request : CNFToken) :
    run (compileWorkMachine appenderMachine)
        (6 * BuilderTokenAppender.workSteps problem.input
          (emittedPrefix problem index.val))
        (encodeWorkConfiguration
          (BuilderTokenAppender.entryConfiguration request
            (BuilderTokenAppender.workspaceTape problem.input outsideLeft
              (emittedPrefix problem index.val)))) =
      encodeWorkConfiguration
        (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
          (emittedPrefix problem index.val ++ [request])) := by
  exact run_compileWorkMachine_mul_of_workRunExact appenderMachine
    (BuilderTokenAppender.workSteps problem.input
      (emittedPrefix problem index.val))
    (BuilderTokenAppender.entryConfiguration request
      (BuilderTokenAppender.workspaceTape problem.input outsideLeft
        (emittedPrefix problem index.val)))
    (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
      (emittedPrefix problem index.val ++ [request]))
    (appender_workRunExact problem index outsideLeft request)

private theorem workRunExact_succ_split_last (selectedMachine : WorkMachine) :
    forall (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? selectedMachine (steps + 1) initial = some final ->
      exists before,
        workRunExact? selectedMachine steps initial = some before /\
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

private theorem one_step_short_not_halted_of_exact
    (selectedMachine : WorkMachine) (steps : Nat)
    (initial final : WorkConfiguration)
    (hPositive : 0 < steps)
    (hExact : workRunExact? selectedMachine steps initial = some final) :
    selectedMachine.isHalted
        (workRun selectedMachine (steps - 1) initial) = false := by
  let short := steps - 1
  have hSucc : short + 1 = steps := by
    dsimp [short]
    omega
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last selectedMachine short initial final
      hExact with ⟨before, hPrefix, hLast⟩
  have hRun : workRun selectedMachine short initial = before :=
    workRun_eq_of_workRunExact selectedMachine short initial before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some selectedMachine before final hLast

theorem appender_workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    0 < BuilderTokenAppender.workSteps problem.input
      (emittedPrefix problem index) := by
  have hSource := BuilderTokenAppender.sourceCellCount_positive problem.input
  unfold BuilderTokenAppender.workSteps BuilderTokenAppender.halfSteps
  omega

theorem appender_one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (outsideLeft : List WorkSymbol) (request : CNFToken) :
    appenderMachine.isHalted
        (workRun appenderMachine
          (BuilderTokenAppender.workSteps problem.input
            (emittedPrefix problem index.val) - 1)
          (BuilderTokenAppender.entryConfiguration request
            (BuilderTokenAppender.workspaceTape problem.input outsideLeft
              (emittedPrefix problem index.val)))) = false := by
  exact one_step_short_not_halted_of_exact appenderMachine
    (BuilderTokenAppender.workSteps problem.input
      (emittedPrefix problem index.val))
    (BuilderTokenAppender.entryConfiguration request
      (BuilderTokenAppender.workspaceTape problem.input outsideLeft
        (emittedPrefix problem index.val)))
    (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
      (emittedPrefix problem index.val ++ [request]))
    (appender_workSteps_positive problem index.val)
    (appender_workRunExact problem index outsideLeft request)

/-- Polynomial bound for one selected appender trace after any canonical
schedule prefix. -/
def appenderRawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.linear 24 48)
    (.mul (.constant 12)
      (BuilderFullScheduleCursorController.terminalSlotPolynomial verifier))

theorem appenderRawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (appenderRawTimeBound problem.verifier).eval problem.input.length =
      24 * problem.input.length + 48 +
        12 * BuilderFullScheduleCursorController.terminalSlot problem := by
  rfl

theorem appenderCompiledSteps_le {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    6 * BuilderTokenAppender.workSteps problem.input
        (emittedPrefix problem index) <=
      (appenderRawTimeBound problem.verifier).eval problem.input.length := by
  rw [appenderRawTimeBound_eval]
  have hSource := BuilderTokenAppender.sourceCellCount_le problem.input
  have hOutput := emittedPrefix_length_le_terminalSlot problem index
  unfold BuilderTokenAppender.workSteps BuilderTokenAppender.halfSteps
  omega

/-- Total compiled work of M214's exact route classifier followed, on a
populated entry only, by the exact selected-token appender. -/
def stagedCompiledSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Nat :=
  BuilderPostDividerRawRouteClassifier.stagedCompiledSteps problem
      (scheduleCoordinate problem index).val +
    match selectedEntry? problem index.val with
    | some (some _) =>
        6 * BuilderTokenAppender.workSteps problem.input
          (emittedPrefix problem index.val)
    | _ => 0

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPostDividerRawRouteClassifier.rawTimeBound verifier)
    (appenderRawTimeBound verifier)

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPostDividerRawRouteClassifier.rawTimeBound
        problem.verifier).eval problem.input.length +
      (appenderRawTimeBound problem.verifier).eval problem.input.length := by
  rfl

theorem stagedCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    stagedCompiledSteps problem index <=
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hClassifier :=
    BuilderPostDividerRawRouteClassifier.stagedCompiledSteps_le_rawTimeBound
      problem (scheduleCoordinate problem index).val
      (scheduleCoordinate problem index).isLt
  have hAppender := appenderCompiledSteps_le problem index.val
  unfold stagedCompiledSteps
  rw [rawTimeBound_eval]
  cases hSelected : selectedEntry? problem index.val with
  | none =>
      simpa using Nat.le_add_right_of_le hClassifier
  | some entry =>
      cases entry with
      | none =>
          simpa using Nat.le_add_right_of_le hClassifier
      | some token =>
          exact Nat.add_le_add hClassifier hAppender

/-- Exact per-coordinate contract.  M214 supplies the physical route and
preserves arbitrary classifier workspace.  The canonical schedule then
selects either padding or one token; populated entries run the fixed raw
appender and reach exactly the next emitted prefix. -/
def PostDividerEmissionHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (classifierWorkspace outsideLeft : List WorkSymbol) : Prop :=
  BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds problem
      (scheduleCoordinate problem index) classifierWorkspace /\
    launch? problem index outsideLeft =
      some (BuilderTokenAppender.finalConfiguration problem.input outsideLeft
        (emittedPrefix problem (index.val + 1))) /\
    match selectedEntry? problem index.val with
    | none => False
    | some none =>
        emittedPrefix problem (index.val + 1) =
          emittedPrefix problem index.val
    | some (some token) =>
        emittedPrefix problem (index.val + 1) =
            emittedPrefix problem index.val ++ [token] /\
          workRunExact? appenderMachine
              (BuilderTokenAppender.workSteps problem.input
                (emittedPrefix problem index.val))
              (BuilderTokenAppender.entryConfiguration token
                (BuilderTokenAppender.workspaceTape problem.input outsideLeft
                  (emittedPrefix problem index.val))) =
            some (BuilderTokenAppender.finalConfiguration problem.input
              outsideLeft (emittedPrefix problem (index.val + 1))) /\
          run (compileWorkMachine appenderMachine)
              (6 * BuilderTokenAppender.workSteps problem.input
                (emittedPrefix problem index.val))
              (encodeWorkConfiguration
                (BuilderTokenAppender.entryConfiguration token
                  (BuilderTokenAppender.workspaceTape problem.input outsideLeft
                    (emittedPrefix problem index.val)))) =
            encodeWorkConfiguration
              (BuilderTokenAppender.finalConfiguration problem.input
                outsideLeft (emittedPrefix problem (index.val + 1))) /\
          appenderMachine.isHalted
              (workRun appenderMachine
                (BuilderTokenAppender.workSteps problem.input
                  (emittedPrefix problem index.val) - 1)
                (BuilderTokenAppender.entryConfiguration token
                  (BuilderTokenAppender.workspaceTape problem.input outsideLeft
                    (emittedPrefix problem index.val)))) = false

theorem postDividerEmissionHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (classifierWorkspace outsideLeft : List WorkSymbol) :
    PostDividerEmissionHolds problem index classifierWorkspace outsideLeft := by
  have hClassifier :=
    BuilderPostDividerRawRouteClassifier.inRangeRouteClassifierHolds problem
      (scheduleCoordinate problem index) classifierWorkspace
  have hLaunch := launch?_eq_nextPrefix problem index outsideLeft
  refine ⟨hClassifier, hLaunch, ?_⟩
  have hSelected := selectedEntry?_eq_some_getElem problem index
  have hNext := emittedPrefix_succ problem index
  cases hEntry : scheduleEntry problem index with
  | none =>
      rw [hEntry] at hSelected hNext
      rw [hSelected]
      exact hNext
  | some token =>
      rw [hEntry] at hSelected hNext
      rw [hSelected]
      refine ⟨hNext, ?_, ?_, ?_⟩
      · rw [hNext]
        exact appender_workRunExact problem index outsideLeft token
      · rw [hNext]
        exact appender_run_compile_exact problem index outsideLeft token
      · exact appender_one_step_short_not_halted problem index outsideLeft token

/-- M215 closes the all-coordinate executable selected-token launch boundary:
M214's exact physical body/`Finish` classification is retained, the canonical
schedule derives padding or the exact token without a supplied route or token,
and every populated entry runs the fixed appender to the next canonical
emitted prefix within one source-size polynomial.  The selection handoff is
still Lean orchestration rather than a literal raw tape rewrite, and this
theorem does not iterate the schedule or complete the builder or reduction. -/
theorem cook_levin_builder_post_divider_selected_token_launch_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    (forall index :
        Fin (BuilderFullScheduleCursorController.bodySlotCount problem),
      selectedEntry? problem index.val =
        some (scheduleEntry problem index)) /\
    (forall index classifierWorkspace outsideLeft,
      PostDividerEmissionHolds problem index classifierWorkspace outsideLeft) /\
    (forall index,
      stagedCompiledSteps problem index <=
        (rawTimeBound problem.verifier).eval problem.input.length) := by
  exact ⟨selectedEntry?_eq_some_getElem problem,
    postDividerEmissionHolds problem,
    stagedCompiledSteps_le_rawTimeBound problem⟩

end BuilderPostDividerSelectedTokenLaunch

end CookLevin

end PNP.Concrete
