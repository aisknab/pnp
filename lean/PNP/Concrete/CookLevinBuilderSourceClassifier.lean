/-
Copyright (c) 2026 PNP Labs.

Source-derived body/Finish classification for the complete Cook--Levin builder.
Reuse the literal sidecar-copy bridge and unary comparator after the actual
source-derived divider execution. All source registers, input and existing
output remain protected. No caller supplies a prepared entry or selected route.

The comparator's accept state means body and, only for an in-range coordinate,
its reject state means Finish. This phase does not select/emit body tokens,
restore loop scratch, or implement the complete formula builder and reduction.
-/

import PNP.Concrete.CookLevinBuilderDividerSourceExecution

namespace PNP.Concrete.CookLevin.BuilderSourceClassifier

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (count width)
open BuilderDividerSourceExecution (preservedWorkspace)
open BuilderArbitrarySlotHeaderRouter
open BuilderPhysicalClassifierFinishMirroredDispatch
  (mirrorTape mirrorMachine mirrorRule mirrorConfiguration workRunExact?_mirror_of_some
    mirrorRules_pairwise_query_distinct mirrorMachine_acceptState_ne_rejectState)

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat)
    (tape : WorkTape) (hState : config.state = state) (hTape : config.tape = tape) :
    config = { state := state, tape := tape } := by
  cases config with
  | mk currentState currentTape =>
    change currentState = state at hState
    change currentTape = tape at hTape
    subst currentState
    subst currentTape
    rfl

def classifierMachine : WorkMachine := mirrorMachine BuilderPostDividerRawRouteClassifier.machine

def comparatorMachine : WorkMachine := mirrorMachine RawRouter.machine

/-- The same fixed 180-rule bridge and 54-rule comparator, with one serial bridge. -/
def tailMachine : WorkMachine := WorkMachineChain.machine classifierMachine comparatorMachine

def tailInitial (consumed remainder width quotient count : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration tailMachine
    (mirrorTape (BuilderPostDividerRawRouteClassifier.inputTape
      consumed remainder width quotient [] count workspace))

def tailExterior (consumed remainder width count : Nat)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.preservedExterior consumed remainder width [] count workspace

def tailFinal (consumed remainder width quotient count : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (mirrorConfiguration (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration
      quotient count (tailExterior consumed remainder width count workspace)))

def tailSteps (consumed remainder width quotient count : Nat) : Nat :=
  BuilderPostDividerRawRouteClassifier.workSteps consumed remainder width quotient count [] + 1 +
    RawRouter.workSteps quotient count

/-- Both actual fixed-machine traces, including the serial transition between them. -/
theorem tail_workRunExact (consumed remainder width quotient count : Nat)
    (workspace : List WorkSymbol) :
    workRunExact? tailMachine (tailSteps consumed remainder width quotient count)
        (tailInitial consumed remainder width quotient count workspace) =
      some (tailFinal consumed remainder width quotient count workspace) := by
  have hPrefix : BuilderPostDividerRawRouteClassifier.SafeExteriorPrefix [] := by
    intro symbol hMem
    cases hMem
  have hBridge := workRunExact?_mirror_of_some BuilderPostDividerRawRouteClassifier.machine
    (BuilderPostDividerRawRouteClassifier.workSteps consumed remainder width quotient count [])
    (BuilderPostDividerRawRouteClassifier.inputConfiguration consumed remainder width quotient [] count workspace)
    (BuilderPostDividerRawRouteClassifier.comparatorInputConfiguration quotient count
      (tailExterior consumed remainder width count workspace))
    (BuilderPostDividerRawRouteClassifier.workRunExact consumed remainder width quotient count [] workspace hPrefix)
  have hCompare := workRunExact?_mirror_of_some RawRouter.machine (RawRouter.workSteps quotient count)
    (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration quotient count
      (tailExterior consumed remainder width count workspace))
    (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration quotient count
      (tailExterior consumed remainder width count workspace))
    (BuilderPostDividerRawRouteClassifier.shielded_comparator_workRunExact quotient count
      (tailExterior consumed remainder width count workspace))
  exact WorkMachineChain.workRunExact classifierMachine comparatorMachine
    (BuilderPostDividerRawRouteClassifier.workSteps consumed remainder width quotient count [])
    (RawRouter.workSteps quotient count) _ _ _ hBridge rfl hCompare

set_option maxRecDepth 1000000 in
theorem tail_rules_length : tailMachine.rules.length = 243 := rfl

private theorem mirror_noRule (source : WorkMachine)
    (hNoRule : WorkMachineChain.NoRuleAtAccept source) :
    WorkMachineChain.NoRuleAtAccept (mirrorMachine source) := by
  intro selected hMem
  change selected ∈ source.rules.map mirrorRule at hMem
  rcases List.mem_map.mp hMem with ⟨original, hOriginal, hEqual⟩
  subst selected
  exact hNoRule original hOriginal

set_option maxRecDepth 1000000 in
private theorem classifier_noRule : WorkMachineChain.NoRuleAtAccept classifierMachine := by
  apply mirror_noRule
  intro selected hMem
  change selected.sourceState ≠ 20
  change selected ∈ BuilderPostDividerRawRouteClassifier.rules at hMem
  decide +revert

private theorem comparator_noRule : WorkMachineChain.NoRuleAtAccept comparatorMachine := by
  apply mirror_noRule
  intro selected hMem
  exact RawRouter.rule_source_ne_acceptState selected hMem

theorem tail_rules_pairwise_query_distinct :
    tailMachine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct classifierMachine comparatorMachine
    (mirrorRules_pairwise_query_distinct BuilderPostDividerRawRouteClassifier.machine
      BuilderPostDividerRawRouteClassifier.rules_pairwise_query_distinct)
    (mirrorRules_pairwise_query_distinct RawRouter.machine RawRouter.rules_pairwise_query_distinct)
    classifier_noRule

theorem tail_noRuleAtAccept : WorkMachineChain.NoRuleAtAccept tailMachine :=
  WorkMachineChain.noRuleAtAccept classifierMachine comparatorMachine comparator_noRule

theorem tail_acceptState_ne_rejectState : tailMachine.acceptState ≠ tailMachine.rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (mirrorMachine_acceptState_ne_rejectState RawRouter.machine RawRouter.machine_acceptState_ne_rejectState)

/-- The original divider output is the literal classifier input, not a supplied premise. -/
theorem divider_classifier_handoff {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (BuilderDividerSourceExecution.finalConfiguration problem index remaining output).tape =
      (tailInitial ((index / width problem) * width problem) (index % width problem)
        (width problem) (index / width problem) (count problem)
        (preservedWorkspace problem index remaining output)).tape := by
  rw [BuilderDividerSourceExecution.final_tape_layout]
  simp only [tailInitial, workStartConfiguration, mirrorTape,
    BuilderPhysicalClassifierFinishWorkspaceOrientation.mirrorTape,
    BuilderPostDividerRawRouteClassifier.inputTape,
    BuilderPostDividerRawRouteClassifier.terminalPrefix, BuilderPostDividerRawRouteClassifier.sidecar,
    List.nil_append, List.append_assoc, List.cons_append]
  rfl

def machine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderDividerSourceExecution.machine verifier) tailMachine

def initialConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  workStartConfiguration (machine problem.verifier)
    (BuilderCursorSource.cursorTape problem index remaining output)

def finalConfiguration {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (tailFinal ((index / width problem) * width problem) (index % width problem)
      (width problem) (index / width problem) (count problem)
      (preservedWorkspace problem index remaining output))

def workSteps {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) : Nat :=
  BuilderDividerSourceExecution.workSteps problem index remaining + 1 +
    tailSteps ((index / width problem) * width problem) (index % width problem)
      (width problem) (index / width problem) (count problem)

theorem workRunExact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    workRunExact? (machine problem.verifier) (workSteps problem index remaining)
        (initialConfiguration problem index remaining output) =
      some (finalConfiguration problem index remaining output) := by
  have hTail := tail_workRunExact ((index / width problem) * width problem) (index % width problem)
    (width problem) (index / width problem) (count problem) (preservedWorkspace problem index remaining output)
  have hTailInitial : tailInitial ((index / width problem) * width problem) (index % width problem)
      (width problem) (index / width problem) (count problem) (preservedWorkspace problem index remaining output) =
      {
        state := tailMachine.startState
        tape := (BuilderDividerSourceExecution.finalConfiguration problem index remaining output).tape
      } :=
    configuration_eq_of_fields _ _ _ rfl (divider_classifier_handoff problem index remaining output).symm
  rw [hTailInitial] at hTail
  exact WorkMachineChain.workRunExact (BuilderDividerSourceExecution.machine problem.verifier) tailMachine
    (BuilderDividerSourceExecution.workSteps problem index remaining)
    (tailSteps ((index / width problem) * width problem) (index % width problem)
      (width problem) (index / width problem) (count problem)) _ _ _
    (BuilderDividerSourceExecution.workRunExact problem index remaining output) rfl hTail

theorem run_compile_exact {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    run (compileWorkMachine (machine problem.verifier)) (6 * workSteps problem index remaining)
        (encodeWorkConfiguration (initialConfiguration problem index remaining output)) =
      encodeWorkConfiguration (finalConfiguration problem index remaining output) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact problem index remaining output)

theorem finalConfiguration_state {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).state =
      WorkMachineChain.secondState (WorkMachineChain.secondState
        (RawRouter.finalConfiguration (index / width problem) (count problem)).state) := rfl

/-- The comparator touches neither the divider ledger nor the source workspace behind it. -/
theorem final_workspace_preserved {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) :
    (finalConfiguration problem index remaining output).tape.right =
      (RawRouter.finalConfiguration (index / width problem) (count problem)).tape.left ++
        tailExterior ((index / width problem) * width problem) (index % width problem)
          (width problem) (count problem) (preservedWorkspace problem index remaining output) := rfl

theorem rules_pairwise_query_distinct {language : Language} (verifier : PolynomialTimeVerifier language) :
    (machine verifier).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct (BuilderDividerSourceExecution.machine verifier) tailMachine
    (BuilderDividerSourceExecution.rules_pairwise_query_distinct verifier)
    tail_rules_pairwise_query_distinct (BuilderDividerSourceExecution.noRuleAtAccept verifier)

theorem noRuleAtAccept {language : Language} (verifier : PolynomialTimeVerifier language) :
    WorkMachineChain.NoRuleAtAccept (machine verifier) :=
  WorkMachineChain.noRuleAtAccept (BuilderDividerSourceExecution.machine verifier) tailMachine tail_noRuleAtAccept

theorem machine_acceptState_ne_rejectState {language : Language}
    (verifier : PolynomialTimeVerifier language) :
    (machine verifier).acceptState ≠ (machine verifier).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ tail_acceptState_ne_rejectState

/-- Finish is the comparator's non-body endpoint; out-of-range is never given Finish credit. -/
def RouteAgreement {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken) : Prop :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index with
  | .body clauseCoordinate tokenCoordinate =>
      index / width problem = clauseCoordinate.val ∧
      index % width problem = tokenCoordinate.val ∧
      (finalConfiguration problem index remaining output).state = (machine problem.verifier).acceptState
  | .finish =>
      index / width problem = count problem ∧ index % width problem = 0 ∧
      (finalConfiguration problem index remaining output).state = (machine problem.verifier).rejectState
  | .outOfRange => False

theorem routeAgreement {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat) (output : List CNFToken)
    (hIndex : index < BuilderFullScheduleCursorController.bodySlotCount problem) :
    RouteAgreement problem index remaining output := by
  let slot : Fin (BuilderFullScheduleCursorController.bodySlotCount problem) := ⟨index, hIndex⟩
  have hOuter := BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate_outerRoute problem slot
  have hInRange := BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_in_range problem
    (BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate problem slot) index hOuter
  have hDecoded := BuilderPostDividerRawRouteClassifier.decodedRouteHolds_of_not_outOfRange
    problem index hInRange
  have hState := finalConfiguration_state problem index remaining output
  have hCount : count problem = problem.formulaClauseSlotCount := rfl
  have hWidth : width problem = problem.formulaTokensPerClause := rfl
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index with
  | body clauseCoordinate tokenCoordinate =>
    have hBody : index / width problem = clauseCoordinate.val ∧
        index % width problem = tokenCoordinate.val ∧
        (RawRouter.finalConfiguration (index / width problem) (count problem)).state =
          RawRouter.machine.acceptState := by
      simpa only [hCount, hWidth, BuilderPostDividerRawRouteClassifier.DecodedRouteHolds, hRoute] using hDecoded
    unfold RouteAgreement
    rw [hRoute]
    refine ⟨hBody.1, hBody.2.1, ?_⟩
    rw [hState]
    exact congrArg (fun state => WorkMachineChain.secondState (WorkMachineChain.secondState state)) hBody.2.2
  | finish =>
    have hFinish : index / width problem = count problem ∧ index % width problem = 0 ∧
        RawRouter.compareResult 0 (index / width problem) (count problem) = .equal (count problem) ∧
        (RawRouter.finalConfiguration (index / width problem) (count problem)).state =
          RawRouter.machine.rejectState := by
      simpa only [hCount, hWidth, BuilderPostDividerRawRouteClassifier.DecodedRouteHolds, hRoute] using hDecoded
    unfold RouteAgreement
    rw [hRoute]
    refine ⟨hFinish.1, hFinish.2.1, ?_⟩
    rw [hState]
    exact congrArg (fun state => WorkMachineChain.secondState (WorkMachineChain.secondState state)) hFinish.2.2.2
  | outOfRange =>
    simp only [BuilderPostDividerRawRouteClassifier.DecodedRouteHolds, hRoute] at hDecoded

/-- Division, count copying, comparison and both new bridges are all charged. -/
def rawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let span := BuilderDividerSourceExecution.sourceSpan verifier
  let size := NatPolynomial.add (.mul (.constant 4) span) (.constant 2)
  let successor := NatPolynomial.add span (.constant 1)
  let overhead := NatPolynomial.add
    (.add (.mul (.mul (.constant 20) size) size)
      (.mul (.mul (.constant 6) successor) successor)) (.constant 2)
  .add (BuilderDividerSourceExecution.rawTimeBound verifier) (.mul (.constant 6) overhead)

theorem rawTimeBound_le {language : Language} (problem : VerifierTableauProblem language)
    (index remaining : Nat)
    (hBalance : index + remaining = BuilderFullScheduleCursorController.bodySlotCount problem) :
    6 * workSteps problem index remaining ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  let span := (BuilderDividerSourceExecution.sourceSpan problem.verifier).eval problem.input.length
  let quotient := index / width problem
  have hCount : count problem ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .clauseCount index remaining hBalance
  have hIndex : index ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .index index remaining hBalance
  have hWidth : width problem ≤ span :=
    BuilderDividerSourceExecution.operand_le_sourceSpan problem .tokenWidth index remaining hBalance
  have hQuotient : quotient ≤ span := Nat.le_trans (Nat.div_le_self index (width problem)) hIndex
  have hReconstruct := BuilderDividerSourceExecution.quotient_remainder_reconstruct problem index
  have hSize : BuilderPostDividerRawRouteClassifier.bridgeSize (quotient * width problem)
      (index % width problem) (width problem) quotient (count problem) [] ≤ 4 * span + 2 := by
    unfold BuilderPostDividerRawRouteClassifier.bridgeSize BuilderPostDividerRawRouteClassifier.terminalLength
    simp only [List.length_nil]
    change quotient * width problem + index % width problem = index at hReconstruct
    omega
  have hBridge := Nat.le_trans
    (BuilderPostDividerRawRouteClassifier.workSteps_le_quadratic (quotient * width problem)
      (index % width problem) (width problem) quotient (count problem) [])
    (Nat.mul_le_mul (Nat.mul_le_mul_left 20 hSize) hSize)
  have hSuccessor : quotient + 1 ≤ span + 1 := by omega
  have hCompare := Nat.le_trans (RawRouter.workSteps_le quotient (count problem))
    (Nat.mul_le_mul (Nat.mul_le_mul_left 6 hSuccessor) hSuccessor)
  have hSource := BuilderDividerSourceExecution.rawTimeBound_le problem index remaining hBalance
  change 6 * workSteps problem index remaining ≤
    (BuilderDividerSourceExecution.rawTimeBound problem.verifier).eval problem.input.length +
      6 * (20 * (4 * span + 2) * (4 * span + 2) + 6 * (span + 1) * (span + 1) + 2)
  unfold workSteps tailSteps
  change BuilderPostDividerRawRouteClassifier.workSteps ((index / width problem) * width problem)
      (index % width problem) (width problem) (index / width problem) (count problem) [] ≤
      20 * (4 * span + 2) * (4 * span + 2) at hBridge
  change RawRouter.workSteps (index / width problem) (count problem) ≤
    6 * (span + 1) * (span + 1) at hCompare
  omega

def fromRawMachine {language : Language} (verifier : PolynomialTimeVerifier language) : WorkMachine :=
  WorkMachineChain.machine (BuilderInitialization.machine verifier) (machine verifier)

def fromRawInitial {language : Language} (problem : VerifierTableauProblem language) : WorkConfiguration :=
  workStartConfiguration (fromRawMachine problem.verifier) (rawInputWorkTape problem.input)

def fromRawFinal {language : Language} (problem : VerifierTableauProblem language) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (finalConfiguration problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
      (encodeUnaryTokens problem.FormulaWidth))

def fromRawSteps {language : Language} (problem : VerifierTableauProblem language) : Nat :=
  BuilderInitialization.workSteps problem + 1 +
    workSteps problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)

theorem fromRaw_workRunExact {language : Language} (problem : VerifierTableauProblem language) :
    workRunExact? (fromRawMachine problem.verifier) (fromRawSteps problem)
        (fromRawInitial problem) = some (fromRawFinal problem) := by
  have hInit := BuilderInitialization.workRunExact problem
  have hInitFinal : BuilderInitialization.finalConfiguration problem =
      {
        state := (BuilderInitialization.machine problem.verifier).acceptState
        tape := BuilderCursorSource.cursorTape problem 0
          (BuilderFullScheduleCursorController.bodySlotCount problem)
          (encodeUnaryTokens problem.FormulaWidth)
      } :=
    configuration_eq_of_fields _ _ _
      (BuilderInitialization.finalConfiguration_state problem)
      (BuilderCursorSource.initializer_tape_handoff problem)
  rw [hInitFinal] at hInit
  exact WorkMachineChain.workRunExact (BuilderInitialization.machine problem.verifier) (machine problem.verifier)
    (BuilderInitialization.workSteps problem)
    (workSteps problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)) _ _ _ hInit rfl
    (workRunExact problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
      (encodeUnaryTokens problem.FormulaWidth))

theorem fromRaw_run_compile_exact {language : Language} (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (fromRawMachine problem.verifier)) (6 * fromRawSteps problem)
        (encodeWorkConfiguration (fromRawInitial problem)) =
      encodeWorkConfiguration (fromRawFinal problem) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (fromRaw_workRunExact problem)

def fromRawTimeBound {language : Language} (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (.add (BuilderInitialization.rawTimeBound verifier) (.constant 6)) (rawTimeBound verifier)

theorem fromRawTimeBound_le {language : Language} (problem : VerifierTableauProblem language) :
    6 * fromRawSteps problem ≤ (fromRawTimeBound problem.verifier).eval problem.input.length := by
  have hInit := BuilderInitialization.rawTimeBound_le problem
  have hClassifier := rawTimeBound_le problem 0
    (BuilderFullScheduleCursorController.bodySlotCount problem) (Nat.zero_add _)
  simp only [fromRawTimeBound, NatPolynomial.eval_add, NatPolynomial.eval_constant]
  unfold fromRawSteps
  omega

/-- Source initialization starts at the real first body/Finish opportunity. -/
theorem fromRaw_routeAgreement {language : Language} (problem : VerifierTableauProblem language) :
    match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem 0 with
    | .body _ _ => (fromRawFinal problem).state = (fromRawMachine problem.verifier).acceptState
    | .finish => (fromRawFinal problem).state = (fromRawMachine problem.verifier).rejectState
    | .outOfRange => False := by
  have hAgreement := routeAgreement problem 0 (BuilderFullScheduleCursorController.bodySlotCount problem)
    (encodeUnaryTokens problem.FormulaWidth) (BuilderFullScheduleCursorController.bodySlotCount_positive problem)
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem 0 with
  | body clauseCoordinate tokenCoordinate =>
    simp only [RouteAgreement, hRoute] at hAgreement
    exact congrArg WorkMachineChain.secondState hAgreement.2.2
  | finish =>
    simp only [RouteAgreement, hRoute] at hAgreement
    exact congrArg WorkMachineChain.secondState hAgreement.2.2
  | outOfRange =>
    simp only [RouteAgreement, hRoute] at hAgreement

end PNP.Concrete.CookLevin.BuilderSourceClassifier
