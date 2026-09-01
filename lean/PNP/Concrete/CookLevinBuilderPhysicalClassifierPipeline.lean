/-
Copyright (c) 2026 PNP Labs.

One fixed physical pipeline from M213's post-header tape bridge through the
raw divider and M214's body-versus-Finish classifier.

The construction ranges over every canonical post-header coordinate and
arbitrary builder workspace. It does not yet derive a padding or token request,
run the optional-token dispatcher, iterate one literal schedule loop, establish
builder RawRefinement, or package the Cook--Levin reduction.
-/

import PNP.Concrete.CookLevinBuilderPhysicalFinishRequest
import PNP.Concrete.WorkMachineChain

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPhysicalClassifierPipeline

open PipelineStateNamespace
open BuilderPostDividerSelectedTokenLaunch

abbrev bridgeMachine : WorkMachine :=
  BuilderPostHeaderRawTapeBridge.machine
abbrev dividerMachine : WorkMachine :=
  BuilderPostHeaderRawTapeBridge.dividerMachine
abbrev classifierBridgeMachine : WorkMachine :=
  BuilderPostDividerRawRouteClassifier.machine
abbrev comparatorMachine : WorkMachine :=
  BuilderPostDividerRawRouteClassifier.comparatorMachine

def bridgeDividerMachine : WorkMachine :=
  WorkMachineChain.machine bridgeMachine dividerMachine

def bridgeDividerClassifierMachine : WorkMachine :=
  WorkMachineChain.machine bridgeDividerMachine classifierBridgeMachine

/-- One fixed machine containing M213's bridge, M211's divider, M214's
post-divider bridge and M214's shielded comparator. -/
def machine : WorkMachine :=
  WorkMachineChain.machine bridgeDividerClassifierMachine comparatorMachine

set_option maxRecDepth 1000000 in
theorem rules_length : machine.rules.length = 711 := by
  rfl

set_option maxRecDepth 1000000 in
private theorem bridge_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept bridgeMachine := by
  intro rule hRule
  change rule.sourceState ≠ 39
  change rule ∈ BuilderPostHeaderRawTapeBridge.rules at hRule
  decide +revert

private theorem divider_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept dividerMachine := by
  intro rule hRule
  exact BuilderPostHeaderRawDivider.rule_source_ne_acceptState rule hRule

set_option maxRecDepth 1000000 in
private theorem classifier_noRuleAtAccept :
    WorkMachineChain.NoRuleAtAccept classifierBridgeMachine := by
  intro rule hRule
  change rule.sourceState ≠ 20
  change rule ∈ BuilderPostDividerRawRouteClassifier.rules at hRule
  decide +revert

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  have hBridgeDivider :
      bridgeDividerMachine.rules.Pairwise WorkMachineChain.QueryDistinct := by
    exact WorkMachineChain.rules_pairwise_query_distinct
      bridgeMachine dividerMachine
      BuilderPostHeaderRawTapeBridge.rules_pairwise_query_distinct
      BuilderPostHeaderRawDivider.rules_pairwise_query_distinct
      bridge_noRuleAtAccept
  have hBridgeDividerNoRule :
      WorkMachineChain.NoRuleAtAccept bridgeDividerMachine := by
    exact WorkMachineChain.noRuleAtAccept bridgeMachine dividerMachine
      divider_noRuleAtAccept
  have hBridgeDividerClassifier :
      bridgeDividerClassifierMachine.rules.Pairwise
        WorkMachineChain.QueryDistinct := by
    exact WorkMachineChain.rules_pairwise_query_distinct
      bridgeDividerMachine classifierBridgeMachine
      hBridgeDivider
      BuilderPostDividerRawRouteClassifier.rules_pairwise_query_distinct
      hBridgeDividerNoRule
  have hBridgeDividerClassifierNoRule :
      WorkMachineChain.NoRuleAtAccept bridgeDividerClassifierMachine := by
    exact WorkMachineChain.noRuleAtAccept bridgeDividerMachine
      classifierBridgeMachine classifier_noRuleAtAccept
  exact WorkMachineChain.rules_pairwise_query_distinct
    bridgeDividerClassifierMachine comparatorMachine
    hBridgeDividerClassifier
    BuilderArbitrarySlotHeaderRouter.RawRouter.rules_pairwise_query_distinct
    hBridgeDividerClassifierNoRule

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  decide

def firstBodySlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFullScheduleCursorController.firstBodySlot problem

def width {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.formulaTokensPerClause

def clauseCount {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.formulaClauseSlotCount

def protectedWorkspace {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.sidecar
    (clauseCount problem) workspace

/-! ## Equal outer-router branch -/

def equalBridgeInitialConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostHeaderRawTapeBridge.equalInputConfiguration
    (firstBodySlot problem) (width problem)
    (protectedWorkspace problem workspace)

def equalBridgeFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostHeaderRawTapeBridge.equalFinalConfiguration
    (firstBodySlot problem) (width problem)
    (protectedWorkspace problem workspace)

def equalDividerFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
    0 (width problem)
    (BuilderPostHeaderRawTapeBridge.equalExterior
      (firstBodySlot problem) (width problem)
      (protectedWorkspace problem workspace))

def equalClassifierInitialConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostDividerRawRouteClassifier.inputConfiguration
    0 0 (width problem) 0
    (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix
      (firstBodySlot problem) (width problem))
    (clauseCount problem) workspace

def equalClassifierExterior {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.preservedExterior
    0 0 (width problem)
    (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix
      (firstBodySlot problem) (width problem))
    (clauseCount problem) workspace

def equalClassifierFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostDividerRawRouteClassifier.comparatorInputConfiguration
    0 (clauseCount problem) (equalClassifierExterior problem workspace)

def equalComparatorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration
    0 (clauseCount problem) (equalClassifierExterior problem workspace)

def equalEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (renameConfiguration WorkMachineChain.firstState
      (renameConfiguration WorkMachineChain.firstState
        (equalBridgeInitialConfiguration problem workspace)))

def equalFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (equalComparatorFinalConfiguration problem workspace)

def equalWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  ((BuilderPostHeaderRawTapeBridge.equalWorkSteps (width problem) + 1 +
      BuilderPostHeaderRawDivider.workSteps 0 (width problem)) + 1 +
    BuilderPostDividerRawRouteClassifier.workSteps
      0 0 (width problem) 0 (clauseCount problem)
      (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix
        (firstBodySlot problem) (width problem))) + 1 +
    BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
      0 (clauseCount problem)

theorem equal_stage_handoffs {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    BuilderPostHeaderRawTapeBridge.equalInputTape
        (firstBodySlot problem) (width problem)
        (protectedWorkspace problem workspace) =
      BuilderPostHeaderRawTapeBridge.extendRouterResultTape
        (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
          (.equal (firstBodySlot problem))).tape
        (width problem) (protectedWorkspace problem workspace) ∧
    (equalBridgeFinalConfiguration problem workspace).tape =
      (BuilderPostHeaderRawTapeBridge.shieldedDividerStartConfiguration
        0 (width problem)
        (BuilderPostHeaderRawTapeBridge.equalExterior
          (firstBodySlot problem) (width problem)
          (protectedWorkspace problem workspace))).tape ∧
    (equalClassifierInitialConfiguration problem workspace).tape =
      (equalDividerFinalConfiguration problem workspace).tape ∧
    (equalClassifierFinalConfiguration problem workspace).tape =
      (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
        0 (clauseCount problem)
        (equalClassifierExterior problem workspace)).tape := by
  exact And.intro
    (BuilderPostHeaderRawTapeBridge.equalInputTape_is_exact_router_result
      (firstBodySlot problem) (width problem)
      (protectedWorkspace problem workspace))
    (And.intro
      (BuilderPostHeaderRawTapeBridge.equalFinal_tape_is_shieldedDivider_start
        (firstBodySlot problem) (width problem)
        (protectedWorkspace problem workspace))
      (And.intro
        (BuilderPostDividerRawRouteClassifier.equal_input_tape_is_exact_m213_final
          (firstBodySlot problem) (width problem) (clauseCount problem)
          workspace)
        rfl))

theorem equal_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    workRunExact? machine (equalWorkSteps problem)
        (equalEntryConfiguration problem workspace) =
      some (equalFinalConfiguration problem workspace) := by
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  have hBridge := BuilderPostHeaderRawTapeBridge.equal_workRunExact
    (firstBodySlot problem) (width problem)
    (protectedWorkspace problem workspace) hWidth
  have hDivider :
      workRunExact? dividerMachine
          (BuilderPostHeaderRawDivider.workSteps 0 (width problem))
          { state := dividerMachine.startState
            tape := (equalBridgeFinalConfiguration problem workspace).tape } =
        some (equalDividerFinalConfiguration problem workspace) := by
    have hTape :=
      BuilderPostHeaderRawTapeBridge.equalFinal_tape_is_shieldedDivider_start
        (firstBodySlot problem) (width problem)
        (protectedWorkspace problem workspace)
    unfold equalBridgeFinalConfiguration
    rw [hTape]
    change workRunExact? dividerMachine
        (BuilderPostHeaderRawDivider.workSteps 0 (width problem))
        (BuilderPostHeaderRawTapeBridge.shieldedDividerStartConfiguration
          0 (width problem)
          (BuilderPostHeaderRawTapeBridge.equalExterior
            (firstBodySlot problem) (width problem)
            (protectedWorkspace problem workspace))) = _
    exact BuilderPostHeaderRawTapeBridge.shielded_divider_workRunExact
      0 (width problem)
      (BuilderPostHeaderRawTapeBridge.equalExterior
        (firstBodySlot problem) (width problem)
        (protectedWorkspace problem workspace)) hWidth
  have hBridgeDivider := WorkMachineChain.workRunExact
    bridgeMachine dividerMachine
    (BuilderPostHeaderRawTapeBridge.equalWorkSteps (width problem))
    (BuilderPostHeaderRawDivider.workSteps 0 (width problem))
    (equalBridgeInitialConfiguration problem workspace)
    (equalBridgeFinalConfiguration problem workspace)
    (equalDividerFinalConfiguration problem workspace)
    (by simpa [bridgeMachine, equalBridgeInitialConfiguration,
      equalBridgeFinalConfiguration] using hBridge)
    (by rfl) hDivider
  have hClassifier :
      workRunExact? classifierBridgeMachine
          (BuilderPostDividerRawRouteClassifier.workSteps
            0 0 (width problem) 0 (clauseCount problem)
            (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix
              (firstBodySlot problem) (width problem)))
          { state := classifierBridgeMachine.startState
            tape := (renameConfiguration WorkMachineChain.secondState
              (equalDividerFinalConfiguration problem workspace)).tape } =
        some (equalClassifierFinalConfiguration problem workspace) := by
    have hTape :=
      BuilderPostDividerRawRouteClassifier.equal_input_tape_is_exact_m213_final
        (firstBodySlot problem) (width problem) (clauseCount problem)
        workspace
    simp only [renameConfiguration]
    unfold equalDividerFinalConfiguration protectedWorkspace
    rw [← hTape]
    simpa [classifierBridgeMachine, equalClassifierInitialConfiguration,
      equalClassifierFinalConfiguration, equalClassifierExterior,
      BuilderPostDividerRawRouteClassifier.inputConfiguration,
      BuilderPostDividerRawRouteClassifier.machine] using
      (BuilderPostDividerRawRouteClassifier.workRunExact
        0 0 (width problem) 0 (clauseCount problem)
        (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix
          (firstBodySlot problem) (width problem)) workspace
        (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix_safe
          (firstBodySlot problem) (width problem)))
  have hBridgeDividerClassifier := WorkMachineChain.workRunExact
    bridgeDividerMachine classifierBridgeMachine
    (BuilderPostHeaderRawTapeBridge.equalWorkSteps (width problem) + 1 +
      BuilderPostHeaderRawDivider.workSteps 0 (width problem))
    (BuilderPostDividerRawRouteClassifier.workSteps
      0 0 (width problem) 0 (clauseCount problem)
      (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix
        (firstBodySlot problem) (width problem)))
    (renameConfiguration WorkMachineChain.firstState
      (equalBridgeInitialConfiguration problem workspace))
    (renameConfiguration WorkMachineChain.secondState
      (equalDividerFinalConfiguration problem workspace))
    (equalClassifierFinalConfiguration problem workspace)
    (by simpa [bridgeDividerMachine] using hBridgeDivider)
    (by rfl) hClassifier
  have hComparator :
      workRunExact? comparatorMachine
          (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
            0 (clauseCount problem))
          { state := comparatorMachine.startState
            tape := (renameConfiguration WorkMachineChain.secondState
              (equalClassifierFinalConfiguration problem workspace)).tape } =
        some (equalComparatorFinalConfiguration problem workspace) := by
    change workRunExact? comparatorMachine
        (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps 0 (clauseCount problem))
        (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
          0 (clauseCount problem) (equalClassifierExterior problem workspace)) = _
    exact BuilderPostDividerRawRouteClassifier.shielded_comparator_workRunExact
      0 (clauseCount problem) (equalClassifierExterior problem workspace)
  have hAll := WorkMachineChain.workRunExact
    bridgeDividerClassifierMachine comparatorMachine
    ((BuilderPostHeaderRawTapeBridge.equalWorkSteps (width problem) + 1 +
      BuilderPostHeaderRawDivider.workSteps 0 (width problem)) + 1 +
      BuilderPostDividerRawRouteClassifier.workSteps
        0 0 (width problem) 0 (clauseCount problem)
        (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix
          (firstBodySlot problem) (width problem)))
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
      0 (clauseCount problem))
    (renameConfiguration WorkMachineChain.firstState
      (renameConfiguration WorkMachineChain.firstState
        (equalBridgeInitialConfiguration problem workspace)))
    (renameConfiguration WorkMachineChain.secondState
      (equalClassifierFinalConfiguration problem workspace))
    (equalComparatorFinalConfiguration problem workspace)
    (by simpa [bridgeDividerClassifierMachine] using
      hBridgeDividerClassifier)
    (by rfl) hComparator
  simpa [machine, equalWorkSteps, equalEntryConfiguration,
    equalFinalConfiguration, Nat.add_assoc] using hAll

/-! ## Greater outer-router branch -/

def greaterBridgeInitialConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostHeaderRawTapeBridge.greaterInputConfiguration
    (firstBodySlot problem) remaining (width problem)
    (protectedWorkspace problem workspace)

def greaterBridgeFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostHeaderRawTapeBridge.greaterFinalConfiguration
    (firstBodySlot problem) remaining (width problem)
    (protectedWorkspace problem workspace)

def greaterDividerFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
    (remaining + 1) (width problem)
    (BuilderPostHeaderRawTapeBridge.greaterExterior
      (firstBodySlot problem) remaining (width problem)
      (protectedWorkspace problem workspace))

def greaterConsumed {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat) : Nat :=
  ((remaining + 1) / width problem) * width problem

def greaterRemainder {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat) : Nat :=
  (remaining + 1) % width problem

def greaterQuotient {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat) : Nat :=
  (remaining + 1) / width problem

def greaterClassifierInitialConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostDividerRawRouteClassifier.inputConfiguration
    (greaterConsumed problem remaining) (greaterRemainder problem remaining)
    (width problem) (greaterQuotient problem remaining)
    (BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix
      (firstBodySlot problem) remaining (width problem))
    (clauseCount problem) workspace

def greaterClassifierExterior {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.preservedExterior
    (greaterConsumed problem remaining) (greaterRemainder problem remaining)
    (width problem) (BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix
      (firstBodySlot problem) remaining (width problem))
    (clauseCount problem) workspace

def greaterClassifierFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostDividerRawRouteClassifier.comparatorInputConfiguration
    (greaterQuotient problem remaining) (clauseCount problem)
    (greaterClassifierExterior problem remaining workspace)

def greaterComparatorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration
    (greaterQuotient problem remaining) (clauseCount problem)
    (greaterClassifierExterior problem remaining workspace)

def greaterEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.firstState
    (renameConfiguration WorkMachineChain.firstState
      (renameConfiguration WorkMachineChain.firstState
        (greaterBridgeInitialConfiguration problem remaining workspace)))

def greaterFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (greaterComparatorFinalConfiguration problem remaining workspace)

def greaterWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat) : Nat :=
  ((BuilderPostHeaderRawTapeBridge.greaterWorkSteps
      (firstBodySlot problem) remaining (width problem) + 1 +
      BuilderPostHeaderRawDivider.workSteps (remaining + 1)
        (width problem)) + 1 +
    BuilderPostDividerRawRouteClassifier.workSteps
      (greaterConsumed problem remaining) (greaterRemainder problem remaining)
      (width problem) (greaterQuotient problem remaining)
      (clauseCount problem)
      (BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix
        (firstBodySlot problem) remaining (width problem))) + 1 +
    BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
      (greaterQuotient problem remaining) (clauseCount problem)

theorem greater_stage_handoffs {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) :
    BuilderPostHeaderRawTapeBridge.greaterInputTape
        (firstBodySlot problem) remaining (width problem)
        (protectedWorkspace problem workspace) =
      BuilderPostHeaderRawTapeBridge.extendRouterResultTape
        (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
          (.greater (firstBodySlot problem) remaining)).tape
        (width problem) (protectedWorkspace problem workspace) ∧
    (greaterBridgeFinalConfiguration problem remaining workspace).tape =
      (BuilderPostHeaderRawTapeBridge.shieldedDividerStartConfiguration
        (remaining + 1) (width problem)
        (BuilderPostHeaderRawTapeBridge.greaterExterior
          (firstBodySlot problem) remaining (width problem)
          (protectedWorkspace problem workspace))).tape ∧
    (greaterClassifierInitialConfiguration problem remaining workspace).tape =
      (greaterDividerFinalConfiguration problem remaining workspace).tape ∧
    (greaterClassifierFinalConfiguration problem remaining workspace).tape =
      (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
        (greaterQuotient problem remaining) (clauseCount problem)
        (greaterClassifierExterior problem remaining workspace)).tape := by
  exact And.intro
    (BuilderPostHeaderRawTapeBridge.greaterInputTape_is_exact_router_result
      (firstBodySlot problem) remaining (width problem)
      (protectedWorkspace problem workspace))
    (And.intro
      (BuilderPostHeaderRawTapeBridge.greaterFinal_tape_is_shieldedDivider_start
        (firstBodySlot problem) remaining (width problem)
        (protectedWorkspace problem workspace))
      (And.intro
        (BuilderPostDividerRawRouteClassifier.greater_input_tape_is_exact_m213_final
          (firstBodySlot problem) remaining (width problem)
          (clauseCount problem) workspace)
        rfl))

theorem greater_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) (remaining : Nat)
    (workspace : List WorkSymbol) :
    workRunExact? machine (greaterWorkSteps problem remaining)
        (greaterEntryConfiguration problem remaining workspace) =
      some (greaterFinalConfiguration problem remaining workspace) := by
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  have hBridge := BuilderPostHeaderRawTapeBridge.greater_workRunExact
    (firstBodySlot problem) remaining (width problem)
    (protectedWorkspace problem workspace) hWidth
  have hDivider :
      workRunExact? dividerMachine
          (BuilderPostHeaderRawDivider.workSteps (remaining + 1)
            (width problem))
          { state := dividerMachine.startState
            tape := (greaterBridgeFinalConfiguration problem remaining
              workspace).tape } =
        some (greaterDividerFinalConfiguration problem remaining workspace) := by
    have hTape :=
      BuilderPostHeaderRawTapeBridge.greaterFinal_tape_is_shieldedDivider_start
        (firstBodySlot problem) remaining (width problem)
        (protectedWorkspace problem workspace)
    unfold greaterBridgeFinalConfiguration
    rw [hTape]
    change workRunExact? dividerMachine
        (BuilderPostHeaderRawDivider.workSteps (remaining + 1) (width problem))
        (BuilderPostHeaderRawTapeBridge.shieldedDividerStartConfiguration
          (remaining + 1) (width problem)
          (BuilderPostHeaderRawTapeBridge.greaterExterior
            (firstBodySlot problem) remaining (width problem)
            (protectedWorkspace problem workspace))) = _
    exact BuilderPostHeaderRawTapeBridge.shielded_divider_workRunExact
      (remaining + 1) (width problem)
      (BuilderPostHeaderRawTapeBridge.greaterExterior
        (firstBodySlot problem) remaining (width problem)
        (protectedWorkspace problem workspace)) hWidth
  have hBridgeDivider := WorkMachineChain.workRunExact
    bridgeMachine dividerMachine
    (BuilderPostHeaderRawTapeBridge.greaterWorkSteps
      (firstBodySlot problem) remaining (width problem))
    (BuilderPostHeaderRawDivider.workSteps (remaining + 1) (width problem))
    (greaterBridgeInitialConfiguration problem remaining workspace)
    (greaterBridgeFinalConfiguration problem remaining workspace)
    (greaterDividerFinalConfiguration problem remaining workspace)
    (by simpa [bridgeMachine, greaterBridgeInitialConfiguration,
      greaterBridgeFinalConfiguration] using hBridge)
    (by rfl) hDivider
  have hClassifier :
      workRunExact? classifierBridgeMachine
          (BuilderPostDividerRawRouteClassifier.workSteps
            (greaterConsumed problem remaining)
            (greaterRemainder problem remaining) (width problem)
            (greaterQuotient problem remaining) (clauseCount problem)
            (BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix
              (firstBodySlot problem) remaining (width problem)))
          { state := classifierBridgeMachine.startState
            tape := (renameConfiguration WorkMachineChain.secondState
              (greaterDividerFinalConfiguration problem remaining
                workspace)).tape } =
        some (greaterClassifierFinalConfiguration problem remaining
          workspace) := by
    have hTape :=
      BuilderPostDividerRawRouteClassifier.greater_input_tape_is_exact_m213_final
        (firstBodySlot problem) remaining (width problem)
        (clauseCount problem) workspace
    simp only [renameConfiguration]
    unfold greaterDividerFinalConfiguration protectedWorkspace
    rw [← hTape]
    simpa [classifierBridgeMachine, greaterClassifierInitialConfiguration,
      greaterClassifierFinalConfiguration, greaterConsumed,
      greaterRemainder, greaterQuotient, greaterClassifierExterior,
      BuilderPostDividerRawRouteClassifier.inputConfiguration,
      BuilderPostDividerRawRouteClassifier.machine] using
      (BuilderPostDividerRawRouteClassifier.workRunExact
        (((remaining + 1) / width problem) * width problem)
        ((remaining + 1) % width problem) (width problem)
        ((remaining + 1) / width problem) (clauseCount problem)
        (BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix
          (firstBodySlot problem) remaining (width problem)) workspace
        (BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix_safe
          (firstBodySlot problem) remaining (width problem)))
  have hBridgeDividerClassifier := WorkMachineChain.workRunExact
    bridgeDividerMachine classifierBridgeMachine
    (BuilderPostHeaderRawTapeBridge.greaterWorkSteps
      (firstBodySlot problem) remaining (width problem) + 1 +
      BuilderPostHeaderRawDivider.workSteps (remaining + 1) (width problem))
    (BuilderPostDividerRawRouteClassifier.workSteps
      (greaterConsumed problem remaining) (greaterRemainder problem remaining)
      (width problem) (greaterQuotient problem remaining)
      (clauseCount problem)
      (BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix
        (firstBodySlot problem) remaining (width problem)))
    (renameConfiguration WorkMachineChain.firstState
      (greaterBridgeInitialConfiguration problem remaining workspace))
    (renameConfiguration WorkMachineChain.secondState
      (greaterDividerFinalConfiguration problem remaining workspace))
    (greaterClassifierFinalConfiguration problem remaining workspace)
    (by simpa [bridgeDividerMachine] using hBridgeDivider)
    (by rfl) hClassifier
  have hComparator :
      workRunExact? comparatorMachine
          (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
            (greaterQuotient problem remaining) (clauseCount problem))
          { state := comparatorMachine.startState
            tape := (renameConfiguration WorkMachineChain.secondState
              (greaterClassifierFinalConfiguration problem remaining
                workspace)).tape } =
        some (greaterComparatorFinalConfiguration problem remaining
          workspace) := by
    change workRunExact? comparatorMachine
        (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
          (greaterQuotient problem remaining) (clauseCount problem))
        (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
          (greaterQuotient problem remaining) (clauseCount problem)
          (greaterClassifierExterior problem remaining workspace)) = _
    exact BuilderPostDividerRawRouteClassifier.shielded_comparator_workRunExact
      (greaterQuotient problem remaining) (clauseCount problem)
      (greaterClassifierExterior problem remaining workspace)
  have hAll := WorkMachineChain.workRunExact
    bridgeDividerClassifierMachine comparatorMachine
    ((BuilderPostHeaderRawTapeBridge.greaterWorkSteps
      (firstBodySlot problem) remaining (width problem) + 1 +
      BuilderPostHeaderRawDivider.workSteps (remaining + 1)
        (width problem)) + 1 +
      BuilderPostDividerRawRouteClassifier.workSteps
        (greaterConsumed problem remaining)
        (greaterRemainder problem remaining) (width problem)
        (greaterQuotient problem remaining) (clauseCount problem)
        (BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix
          (firstBodySlot problem) remaining (width problem)))
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
      (greaterQuotient problem remaining) (clauseCount problem))
    (renameConfiguration WorkMachineChain.firstState
      (renameConfiguration WorkMachineChain.firstState
        (greaterBridgeInitialConfiguration problem remaining workspace)))
    (renameConfiguration WorkMachineChain.secondState
      (greaterClassifierFinalConfiguration problem remaining workspace))
    (greaterComparatorFinalConfiguration problem remaining workspace)
    (by simpa [bridgeDividerClassifierMachine] using
      hBridgeDividerClassifier)
    (by rfl) hComparator
  simpa [machine, greaterWorkSteps, greaterEntryConfiguration,
    greaterFinalConfiguration, Nat.add_assoc] using hAll

/-! ## Canonical all-coordinate interface -/

def entryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : WorkConfiguration :=
  match index.val with
  | 0 => equalEntryConfiguration problem workspace
  | remaining + 1 => greaterEntryConfiguration problem remaining workspace

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : WorkConfiguration :=
  match index.val with
  | 0 => equalFinalConfiguration problem workspace
  | remaining + 1 => greaterFinalConfiguration problem remaining workspace

def workSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) : Nat :=
  match index.val with
  | 0 => equalWorkSteps problem
  | remaining + 1 => greaterWorkSteps problem remaining

def StageHandoffsHold {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : Prop :=
  match index.val with
  | 0 =>
      BuilderPostHeaderRawTapeBridge.equalInputTape
          (firstBodySlot problem) (width problem)
          (protectedWorkspace problem workspace) =
        BuilderPostHeaderRawTapeBridge.extendRouterResultTape
          (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
            (.equal (firstBodySlot problem))).tape
          (width problem) (protectedWorkspace problem workspace) ∧
      (equalBridgeFinalConfiguration problem workspace).tape =
        (BuilderPostHeaderRawTapeBridge.shieldedDividerStartConfiguration
          0 (width problem)
          (BuilderPostHeaderRawTapeBridge.equalExterior
            (firstBodySlot problem) (width problem)
            (protectedWorkspace problem workspace))).tape ∧
      (equalClassifierInitialConfiguration problem workspace).tape =
        (equalDividerFinalConfiguration problem workspace).tape ∧
      (equalClassifierFinalConfiguration problem workspace).tape =
        (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
          0 (clauseCount problem)
          (equalClassifierExterior problem workspace)).tape
  | remaining + 1 =>
      BuilderPostHeaderRawTapeBridge.greaterInputTape
          (firstBodySlot problem) remaining (width problem)
          (protectedWorkspace problem workspace) =
        BuilderPostHeaderRawTapeBridge.extendRouterResultTape
          (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
            (.greater (firstBodySlot problem) remaining)).tape
          (width problem) (protectedWorkspace problem workspace) ∧
      (greaterBridgeFinalConfiguration problem remaining workspace).tape =
        (BuilderPostHeaderRawTapeBridge.shieldedDividerStartConfiguration
          (remaining + 1) (width problem)
          (BuilderPostHeaderRawTapeBridge.greaterExterior
            (firstBodySlot problem) remaining (width problem)
            (protectedWorkspace problem workspace))).tape ∧
      (greaterClassifierInitialConfiguration problem remaining workspace).tape =
        (greaterDividerFinalConfiguration problem remaining workspace).tape ∧
      (greaterClassifierFinalConfiguration problem remaining workspace).tape =
        (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
          (greaterQuotient problem remaining) (clauseCount problem)
          (greaterClassifierExterior problem remaining workspace)).tape

theorem stageHandoffsHold {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    StageHandoffsHold problem index workspace := by
  cases hIndex : index.val with
  | zero =>
      simpa [StageHandoffsHold, hIndex] using
        (equal_stage_handoffs problem workspace)
  | succ remaining =>
      simpa [StageHandoffsHold, hIndex] using
        (greater_stage_handoffs problem remaining workspace)

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index workspace) =
      some (finalConfiguration problem index workspace) := by
  cases hIndex : index.val with
  | zero =>
      simpa [workSteps, entryConfiguration, finalConfiguration, hIndex] using
        (equal_workRunExact problem workspace)
  | succ remaining =>
      simpa [workSteps, entryConfiguration, finalConfiguration, hIndex] using
        (greater_workRunExact problem remaining workspace)

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index workspace)) =
      encodeWorkConfiguration (finalConfiguration problem index workspace) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps problem index) (entryConfiguration problem index workspace)
    (finalConfiguration problem index workspace)
    (workRunExact problem index workspace)

/-! ## Route agreement, exact timeout boundary, and polynomial bound -/

def comparisonResult {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult :=
  match index.val with
  | 0 => .equal (firstBodySlot problem)
  | remaining + 1 => .greater (firstBodySlot problem) remaining

private theorem compareResult_add_boundary
    (processed boundary offset : Nat) :
    BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult processed
        (boundary + offset) boundary =
      match offset with
      | 0 => .equal (processed + boundary)
      | remaining + 1 => .greater (processed + boundary) remaining := by
  induction boundary generalizing processed with
  | zero =>
      cases offset <;>
        simp [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult]
  | succ boundary ih =>
      have hCoordinate : boundary + 1 + offset = boundary + offset + 1 := by
        omega
      rw [hCoordinate]
      simp only [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult]
      rw [ih (processed + 1)]
      have hProcessed : processed + 1 + boundary =
          processed + (boundary + 1) := by omega
      rw [hProcessed]

theorem comparisonResult_eq_raw_compare {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0
        (BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate problem
          index).val
        (BuilderFullScheduleCursorController.firstBodySlot problem) =
      comparisonResult problem index := by
  have hCompare := compareResult_add_boundary 0 (firstBodySlot problem)
    index.val
  simpa [firstBodySlot, BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate,
    comparisonResult] using hCompare

theorem finalConfiguration_state {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    (finalConfiguration problem index workspace).state =
      WorkMachineChain.secondState
        (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
          (index.val / width problem) (clauseCount problem)).state := by
  cases hIndex : index.val with
  | zero =>
      simp [finalConfiguration, hIndex, equalFinalConfiguration,
        equalComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        renameConfiguration]
  | succ remaining =>
      simp [finalConfiguration, hIndex, greaterFinalConfiguration,
        greaterComparatorFinalConfiguration, greaterQuotient,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        renameConfiguration]

def RouteAgreement {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : Prop :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val with
  | .body _ _ =>
      (finalConfiguration problem index workspace).state = machine.acceptState
  | .finish =>
      (finalConfiguration problem index workspace).state = machine.rejectState
  | .outOfRange => False

theorem routeAgreement {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    RouteAgreement problem index workspace := by
  have hOuter :=
    BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate_outerRoute
      problem index
  have hInRange :=
    BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute_in_range problem
      (BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate problem index)
      index.val hOuter
  have hDecoded :=
    BuilderPostDividerRawRouteClassifier.decodedRouteHolds_of_not_outOfRange
      problem index.val hInRange
  have hState := finalConfiguration_state problem index workspace
  cases hRoute :
      BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      have hBody :
          index.val / width problem = clauseCoordinate.val ∧
          index.val % width problem = tokenCoordinate.val ∧
          (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
            (index.val / width problem) (clauseCount problem)).state =
              comparatorMachine.acceptState := by
        simpa [BuilderPostDividerRawRouteClassifier.DecodedRouteHolds,
          width, clauseCount, hRoute] using hDecoded
      unfold RouteAgreement
      rw [hRoute, hState]
      simpa [machine, WorkMachineChain.machine] using
        congrArg WorkMachineChain.secondState hBody.2.2
  | finish =>
      have hFinish :
          index.val / width problem = clauseCount problem ∧
          index.val % width problem = 0 ∧
          BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0
              (index.val / width problem) (clauseCount problem) =
                .equal (clauseCount problem) ∧
          (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
            (index.val / width problem) (clauseCount problem)).state =
              comparatorMachine.rejectState := by
        simpa [BuilderPostDividerRawRouteClassifier.DecodedRouteHolds,
          width, clauseCount, hRoute] using hDecoded
      unfold RouteAgreement
      rw [hRoute, hState]
      simpa [machine, WorkMachineChain.machine] using
        congrArg WorkMachineChain.secondState hFinish.2.2.2
  | outOfRange =>
      simp only [BuilderPostDividerRawRouteClassifier.DecodedRouteHolds,
        hRoute] at hDecoded

private theorem workRunExact_succ_split_last (selectedMachine : WorkMachine) :
    forall (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? selectedMachine (steps + 1) initial = some final →
      ∃ before,
        workRunExact? selectedMachine steps initial = some before ∧
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
               | some result => workRunExact? selectedMachine (steps + 1) result) =
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

theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    0 < workSteps problem index := by
  cases hIndex : index.val with
  | zero =>
      simp only [workSteps, hIndex]
      unfold equalWorkSteps
      omega
  | succ remaining =>
      simp only [workSteps, hIndex]
      unfold greaterWorkSteps
      omega

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index workspace)) = false := by
  have hPositive := workSteps_positive problem index
  let short := workSteps problem index - 1
  have hSucc : short + 1 = workSteps problem index := by
    dsimp [short]
    omega
  have hExact := workRunExact problem index workspace
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last machine short
      (entryConfiguration problem index workspace)
      (finalConfiguration problem index workspace) hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short
      (entryConfiguration problem index workspace) = before :=
    workRun_eq_of_workRunExact machine short
      (entryConfiguration problem index workspace) before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine before
    (finalConfiguration problem index workspace) hLast

theorem workSteps_eq_components {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workSteps problem index =
      BuilderPostHeaderRawTapeBridge.bridgeWorkStepsForResult (width problem)
          (comparisonResult problem index) +
        BuilderPostDividerRawRouteClassifier.postDividerWorkStepsForResult
          (width problem) (clauseCount problem)
          (comparisonResult problem index) + 3 := by
  cases hIndex : index.val with
  | zero =>
      simp [workSteps, comparisonResult, hIndex, equalWorkSteps,
        BuilderPostHeaderRawTapeBridge.bridgeWorkStepsForResult,
        BuilderPostDividerRawRouteClassifier.postDividerWorkStepsForResult,
        BuilderPostDividerRawRouteClassifier.dividerWorkStepsForResult,
        BuilderPostDividerRawRouteClassifier.classifierWorkStepsForResult,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega
  | succ remaining =>
      simp [workSteps, comparisonResult, hIndex, greaterWorkSteps,
        greaterConsumed, greaterRemainder, greaterQuotient,
        BuilderPostHeaderRawTapeBridge.bridgeWorkStepsForResult,
        BuilderPostDividerRawRouteClassifier.postDividerWorkStepsForResult,
        BuilderPostDividerRawRouteClassifier.dividerWorkStepsForResult,
        BuilderPostDividerRawRouteClassifier.classifierWorkStepsForResult,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega

theorem compiledSteps_le_staged_add_launches {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      BuilderPostDividerRawRouteClassifier.stagedCompiledSteps problem
          (BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate problem
            index).val + 18 := by
  rw [workSteps_eq_components problem index]
  unfold BuilderPostDividerRawRouteClassifier.stagedCompiledSteps
    BuilderPostHeaderRawTapeBridge.stagedCompiledSteps
  rw [comparisonResult_eq_raw_compare problem index]
  unfold width clauseCount
  omega

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPostDividerRawRouteClassifier.rawTimeBound verifier)
    (.constant 18)

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPostDividerRawRouteClassifier.rawTimeBound
        problem.verifier).eval problem.input.length + 18 := by
  rfl

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hLocal := compiledSteps_le_staged_add_launches problem index
  have hStaged :=
    BuilderPostDividerRawRouteClassifier.stagedCompiledSteps_le_rawTimeBound
      problem
      (BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate problem
        index).val
      (BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate problem
        index).isLt
  rw [rawTimeBound_eval]
  omega

def PhysicalClassifierPipelineHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) : Prop :=
  StageHandoffsHold problem index workspace ∧
    BuilderPostDividerRawRouteClassifier.InRangeRouteClassifierHolds problem
      (BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate problem index)
      workspace ∧
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index workspace) =
      some (finalConfiguration problem index workspace) ∧
    run (compileWorkMachine machine) (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index workspace)) =
      encodeWorkConfiguration (finalConfiguration problem index workspace) ∧
    machine.isHalted
        (workRun machine (workSteps problem index - 1)
          (entryConfiguration problem index workspace)) = false ∧
    RouteAgreement problem index workspace

theorem physicalClassifierPipelineHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (workspace : List WorkSymbol) :
    PhysicalClassifierPipelineHolds problem index workspace := by
  exact ⟨stageHandoffsHold problem index workspace,
    BuilderPostDividerRawRouteClassifier.inRangeRouteClassifierHolds problem
      (BuilderPostDividerSelectedTokenLaunch.scheduleCoordinate problem index)
      workspace,
    workRunExact problem index workspace,
    run_compile_exact problem index workspace,
    one_step_short_not_halted problem index workspace,
    routeAgreement problem index workspace⟩

/-- M220 closes one fixed, all-coordinate physical classifier pipeline from
M213's post-header tape through the raw divider, the M214 bridge, and the raw
body-versus-`Finish` comparator. It does not derive the selected request, run
the dispatcher or literal loop, construct the complete formula, establish
builder `RawRefinement`, or package the Cook--Levin reduction. -/
theorem cook_levin_builder_physical_classifier_pipeline_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    machine.rules.length = 711 ∧
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) ∧
    (forall
      (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
      (workspace : List WorkSymbol),
      PhysicalClassifierPipelineHolds problem index workspace) ∧
    (forall
      (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)),
      6 * workSteps problem index ≤
        (rawTimeBound problem.verifier).eval problem.input.length) := by
  exact ⟨rules_length, rules_pairwise_query_distinct,
    physicalClassifierPipelineHolds problem,
    compiledSteps_le_rawTimeBound problem⟩
end BuilderPhysicalClassifierPipeline

end CookLevin


end PNP.Concrete
