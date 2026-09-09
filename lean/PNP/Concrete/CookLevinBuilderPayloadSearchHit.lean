/-
Copyright (c) 2026 PNP Labs.

The hit continuation for source-bound literal search. Erase exactly the fourteen
comparison scratch registers, retaining the actual source/request/cursor frame,
then read the source literal and select its canonical token. No source list is
copied or supplied hit verdict compiled into the machine.

This intermediate contract accepts the physical comparison frame. The enclosing
guarded loop must still derive the valid ordinal and the branch from input.
-/
import PNP.Concrete.CookLevinBuilderPayloadSearchComparison
import PNP.Concrete.CookLevinBuilderRegisterErase

namespace PNP.Concrete.CookLevin.BuilderPayloadSearchHit

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadLiteralTokenSelector (Kind Source Context)
open PipelineStateNamespace (renameConfiguration)

def machine (kind : Kind) : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterErase.machine 14)
    (BuilderPayloadLiteralTokenSelector.machine kind)
def scratch {width : Nat} (source : Source width) (context : Context source.ordinal) : List Nat :=
  BuilderPayloadSearchComparison.comparisonScratch source.kind source.ordinal context.position source.originalLiteral.index.val
def initialValues {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) : List Nat :=
  BuilderPayloadSearchComparison.finalValues source context older
def restoredOutside {width : Nat} (source : Source width) (context : Context source.ordinal) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (BuilderRegisterErase.clearedSpan (scratch source context)) .blank ++ outside
def workSteps {width : Nat} (source : Source width) (context : Context source.ordinal) : Nat :=
  BuilderRegisterErase.workSteps (scratch source context) + 1 +
    BuilderPayloadLiteralTokenSelector.workSteps source context
def initialConfiguration {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine source.kind) (endTape (initialValues source context older) inside outside)
def finalConfiguration {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderPayloadLiteralTokenSelector.finalConfiguration source context older inside (restoredOutside source context outside))
def finalValues {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) : List Nat :=
  BuilderLiteralTokenSelector.finalValues source.selectedLiteral.positive source.originalLiteral.index.val
    context.position (BuilderPayloadLiteralTokenSelector.prepareOlder source context older)
def finalOutside {width : Nat} (source : Source width) (context : Context source.ordinal) (outside : List WorkSymbol) : List WorkSymbol :=
  BuilderLiteralTokenSelector.finalOutside source.selectedLiteral.positive source.originalLiteral.index.val
    context.position (BuilderPayloadLiteralTokenSelector.prepareOutside source context (restoredOutside source context outside))
def observe (configuration : WorkConfiguration) : Option CNFToken :=
  if configuration.state = WorkMachineChain.secondState (WorkMachineChain.secondState 0) then some .t
  else if configuration.state = WorkMachineChain.secondState (WorkMachineChain.secondState 1) then some .f else none

theorem scratch_length {width : Nat} (source : Source width) (context : Context source.ordinal) :
    (scratch source context).length = 14 :=
  BuilderPayloadSearchComparison.comparisonScratch_length source.kind source.ordinal context.position source.originalLiteral.index.val

theorem input_layout {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) :
    initialValues source context older = BuilderPayloadLiteralTokenSelector.initialValues source context older ++ scratch source context := by
  simp only [initialValues, BuilderPayloadSearchComparison.finalValues, BuilderPayloadSearchComparison.chunk_scratch_layout,
    BuilderPayloadSearchComparison.baseValues, BuilderPayloadLiteralTokenSelector.initialValues, scratch, List.append_assoc]

theorem restore_workRunExact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (BuilderRegisterErase.machine 14) (BuilderRegisterErase.workSteps (scratch source context))
      (workStartConfiguration (BuilderRegisterErase.machine 14) (endTape (initialValues source context older) inside outside)) =
      some {state := (BuilderRegisterErase.machine 14).acceptState, tape := endTape (BuilderPayloadLiteralTokenSelector.initialValues source context older) inside (restoredOutside source context outside)} := by
  have h := BuilderRegisterErase.workRunExact 14 (BuilderPayloadLiteralTokenSelector.initialValues source context older)
    (scratch source context) inside outside (scratch_length source context)
  simpa only [BuilderRegisterErase.initialConfiguration, BuilderRegisterErase.finalConfiguration,
    restoredOutside, input_layout] using h

theorem restored_span_eq {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) :
    (registerWord (BuilderPayloadLiteralTokenSelector.initialValues source context older)).length +
      (restoredOutside source context outside).length =
    (registerWord (initialValues source context older)).length + outside.length := by
  simp only [input_layout, restoredOutside, BuilderRegisterErase.clearedSpan,
    registerWord_append, List.length_append, List.length_replicate, Nat.add_assoc]

theorem workRunExact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine source.kind) (workSteps source context) (initialConfiguration source context older inside outside) =
      some (finalConfiguration source context older inside outside) := by
  have hRestore := restore_workRunExact source context older inside outside
  have hSelect := BuilderPayloadLiteralTokenSelector.workRunExact source context older inside (restoredOutside source context outside)
  exact WorkMachineChain.workRunExact _ _ _ _ _ _ _ hRestore rfl hSelect

theorem run_compile_exact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine source.kind)) (6 * workSteps source context)
      (encodeWorkConfiguration (initialConfiguration source context older inside outside)) =
      encodeWorkConfiguration (finalConfiguration source context older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact source context older inside outside)

theorem observe_renamed (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderPayloadLiteralTokenSelector.observe configuration := by
  simp only [observe, renameConfiguration, BuilderPayloadLiteralTokenSelector.observe,
    BuilderIndexedLiteralTokenSelector.observe, WorkMachineChain.secondState_injective.eq_iff]

theorem canonical_result {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration source context older inside outside) =
      DirectToken.literalSlot source.selectedLiteral.emit context.position := by
  rw [finalConfiguration, observe_renamed]
  exact BuilderPayloadLiteralTokenSelector.canonical_result source context older inside (restoredOutside source context outside)

theorem workRun_observes_literal {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun (machine source.kind) (workSteps source context) (initialConfiguration source context older inside outside)) =
      DirectToken.literalSlot source.selectedLiteral.emit context.position := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact source context older inside outside)]
  exact canonical_result source context older inside outside

theorem final_tape {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration source context older inside outside).tape =
      endTape (finalValues source context older) inside (finalOutside source context outside) := rfl

theorem original_frame_preserved {width : Nat} (source : Source width) (context : Context source.ordinal) (older : List Nat) :
    ∃ remainingScratch, finalValues source context older =
      BuilderPayloadLiteralTokenSelector.initialValues source context older ++ remainingScratch :=
  BuilderPayloadLiteralTokenSelector.original_frame_preserved source context older

theorem rules_pairwise_query_distinct (kind : Kind) :
    (machine kind).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _ (BuilderRegisterErase.rules_pairwise_query_distinct 14)
    (BuilderPayloadLiteralTokenSelector.rules_pairwise_query_distinct kind) (BuilderRegisterErase.noRuleAtAccept 14)
theorem noRuleAtAccept (kind : Kind) : WorkMachineChain.NoRuleAtAccept (machine kind) :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderPayloadLiteralTokenSelector.noRuleAtAccept kind)
theorem noRuleAtReject (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (machine kind) (machine kind).rejectState :=
  WorkMachineChain.noRuleAtAccept (BuilderRegisterErase.machine 14)
    {BuilderPayloadLiteralTokenSelector.machine kind with acceptState := (BuilderPayloadLiteralTokenSelector.machine kind).rejectState}
    (BuilderPayloadLiteralTokenSelector.noRuleAtReject kind)
theorem acceptState_ne_rejectState (kind : Kind) : (machine kind).acceptState ≠ (machine kind).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (BuilderPayloadLiteralTokenSelector.acceptState_ne_rejectState kind)
theorem noRuleAtPadding (kind : Kind) : WorkMachineProgramGraph.NoRuleAt (machine kind)
    (WorkMachineChain.secondState (WorkMachineChain.secondState 2)) :=
  WorkMachineChain.noRuleAtAccept (BuilderRegisterErase.machine 14)
    {BuilderPayloadLiteralTokenSelector.machine kind with acceptState := WorkMachineChain.secondState 2}
    (BuilderPayloadLiteralTokenSelector.noRuleAtPadding kind)

def spanPolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  BuilderPayloadLiteralTokenSelector.spanPolynomial kind bound
def rawTimePolynomial (kind : Kind) (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterErase.rawTimePolynomial bound) (.constant 6))
    (BuilderPayloadLiteralTokenSelector.rawTimePolynomial kind bound)

theorem source_polynomial_bounds {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues source context older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues source context older)).length + (finalOutside source context outside).length ≤
      (spanPolynomial source.kind bound).eval input ∧
    6 * workSteps source context ≤ (rawTimePolynomial source.kind bound).eval input := by
  have hRestored : (registerWord (BuilderPayloadLiteralTokenSelector.initialValues source context older)).length +
      (restoredOutside source context outside).length ≤ bound.eval input := by
    rw [restored_span_eq]
    exact hSpan
  have hScratch : BuilderRegisterErase.clearedSpan (scratch source context) ≤ bound.eval input := by
    simp only [input_layout, registerWord_append, List.length_append] at hSpan
    exact Nat.le_trans (by unfold BuilderRegisterErase.clearedSpan; omega) hSpan
  have hErase := BuilderRegisterErase.source_polynomial_bound bound input (scratch source context) hScratch
  have hSelect := BuilderPayloadLiteralTokenSelector.source_polynomial_bounds source context older
    (restoredOutside source context outside) bound input hRestored
  constructor
  · exact hSelect.1
  · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

/-- The physical comparison's accepting state links directly to the hit machine.
The inequality is a theorem premise for this branch, not an executable verdict. -/
theorem comparison_hit_workRunExact {width : Nat} (source : Source width) (context : Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol)
    (hHit : context.position < source.originalLiteral.index.val + 2) :
    workRunExact? (WorkMachineChain.machine (BuilderPayloadSearchComparison.machine source.kind) (machine source.kind))
      (BuilderPayloadSearchComparison.workSteps source context + 1 + workSteps source context)
      (workStartConfiguration (WorkMachineChain.machine (BuilderPayloadSearchComparison.machine source.kind) (machine source.kind))
        (endTape (BuilderPayloadSearchComparison.initialValues source context older) inside outside)) =
      some (renameConfiguration WorkMachineChain.secondState
        (finalConfiguration source context older inside (BuilderPayloadSearchComparison.finalOutside source context outside))) := by
  have hCompare := BuilderPayloadSearchComparison.workRunExact source context older inside outside
  have hState := (BuilderPayloadSearchComparison.final_accept_iff source context older inside outside).2 hHit
  have hSelect : workRunExact? (machine source.kind) (workSteps source context)
      (workStartConfiguration (machine source.kind) (BuilderPayloadSearchComparison.finalConfiguration source context older inside outside).tape) =
      some (finalConfiguration source context older inside (BuilderPayloadSearchComparison.finalOutside source context outside)) := by
    rw [BuilderPayloadSearchComparison.final_tape]
    exact workRunExact source context older inside (BuilderPayloadSearchComparison.finalOutside source context outside)
  exact WorkMachineChain.workRunExact _ _ _ _ _ _ _ hCompare hState hSelect

end PNP.Concrete.CookLevin.BuilderPayloadSearchHit
