/-
Copyright (c) 2026 PNP Labs.

Complete physical body-clause lookup from the actual source/request frame.
A fixed source-family program first constructs the search input, then selects
the exact canonical token. Injective state renaming preserves all five stable
outcomes, including separator, finish and padding. Every phase and bridge is
charged to one original-input polynomial bound.

The enclosing dispatcher must still derive the source family and body/pair
branch from the actual tag and clause index. Absent sources, negative pairs,
cleanup/root recovery and the full formula loop remain separate obligations.
-/
import PNP.Concrete.CookLevinBuilderPayloadBodyPreparation

namespace PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup

open PipelineTape
open BuilderPayloadSourceSearchBlank (BlankOutside)
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family Request family body requestValues)
open WorkMachineProgramGraph (endpointConfiguration)
open PipelineStateNamespace (renameConfiguration)

def machine (route : Family) : WorkMachine :=
  WorkMachineChain.machine (BuilderPayloadBodyPreparation.machine route) (BuilderPayloadClauseTokenSelector.machine route)

def trueState : Nat := WorkMachineChain.secondState BuilderPayloadClauseTokenSelector.trueState
def falseState : Nat := WorkMachineChain.secondState 1
def paddingState : Nat := WorkMachineChain.secondState 2
def separatorState : Nat := WorkMachineChain.secondState BuilderPayloadClauseTokenSelector.separatorState
def finishState : Nat := WorkMachineChain.secondState BuilderPayloadClauseTokenSelector.finishState

def observe (configuration : WorkConfiguration) : Option CNFToken :=
  if configuration.state = trueState then some .t else if configuration.state = falseState then some .f
  else if configuration.state = separatorState then some .sep else if configuration.state = finishState then some .finish else none

def initialConfiguration {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine (family constraint))
    (endTape (requestValues constraint request older) inside outside)
def finalConfiguration {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (values : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (endpointConfiguration (BuilderPayloadClauseTokenSelector.endpoint constraint request.originalPosition) (endTape values inside outside))

theorem terminal_states_distinct :
    ([trueState,falseState,paddingState,separatorState,finishState] : List Nat).Pairwise
      (fun left right => left ≠ right) := by decide

theorem observe_rename (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderPayloadClauseTokenSelector.observe configuration := by
  have hEq (left right : Nat) :
      WorkMachineChain.secondState left = WorkMachineChain.secondState right ↔ left = right :=
    ⟨fun h => WorkMachineChain.secondState_injective h,
      fun h => congrArg WorkMachineChain.secondState h⟩
  simp only [observe, renameConfiguration, trueState, falseState, separatorState, finishState,
    BuilderPayloadClauseTokenSelector.observe, BuilderLiteralClauseTokenSelector.observe, hEq,
    BuilderPayloadClauseTokenSelector.trueState, BuilderPayloadClauseTokenSelector.separatorState, BuilderPayloadClauseTokenSelector.finishState]

theorem final_observation {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (values : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration constraint request values inside outside) =
      (encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]? := by
  rw [finalConfiguration, observe_rename]
  exact BuilderPayloadClauseTokenSelector.endpoint_observes_encoding constraint request.originalPosition _

private theorem no_rule_at_second (first second : WorkMachine) (state : Nat)
    (hNo : WorkMachineProgramGraph.NoRuleAt second state) :
    WorkMachineProgramGraph.NoRuleAt (WorkMachineChain.machine first second) (WorkMachineChain.secondState state) :=
  WorkMachineChain.noRuleAtAccept first {second with acceptState := state} hNo

theorem rules_pairwise_query_distinct (route : Family) :
    (machine route).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _ (BuilderPayloadBodyPreparation.rules_pairwise_query_distinct route)
    (BuilderPayloadClauseTokenSelector.rules_pairwise_query_distinct route) (BuilderPayloadBodyPreparation.noRuleAtAccept route)
theorem noRuleAtAccept (route : Family) : WorkMachineChain.NoRuleAtAccept (machine route) :=
  WorkMachineChain.noRuleAtAccept _ _ (BuilderPayloadClauseTokenSelector.noRuleAtAccept route)
theorem noRuleAtReject (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) (machine route).rejectState :=
  no_rule_at_second _ _ _ (BuilderPayloadClauseTokenSelector.noRuleAtReject route)
theorem acceptState_ne_rejectState (route : Family) :
    (machine route).acceptState ≠ (machine route).rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ (BuilderPayloadClauseTokenSelector.acceptState_ne_rejectState route)
theorem noRuleAtPadding (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) paddingState :=
  no_rule_at_second _ _ _ (BuilderPayloadClauseTokenSelector.noRuleAtPadding route)
theorem noRuleAtSeparator (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) separatorState :=
  no_rule_at_second _ _ _ (BuilderPayloadClauseTokenSelector.noRuleAtSeparator route)
theorem noRuleAtFinish (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) finishState :=
  no_rule_at_second _ _ _ (BuilderPayloadClauseTokenSelector.noRuleAtFinish route)

def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderPayloadClauseTokenSelector.spanPolynomial (BuilderPayloadBodyPreparation.spanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderPayloadBodyPreparation.rawTimePolynomial bound) (.constant 6))
    (BuilderPayloadClauseTokenSelector.rawTimePolynomial (BuilderPayloadBodyPreparation.spanPolynomial bound))

private theorem machine_projection (route : Family) :
    WorkMachineChain.machine (BuilderPayloadBodyPreparation.machine route)
      (BuilderPayloadClauseTokenSelector.machine route) = machine route := rfl

private theorem initial_projection (route : Family) (tape : WorkTape) :
    renameConfiguration WorkMachineChain.firstState
      (workStartConfiguration (BuilderPayloadBodyPreparation.machine route) tape) =
      workStartConfiguration (machine route) tape := rfl

/-- The execution witness and physical search frame are derived internally
from the actual source/request; no prepared count, token or execution is supplied. -/
theorem workRun_polynomial_lookup_with_blank {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (requestValues constraint request older)).length + outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol),
      workRunExact? (machine (family constraint)) steps
        (initialConfiguration constraint request older inside outside) =
        some (finalConfiguration constraint request values inside resultOutside) ∧
      observe (finalConfiguration constraint request values inside resultOutside) =
        (encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]? ∧
      (∃ scratch, values = requestValues constraint request older ++ scratch) ∧
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input ∧
      (BlankOutside outside → BlankOutside resultOutside) := by
  have hPrepBounds := BuilderPayloadBodyPreparation.source_polynomial_bounds constraint request older outside bound input hSpan
  have hEntry : (registerWord (BuilderPayloadClauseTokenSelector.initialValues constraint request request.originalPosition older)).length +
      (BuilderPayloadBodyPreparation.finalOutside constraint request outside).length ≤ (BuilderPayloadBodyPreparation.spanPolynomial bound).eval input := by
    rw [← BuilderPayloadBodyPreparation.final_values_search_input]
    exact hPrepBounds.1
  obtain ⟨steps, values, resultOutside, hLookup, _, hRetained, hSpace, hTime, hResultBlank⟩ :=
    BuilderPayloadClauseTokenSelector.workRun_polynomial_lookup_with_blank constraint request request.originalPosition older inside
      (BuilderPayloadBodyPreparation.finalOutside constraint request outside) (BuilderPayloadBodyPreparation.spanPolynomial bound) input hEntry
  have hPrep := BuilderPayloadBodyPreparation.workRunExact constraint request older inside outside
  rw [← BuilderPayloadBodyPreparation.final_values_search_input] at hLookup
  have hChain := WorkMachineChain.workRunExact (BuilderPayloadBodyPreparation.machine (family constraint))
    (BuilderPayloadClauseTokenSelector.machine (family constraint)) (BuilderPayloadBodyPreparation.workSteps constraint request) steps
    _ _ _ hPrep rfl hLookup
  rw [machine_projection] at hChain
  refine ⟨BuilderPayloadBodyPreparation.workSteps constraint request + 1 + steps, values, resultOutside, ?_,
    final_observation constraint request values inside resultOutside, hRetained, hSpace, ?_, ?_⟩
  · simpa only [BuilderPayloadBodyPreparation.initialConfiguration, BuilderPayloadBodyPreparation.initialValues, initial_projection, initialConfiguration,
      finalConfiguration] using hChain
  · have hPrepTime := hPrepBounds.2
    simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  · intro hBlank
    exact hResultBlank (BuilderPayloadSourceSearchBlank.blank_drop _ _
      (BuilderPayloadSourceSearchBlank.blank_drop _ _ (BuilderPayloadSourceSearchBlank.blank_drop outside _ hBlank)))

/-- Preserve the existing arbitrary-exterior lookup interface. -/
theorem workRun_polynomial_lookup {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (requestValues constraint request older)).length + outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol),
      workRunExact? (machine (family constraint)) steps
        (initialConfiguration constraint request older inside outside) =
        some (finalConfiguration constraint request values inside resultOutside) ∧
      observe (finalConfiguration constraint request values inside resultOutside) =
        (encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]? ∧
      (∃ scratch, values = requestValues constraint request older ++ scratch) ∧
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  obtain ⟨steps, values, resultOutside, hRun, hToken, hRetained, hSpace, hTime, _⟩ :=
    workRun_polynomial_lookup_with_blank constraint request older inside outside bound input hSpan
  exact ⟨steps, values, resultOutside, hRun, hToken, hRetained, hSpace, hTime⟩

theorem uniform_polynomial_lookup {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (requestValues constraint request older)).length + outside.length ≤ bound.eval input) :
    ∃ (rawSteps : Nat) (values : List Nat) (resultOutside : List WorkSymbol),
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine (machine (family constraint))) rawSteps
        (encodeWorkConfiguration (initialConfiguration constraint request older inside outside)) =
        encodeWorkConfiguration (finalConfiguration constraint request values inside resultOutside) ∧
      observe (finalConfiguration constraint request values inside resultOutside) =
        (encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]? ∧
      (∃ scratch, values = requestValues constraint request older ++ scratch) ∧
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input := by
  obtain ⟨steps, values, resultOutside, hRun, hToken, hRetained, hSpace, hTime⟩ :=
    workRun_polynomial_lookup constraint request older inside outside bound input hSpan
  exact ⟨6 * steps, values, resultOutside, hTime,
    run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hToken, hRetained, hSpace⟩

end PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup
