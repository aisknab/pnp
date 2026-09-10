/-
Copyright (c) 2026 PNP Labs.

Complete negative-clause token lookup from an actual exactly-one source/request.
One fixed machine derives both source variables and the original position, then
selects the exact requested token. All five token outcomes are preserved; an
invalid pair ordinal stops before selection at a distinct stable endpoint.

Canonical register bounds and real finite tape bounds are kept separate.
Every phase and bridge is charged to the original source span. The outer
tag/index dispatcher must still derive positive-index and blank-exterior
invariants; source absence, recovery and the complete formula loop remain open.
-/
import PNP.Concrete.CookLevinBuilderRequestedExclusionInput

namespace PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup

open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request)
open BuilderExclusionPairSelection (selectedPair)
open PipelineStateNamespace (renameConfiguration)

def machine : WorkMachine :=
  WorkMachineChain.machine BuilderRequestedExclusionInput.machine BuilderExclusionClauseTokenSelector.machine
private theorem machine_projection :
    WorkMachineChain.machine BuilderRequestedExclusionInput.machine BuilderExclusionClauseTokenSelector.machine = machine := rfl
private theorem initial_projection (tape : WorkTape) :
    renameConfiguration WorkMachineChain.firstState
      (workStartConfiguration BuilderRequestedExclusionInput.machine tape) = workStartConfiguration machine tape := rfl

def trueState : Nat := WorkMachineChain.secondState 0
def falseState : Nat := WorkMachineChain.secondState 1
def paddingState : Nat := WorkMachineChain.secondState 2
def separatorState : Nat := WorkMachineChain.secondState BuilderExclusionClauseTokenSelector.separatorState
def finishState : Nat := WorkMachineChain.secondState BuilderExclusionClauseTokenSelector.finishState
def invalidState : Nat := WorkMachineChain.firstState BuilderRequestedExclusionInput.machine.rejectState

def observe (configuration : WorkConfiguration) : Option CNFToken :=
  if configuration.state = trueState then some .t else if configuration.state = falseState then some .f
  else if configuration.state = separatorState then some .sep else if configuration.state = finishState then some .finish else none
def canonicalToken {width : Nat} (variables : List (Fin width)) (request : Request) : Option CNFToken :=
  (LocalConstraint.clauseSlotDirect (.exactlyOne variables) request.clauseIndex).bind
    (fun clause => (encodeClauseTokens (BoundedClause.emit clause))[request.originalPosition]?)
def initialConfiguration {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)
def finalConfiguration {width : Nat} (first second : Fin width) (position : Nat) (older : List Nat)
    (inside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderExclusionClauseTokenSelector.finalConfiguration first second position BuilderRequestedExclusionInput.Position.retained older inside [])

theorem terminal_states_distinct :
    ([trueState, falseState, paddingState, separatorState, finishState, invalidState] : List Nat).Pairwise
      (fun left right => left ≠ right) := by
  have hNe (left right : Nat) :
      WorkMachineChain.secondState left ≠ WorkMachineChain.secondState right ↔ left ≠ right :=
    ⟨fun h e => h (congrArg WorkMachineChain.secondState e),
      fun h e => h (WorkMachineChain.secondState_injective e)⟩
  have hMapped :
      ([0, 1, 2, BuilderExclusionClauseTokenSelector.separatorState, BuilderExclusionClauseTokenSelector.finishState].map
        WorkMachineChain.secondState).Pairwise (fun left right => left ≠ right) := by
    simpa only [List.pairwise_map, hNe] using BuilderExclusionClauseTokenSelector.terminal_states_distinct
  change (([0, 1, 2, BuilderExclusionClauseTokenSelector.separatorState, BuilderExclusionClauseTokenSelector.finishState].map
    WorkMachineChain.secondState) ++ [invalidState]).Pairwise (fun left right => left ≠ right)
  rw [List.pairwise_append]
  refine ⟨hMapped, List.Pairwise.cons (by intro value h; cases h) List.Pairwise.nil, ?_⟩
  intro left hLeft right hRight
  rcases List.mem_map.mp hLeft with ⟨state, _, rfl⟩
  have hRightValue := List.mem_singleton.mp hRight
  rw [hRightValue]
  exact Ne.symm (WorkMachineChain.firstState_ne_secondState BuilderRequestedExclusionInput.machine.rejectState state)

theorem observe_rename (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderExclusionClauseTokenSelector.observe configuration := by
  have hEq (left right : Nat) :
      WorkMachineChain.secondState left = WorkMachineChain.secondState right ↔ left = right :=
    ⟨fun h => WorkMachineChain.secondState_injective h, fun h => congrArg WorkMachineChain.secondState h⟩
  simp only [observe, renameConfiguration, trueState, falseState, separatorState, finishState,
    BuilderExclusionClauseTokenSelector.observe, hEq]

theorem observe_blankEquivalent {actual canonical : WorkConfiguration}
    (hEquivalent : WorkConfiguration.BlankEquivalent actual canonical) :
    observe actual = observe canonical := by
  simp only [observe, hEquivalent.state]

theorem final_observation {width : Nat} (first second : Fin width) (position : Nat) (older : List Nat)
    (inside : List WorkSymbol) :
    observe (finalConfiguration first second position older inside) =
      (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  rw [finalConfiguration, observe_rename]
  exact BuilderExclusionClauseTokenSelector.canonical_result first second position
    BuilderRequestedExclusionInput.Position.retained older inside []

theorem observe_invalid (tape : WorkTape) : observe {state := invalidState, tape := tape} = none := rfl

theorem canonicalToken_eq_emit {width : Nat} (variables : List (Fin width)) (request : Request) :
    canonicalToken variables request =
      ((LocalConstraint.exactlyOne variables).emit[request.clauseIndex]?).bind
        (fun clause => (encodeClauseTokens (BoundedClause.emit clause))[request.originalPosition]?) := by
  rw [canonicalToken, LocalConstraint.clauseSlotDirect_eq_emit_getElem?]

theorem canonicalToken_selected {width : Nat} (variables : List (Fin width)) (request : Request)
    (first second : Fin variables.length) (hPositive : 0 < request.clauseIndex)
    (hPair : selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val)) :
    canonicalToken variables request =
      (encodeClauseTokens (BoundedClause.emit (excludeBoundedPairClause variables[first.val] variables[second.val])))[request.originalPosition]? := by
  have hIndex : request.clauseIndex - 1 + 1 = request.clauseIndex := by omega
  have hFirst : variables[first.val]? = some variables[first.val] := List.getElem?_eq_getElem first.isLt
  have hSecond : variables[second.val]? = some variables[second.val] := List.getElem?_eq_getElem second.isLt
  have hClause := BuilderExclusionPairSelection.selectedPair_observes_exactlyOne variables (request.clauseIndex - 1)
  simp only [hPair, BuilderExclusionPairSelection.observePair, hFirst, hSecond, Option.bind_some, Option.map_some, hIndex] at hClause
  unfold canonicalToken
  rw [← hClause]
  rfl

theorem canonicalToken_invalid {width : Nat} (variables : List (Fin width)) (request : Request)
    (hPositive : 0 < request.clauseIndex)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1) :
    canonicalToken variables request = none := by
  have hIndex : request.clauseIndex - 1 + 1 = request.clauseIndex := by omega
  have hNone := (BuilderExclusionPairSelection.selectedPair_none_iff variables.length (request.clauseIndex - 1)).mpr hInvalid
  have hClause := BuilderExclusionPairSelection.selectedPair_observes_exactlyOne variables (request.clauseIndex - 1)
  simp only [hNone, BuilderExclusionPairSelection.observePair, hIndex] at hClause
  unfold canonicalToken
  rw [← hClause]
  rfl

private theorem no_rule_at_second (first second : WorkMachine) (state : Nat)
    (hNo : WorkMachineProgramGraph.NoRuleAt second state) :
    WorkMachineProgramGraph.NoRuleAt (WorkMachineChain.machine first second) (WorkMachineChain.secondState state) :=
  WorkMachineChain.noRuleAtAccept first {second with acceptState := state} hNo
private theorem bridge_source {source target : Nat} {rule : WorkRule}
    (hMem : rule ∈ PipelineStageBridges.launchRules source target) : rule.sourceState = source := by
  rcases List.mem_map.mp hMem with ⟨symbol, _, rfl⟩
  rfl
private theorem no_rule_at_first (first second : WorkMachine) (state : Nat)
    (hDifferent : first.acceptState ≠ state) (hNo : WorkMachineProgramGraph.NoRuleAt first state) :
    WorkMachineProgramGraph.NoRuleAt (WorkMachineChain.machine first second) (WorkMachineChain.firstState state) := by
  intro rule hMem hEqual
  simp only [WorkMachineChain.machine, WorkMachineChain.rules, List.mem_append] at hMem
  rcases hMem with hBridge | hFirst | hSecond
  · have hSource := bridge_source hBridge
    exact hDifferent (WorkMachineChain.firstState_injective (hSource.symm.trans hEqual))
  · rcases List.mem_map.mp hFirst with ⟨localRule, hLocal, rfl⟩
    exact hNo localRule hLocal (WorkMachineChain.firstState_injective hEqual)
  · rcases List.mem_map.mp hSecond with ⟨localRule, _, rfl⟩
    exact WorkMachineChain.firstState_ne_secondState _ _ hEqual.symm

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _ BuilderRequestedExclusionInput.rules_pairwise_query_distinct
    BuilderExclusionClauseTokenSelector.rules_pairwise_query_distinct BuilderRequestedExclusionInput.noRuleAtAccept
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderExclusionClauseTokenSelector.noRuleAtAccept
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  no_rule_at_second _ _ _ BuilderExclusionClauseTokenSelector.noRuleAtReject
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderExclusionClauseTokenSelector.acceptState_ne_rejectState
theorem noRuleAtPadding : WorkMachineProgramGraph.NoRuleAt machine paddingState :=
  no_rule_at_second _ _ _ BuilderExclusionClauseTokenSelector.noRuleAtPadding
theorem noRuleAtSeparator : WorkMachineProgramGraph.NoRuleAt machine separatorState :=
  no_rule_at_second _ _ _ BuilderExclusionClauseTokenSelector.noRuleAtSeparator
theorem noRuleAtFinish : WorkMachineProgramGraph.NoRuleAt machine finishState :=
  no_rule_at_second _ _ _ BuilderExclusionClauseTokenSelector.noRuleAtFinish
theorem noRuleAtInvalid : WorkMachineProgramGraph.NoRuleAt machine invalidState :=
  no_rule_at_first _ _ _ BuilderRequestedExclusionInput.acceptState_ne_rejectState BuilderRequestedExclusionInput.noRuleAtReject

def canonicalSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderExclusionClauseTokenSelector.spanPolynomial (BuilderRequestedExclusionInput.canonicalSpanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRequestedExclusionInput.rawTimePolynomial bound) (.constant 6))
    (BuilderExclusionClauseTokenSelector.rawTimePolynomial (BuilderRequestedExclusionInput.canonicalSpanPolynomial bound))
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add bound (rawTimePolynomial bound)

private theorem equivalent_rename (rename : Nat → Nat) {actual canonical : WorkConfiguration}
    (hEquivalent : WorkConfiguration.BlankEquivalent actual canonical) :
    WorkConfiguration.BlankEquivalent (renameConfiguration rename actual) (renameConfiguration rename canonical) :=
  ⟨congrArg rename hEquivalent.state, hEquivalent.tape⟩

/-- All selector data and its successful execution are derived inside the
original-source theorem; the selected clause is identified in canonical order. -/
theorem workRun_valid_source_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (steps : Nat) (preparedOlder : List Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      (∃ suffix, preparedOlder = BuilderRequestedPairLookup.initialValues variables request older ++ suffix) ∧
      workRunExact? machine steps (initialConfiguration variables request older inside outside) = some final ∧
      WorkConfiguration.BlankEquivalent final
        (finalConfiguration variables[first.val] variables[second.val] request.originalPosition preparedOlder inside) ∧
      observe final = canonicalToken variables request ∧
      (registerWord (BuilderExclusionClauseTokenSelector.finalValues variables[first.val] variables[second.val]
        request.originalPosition BuilderRequestedExclusionInput.Position.retained preparedOlder)).length +
        (BuilderExclusionClauseTokenSelector.finalOutside variables[first.val] variables[second.val] request.originalPosition []).length ≤
          (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  obtain ⟨first, second, prepareSteps, preparedOlder, middle, hPair, hPrefix, hPrepare,
      hPrepareEquivalent, hCanonicalSpan, _, hPrepareTime⟩ :=
    BuilderRequestedExclusionInput.workRun_source_prepare variables request older inside outside bound input
      hPositive hBlank hValid hSpan
  have hSelectorBounds := BuilderExclusionClauseTokenSelector.source_polynomial_bounds variables[first.val] variables[second.val]
    request.originalPosition BuilderRequestedExclusionInput.Position.retained preparedOlder
    BuilderRequestedExclusionInput.Position.retained_length [] (BuilderRequestedExclusionInput.canonicalSpanPolynomial bound) input (by
      simpa only [List.length_nil, Nat.add_zero] using hCanonicalSpan)
  have hSelector := BuilderExclusionClauseTokenSelector.workRunExact variables[first.val] variables[second.val]
    request.originalPosition BuilderRequestedExclusionInput.Position.retained preparedOlder
    BuilderRequestedExclusionInput.Position.retained_length inside []
  have hSelectorInitial : WorkConfiguration.BlankEquivalent
      (workStartConfiguration BuilderExclusionClauseTokenSelector.machine middle.tape)
      (BuilderExclusionClauseTokenSelector.initialConfiguration variables[first.val].val variables[second.val].val
        request.originalPosition BuilderRequestedExclusionInput.Position.retained preparedOlder inside []) := by
    refine ⟨rfl, ?_⟩
    exact hPrepareEquivalent.tape
  obtain ⟨selectedFinal, hSelected, hSelectedEquivalent⟩ :=
    PNP.Concrete.workRunExact?_transport BuilderExclusionClauseTokenSelector.machine _ hSelectorInitial hSelector
  have hPrepareState := hPrepareEquivalent.state
  simp only [workStartConfiguration] at hSelected
  have hChain := WorkMachineChain.workRunExact BuilderRequestedExclusionInput.machine BuilderExclusionClauseTokenSelector.machine
    prepareSteps _ _ _ _ hPrepare hPrepareState hSelected
  rw [machine_projection, initial_projection] at hChain
  let steps := prepareSteps + 1 +
    BuilderExclusionClauseTokenSelector.workSteps variables[first.val] variables[second.val] request.originalPosition
      BuilderRequestedExclusionInput.Position.retained BuilderRequestedExclusionInput.Position.retained_length
  let final := renameConfiguration WorkMachineChain.secondState selectedFinal
  have hExecution : workRunExact? machine steps (initialConfiguration variables request older inside outside) = some final := hChain
  have hEquivalent : WorkConfiguration.BlankEquivalent final
      (finalConfiguration variables[first.val] variables[second.val] request.originalPosition preparedOlder inside) :=
    equivalent_rename WorkMachineChain.secondState hSelectedEquivalent
  have hObserved : observe final = canonicalToken variables request := by
    rw [observe_blankEquivalent hEquivalent, final_observation, canonicalToken_selected variables request first second hPositive hPair]
  have hTime : 6 * steps ≤ (rawTimePolynomial bound).eval input := by
    have hSelectTime := hSelectorBounds.2
    simp only [steps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  refine ⟨first, second, steps, preparedOlder, final, hPair, hPrefix, hExecution, hEquivalent, hObserved, hSelectorBounds.1, ?_, hTime⟩
  have hCells := BuilderRequestedPairLookup.workRun_storedCells machine steps _ _ hExecution
  simp only [BuilderRequestedPairLookup.storedCells, initialConfiguration, workStartConfiguration, endTape,
    List.length_append, List.length_reverse] at hCells ⊢
  simp only [spanPolynomial, NatPolynomial.eval_add]
  omega

/-- Out-of-range pair requests stop in the first phase, not at the false-token
endpoint. The selector is never entered and the canonical request frame remains. -/
theorem workRun_invalid_source_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps (initialConfiguration variables request older inside outside) = some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := invalidState
        tape := endTape (BuilderRequestedPairVariables.lookupValues variables request older) inside []
      } ∧
      observe final = canonicalToken variables request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  obtain ⟨steps, rejected, hReject, hRejectedEquivalent, _, hRejectTime⟩ :=
    BuilderRequestedExclusionInput.workRun_invalid_source_prepare variables request older inside outside bound input
      hPositive hBlank hInvalid hSpan
  have hLift := PipelineStageBridges.workRunExact?_transport
    BuilderRequestedExclusionInput.machine
    (WorkMachineChain.machine BuilderRequestedExclusionInput.machine BuilderExclusionClauseTokenSelector.machine)
    WorkMachineChain.firstState
    (WorkMachineChain.first_workStep_of_some BuilderRequestedExclusionInput.machine BuilderExclusionClauseTokenSelector.machine)
    steps _ _ hReject
  rw [machine_projection, initial_projection] at hLift
  let final := renameConfiguration WorkMachineChain.firstState rejected
  have hExecution : workRunExact? machine steps (initialConfiguration variables request older inside outside) = some final := hLift
  have hEquivalent : WorkConfiguration.BlankEquivalent final {
      state := invalidState
      tape := endTape (BuilderRequestedPairVariables.lookupValues variables request older) inside []
    } := equivalent_rename WorkMachineChain.firstState hRejectedEquivalent
  have hObserved : observe final = canonicalToken variables request := by
    rw [observe_blankEquivalent hEquivalent, observe_invalid, canonicalToken_invalid variables request hPositive hInvalid]
  have hTime : 6 * steps ≤ (rawTimePolynomial bound).eval input := by
    simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  refine ⟨steps, final, hExecution, hEquivalent, hObserved, ?_, hTime⟩
  have hCells := BuilderRequestedPairLookup.workRun_storedCells machine steps _ _ hExecution
  simp only [BuilderRequestedPairLookup.storedCells, initialConfiguration, workStartConfiguration, endTape,
    List.length_append, List.length_reverse] at hCells ⊢
  simp only [spanPolynomial, NatPolynomial.eval_add]
  omega

/-- Every positive exactly-one clause request is covered, including invalid
pair ordinals and positions past the complete encoded clause. -/
theorem workRun_polynomial_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps (initialConfiguration variables request older inside outside) = some final ∧
      observe final = canonicalToken variables request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  by_cases hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length
  · obtain ⟨_, _, steps, _, final, _, _, hRun, _, hObserved, _, hSpace, hTime⟩ :=
      workRun_valid_source_lookup variables request older inside outside bound input hPositive hBlank hValid hSpan
    exact ⟨steps, final, hRun, hObserved, hSpace, hTime⟩
  · obtain ⟨steps, final, hRun, _, hObserved, hSpace, hTime⟩ :=
      workRun_invalid_source_lookup variables request older inside outside bound input hPositive hBlank (by omega) hSpan
    exact ⟨steps, final, hRun, hObserved, hSpace, hTime⟩

theorem uniform_polynomial_lookup {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration variables request older inside outside)) = encodeWorkConfiguration final ∧
      observe final = canonicalToken variables request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  obtain ⟨steps, final, hRun, hObserved, hSpace, hTime⟩ :=
    workRun_polynomial_lookup variables request older inside outside bound input hPositive hBlank hSpan
  exact ⟨6 * steps, final, hTime, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hObserved, hSpace⟩

end PNP.Concrete.CookLevin.BuilderRequestedExclusionTokenLookup
