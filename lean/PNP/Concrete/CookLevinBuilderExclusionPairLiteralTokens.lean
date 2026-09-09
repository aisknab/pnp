/-
Copyright (c) 2026 PNP Labs.

Read the exact negative-literal body of a canonical exclusion clause from the
two physically retained source-variable values and an actual position register.
A fixed seven-field pack feeds the existing complete literal-list locator;
no selected literal or token verdict determines executable control.

The eleven-register retained suffix is produced by the second source reader.
Clause separator/finish selection and source-position request binding remain
downstream; this module does not claim the complete clause or formula builder.
-/

import PNP.Concrete.CookLevinBuilderExclusionPairSecondVariable
import PNP.Concrete.CookLevinBuilderLiteralListSearchBounds

namespace PNP.Concrete.CookLevin.BuilderExclusionPairLiteralTokens

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues)
open PipelineStateNamespace (renameConfiguration)

def frame (first second position : Nat) (retained : List Nat) : List Nat :=
  [first] ++ retained ++ [second, position]

theorem frame_length (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    (frame first second position retained).length = 14 := by
  simp only [frame, List.length_append, List.length_cons, List.length_nil, hRetained]

def environment (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) (index : Fin 14) : Nat :=
  (frame first second position retained)[index.val]'(by
    rw [frame_length first second position retained hRetained]
    exact index.isLt)

theorem environment_values (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    List.ofFn (environment first second position retained hRetained) =
      frame first second position retained := by
  apply List.ext_getElem
  · rw [List.length_ofFn, frame_length first second position retained hRetained]
  · intro index hLeft hRight
    simp only [List.getElem_ofFn]
    rfl

theorem environment_first (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    environment first second position retained hRetained ⟨0, by decide⟩ = first := rfl

theorem environment_second (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    environment first second position retained hRetained ⟨12, by decide⟩ = second := by
  simp only [environment, frame, List.cons_append, List.nil_append, List.getElem_cons_succ]
  rw [List.getElem_append_right (by omega)]
  simp only [hRetained]
  rfl

theorem environment_position (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    environment first second position retained hRetained ⟨13, by decide⟩ = position := by
  simp only [environment, frame, List.cons_append, List.nil_append, List.getElem_cons_succ]
  rw [List.getElem_append_right (by omega)]
  simp only [hRetained]
  rfl

def fields : List (BuilderRegisterPack.Field 14) :=
  [.argument ⟨12, by decide⟩, .constant 0,
   .argument ⟨0, by decide⟩, .constant 0,
   .constant 0, .constant 2, .argument ⟨13, by decide⟩]

theorem fields_length : fields.length = 7 := rfl

theorem packed_values (first second position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) :
    BuilderRegisterPack.values fields (environment first second position retained hRetained) =
      [second, 0, first, 0, 0, 2, position] := by
  change [environment first second position retained hRetained ⟨12, by decide⟩, 0,
    environment first second position retained hRetained ⟨0, by decide⟩, 0, 0, 2,
    environment first second position retained hRetained ⟨13, by decide⟩] = _
  rw [environment_second, environment_first, environment_position]

theorem literal_payload {width : Nat} (first second : Fin width) :
    literalListValues (excludeBoundedPairClause first second) =
      [0, first.val, 0, second.val] := rfl

def initialValues (first second position : Nat) (retained older : List Nat) : List Nat :=
  older ++ frame first second position retained

theorem lookup_layout {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) :
    older ++ List.ofFn (environment first.val second.val position retained hRetained) ++
        BuilderRegisterPack.values fields (environment first.val second.val position retained hRetained) =
      BuilderLiteralListSearch.initialValues (excludeBoundedPairClause first second) position
        (initialValues first.val second.val position retained older) := by
  rw [environment_values, packed_values]
  change (older ++ frame first.val second.val position retained) ++ [second.val, 0, first.val, 0, 0, 2, position] =
    ((older ++ frame first.val second.val position retained) ++ [second.val, 0, first.val, 0]) ++ [0, 2, position]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

def prepareMachine : WorkMachine := BuilderRegisterPack.machine fields 0
def machine : WorkMachine := WorkMachineChain.machine prepareMachine BuilderLiteralListSearch.machine
def prepareSteps (first second position : Nat) (retained : List Nat) (hRetained : retained.length = 11) : Nat :=
  BuilderRegisterPack.workSteps fields (environment first second position retained hRetained) []
def workSteps {width : Nat} (first second : Fin width) (position : Nat) (retained : List Nat)
    (hRetained : retained.length = 11) : Nat :=
  prepareSteps first.val second.val position retained hRetained + 1 +
    BuilderLiteralListSearch.workSteps (excludeBoundedPairClause first second) position
def prepareOutside (first second position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop (registerWord [second, 0, first, 0, 0, 2, position]).length
def finalValues {width : Nat} (first second : Fin width) (position : Nat) (retained older : List Nat) : List Nat :=
  BuilderLiteralListSearch.finalValues (excludeBoundedPairClause first second) position
    (initialValues first.val second.val position retained older)
def finalOutside {width : Nat} (first second : Fin width) (position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  BuilderLiteralListSearch.finalOutside (excludeBoundedPairClause first second) position
    (prepareOutside first.val second.val position outside)
def initialConfiguration (first second position : Nat) (retained older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues first second position retained older) inside outside)
def finalConfiguration {width : Nat} (first second : Fin width) (position : Nat) (retained older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderLiteralListSearch.finalConfiguration (excludeBoundedPairClause first second) position
      (initialValues first.val second.val position retained older) inside
      (prepareOutside first.val second.val position outside))
def observe (configuration : WorkConfiguration) : Option CNFToken :=
  if configuration.state = WorkMachineChain.secondState 0 then some .t
  else if configuration.state = WorkMachineChain.secondState 1 then some .f else none

theorem prepare_workRunExact {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine (prepareSteps first.val second.val position retained hRetained)
      (workStartConfiguration prepareMachine
        (endTape (initialValues first.val second.val position retained older) inside outside)) =
      some {state := prepareMachine.acceptState,
            tape := endTape (BuilderLiteralListSearch.initialValues (excludeBoundedPairClause first second) position
              (initialValues first.val second.val position retained older)) inside
              (prepareOutside first.val second.val position outside)} := by
  have h := BuilderRegisterPack.workRunExact fields 0 older
    (environment first.val second.val position retained hRetained) [] inside outside rfl
  simp only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    List.append_nil] at h
  rw [lookup_layout first second position retained older hRetained] at h
  simp only [environment_values, packed_values] at h
  exact h

private theorem chain_result (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle : WorkTape) (final : WorkConfiguration)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) = some final) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some (renameConfiguration WorkMachineChain.secondState final) :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

theorem workRunExact {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps first second position retained hRetained)
      (initialConfiguration first.val second.val position retained older inside outside) =
      some (finalConfiguration first second position retained older inside outside) := by
  have hPrepare := prepare_workRunExact first second position retained older hRetained inside outside
  have hSelect := BuilderLiteralListSearch.workRunExact (excludeBoundedPairClause first second) position
    (initialValues first.val second.val position retained older) inside (prepareOutside first.val second.val position outside)
  exact chain_result prepareMachine BuilderLiteralListSearch.machine _ _ _ _ _ hPrepare hSelect

theorem run_compile_exact {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps first second position retained hRetained)
      (encodeWorkConfiguration (initialConfiguration first.val second.val position retained older inside outside)) =
      encodeWorkConfiguration (finalConfiguration first second position retained older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact first second position retained older hRetained inside outside)

theorem observe_renamed (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderLiteralListSearch.observe configuration := by
  have hZero : WorkMachineChain.secondState configuration.state = WorkMachineChain.secondState 0 ↔ configuration.state = 0 :=
    ⟨fun h => WorkMachineChain.secondState_injective h, fun h => congrArg WorkMachineChain.secondState h⟩
  have hOne : WorkMachineChain.secondState configuration.state = WorkMachineChain.secondState 1 ↔ configuration.state = 1 :=
    ⟨fun h => WorkMachineChain.secondState_injective h, fun h => congrArg WorkMachineChain.secondState h⟩
  simp only [observe, renameConfiguration, BuilderLiteralListSearch.observe, BuilderLiteralTokenSelector.observe, hZero, hOne]

theorem canonical_result {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration first second position retained older inside outside) =
      (encodeLiteralListTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  rw [finalConfiguration, observe_renamed, BuilderLiteralListSearch.canonical_result,
    DirectToken.boundedLiteralListSlot_eq_getElem?]

theorem workRun_observes_encoding {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    observe (workRun machine (workSteps first second position retained hRetained)
      (initialConfiguration first.val second.val position retained older inside outside)) =
      (encodeLiteralListTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact first second position retained older hRetained inside outside)]
  exact canonical_result first second position retained older inside outside

theorem final_tape {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).tape =
      endTape (finalValues first second position retained older) inside (finalOutside first second position outside) :=
  BuilderLiteralListSearch.final_tape _ _ _ _ _

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct _ _
    (BuilderRegisterPack.rules_pairwise_query_distinct fields 0)
    BuilderLiteralListSearch.rules_pairwise_query_distinct
    (BuilderRegisterPack.noRuleAtAccept fields 0)
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineChain.noRuleAtAccept _ _ BuilderLiteralListSearch.noRuleAtAccept
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineChain.noRuleAtAccept prepareMachine
    {BuilderLiteralListSearch.machine with acceptState := BuilderLiteralListSearch.machine.rejectState}
    BuilderLiteralListSearch.noRuleAtReject
theorem noRuleAtPadding : WorkMachineProgramGraph.NoRuleAt machine (WorkMachineChain.secondState 2) :=
  WorkMachineChain.noRuleAtAccept prepareMachine {BuilderLiteralListSearch.machine with acceptState := 2}
    BuilderLiteralListSearch.noRuleAtPadding
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _ BuilderLiteralListSearch.acceptState_ne_rejectState

def preparedSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.spanPolynomial fields bound) bound
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderLiteralListSearchBounds.spanPolynomial (preparedSpanPolynomial bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterPack.rawTimePolynomial fields bound) (.constant 6))
    (BuilderLiteralListSearchBounds.rawTimePolynomial (preparedSpanPolynomial bound))

theorem source_polynomial_bounds {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first.val second.val position retained older)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (finalValues first second position retained older)).length +
        (finalOutside first second position outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps first second position retained hRetained ≤ (rawTimePolynomial bound).eval input := by
  have hInput : (registerWord (older ++
      List.ofFn (environment first.val second.val position retained hRetained) ++ [])).length ≤ bound.eval input := by
    simp only [environment_values, List.append_nil]
    change (registerWord (initialValues first.val second.val position retained older)).length ≤ _
    omega
  have hPack := BuilderRegisterPack.source_polynomial_bounds fields bound input older
    (environment first.val second.val position retained hRetained) [] hInput
  have hPacked : (registerWord (BuilderLiteralListSearch.initialValues (excludeBoundedPairClause first second) position
      (initialValues first.val second.val position retained older))).length ≤
        (BuilderRegisterPack.spanPolynomial fields bound).eval input := by
    simpa only [List.append_nil, lookup_layout first second position retained older hRetained] using hPack.1
  have hOutside : (prepareOutside first.val second.val position outside).length ≤ outside.length := by
    simp only [prepareOutside, List.length_drop]
    omega
  have hLookup : (registerWord (BuilderLiteralListSearch.initialValues (excludeBoundedPairClause first second) position
      (initialValues first.val second.val position retained older))).length +
        (prepareOutside first.val second.val position outside).length ≤ (preparedSpanPolynomial bound).eval input := by
    simp only [preparedSpanPolynomial, NatPolynomial.eval_add]
    omega
  have hSearch := BuilderLiteralListSearchBounds.source_polynomial_bounds
    (excludeBoundedPairClause first second) position
    (initialValues first.val second.val position retained older) (prepareOutside first.val second.val position outside)
    (preparedSpanPolynomial bound) input hLookup
  constructor
  · exact hSearch.1
  · have hPackTime := hPack.2
    have hSearchTime := hSearch.2
    simp only [workSteps, prepareSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem uniform_polynomial_lookup {width : Nat} (first second : Fin width) (position : Nat)
    (retained older : List Nat) (hRetained : retained.length = 11) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first.val second.val position retained older)).length +
      outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration first.val second.val position retained older inside outside)) =
        encodeWorkConfiguration (finalConfiguration first second position retained older inside outside) ∧
      observe (finalConfiguration first second position retained older inside outside) =
        (encodeLiteralListTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  have hBound := source_polynomial_bounds first second position retained older hRetained outside bound input hSpan
  exact ⟨6 * workSteps first second position retained hRetained, hBound.2,
    run_compile_exact first second position retained older hRetained inside outside,
    canonical_result first second position retained older inside outside⟩

/-- The fourteen-register source frame is exactly the existing reader output
followed by a physical body-position register. No reader address is changed. -/
theorem reader_output_frame (payload older history : List Nat) (row : Fin 9 → Nat)
    (first second position : Nat) :
    initialValues first second position (BuilderExclusionPairSecondVariable.scratch row)
      (BuilderExclusionPairFirstVariable.initialValues payload older history row ++
        BuilderExclusionPairFirstVariable.scratch row) =
      BuilderExclusionPairSecondVariable.finalValues payload older history row first second ++ [position] := by
  simp only [initialValues, frame, BuilderExclusionPairSecondVariable.finalValues,
    BuilderExclusionPairSecondVariable.initialValues, BuilderExclusionPairSecondVariable.firstHistory,
    List.append_assoc, List.cons_append, List.nil_append]

theorem reader_body_lookup {width : Nat} (first second : Fin width) (position : Nat)
    (payload older history : List Nat) (row : Fin 9 → Nat) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderExclusionPairSecondVariable.finalValues
      payload older history row first.val second.val ++ [position])).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration machine
          (endTape (BuilderExclusionPairSecondVariable.finalValues
            payload older history row first.val second.val ++ [position]) inside outside))) =
        encodeWorkConfiguration (finalConfiguration first second position
          (BuilderExclusionPairSecondVariable.scratch row)
          (BuilderExclusionPairFirstVariable.initialValues payload older history row ++
            BuilderExclusionPairFirstVariable.scratch row) inside outside) ∧
      observe (finalConfiguration first second position (BuilderExclusionPairSecondVariable.scratch row)
        (BuilderExclusionPairFirstVariable.initialValues payload older history row ++
          BuilderExclusionPairFirstVariable.scratch row) inside outside) =
        (encodeLiteralListTokens (BoundedClause.emit (excludeBoundedPairClause first second)))[position]? := by
  let prior := BuilderExclusionPairFirstVariable.initialValues payload older history row ++
    BuilderExclusionPairFirstVariable.scratch row
  have hInput : (registerWord (initialValues first.val second.val position
      (BuilderExclusionPairSecondVariable.scratch row) prior)).length + outside.length ≤ bound.eval input := by
    simpa only [prior, reader_output_frame] using hSpan
  have h := uniform_polynomial_lookup first second position (BuilderExclusionPairSecondVariable.scratch row) prior
    (BuilderExclusionPairSecondVariable.scratch_length row) inside outside bound input hInput
  simpa only [initialConfiguration, prior, reader_output_frame] using h

end PNP.Concrete.CookLevin.BuilderExclusionPairLiteralTokens
