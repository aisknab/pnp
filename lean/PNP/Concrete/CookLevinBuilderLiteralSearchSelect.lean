/-
Copyright (c) 2026 PNP Labs.

Select the literal token after the complete-width comparison has found a hit.
The sign is physically read through the retained comparison history; fixed
argument addresses copy that sign, the actual variable index and token position.
Padding remains a distinct outcome outside the proved hit domain. The cyclic
locator must establish the hit premise using its physical comparison branch.
-/

import PNP.Concrete.CookLevinBuilderLiteralSearchAdvance
import PNP.Concrete.CookLevinBuilderLiteralTokenSelector

namespace PNP.Concrete.CookLevin.BuilderLiteralSearchSelect

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues signValue)
open BuilderLiteralSearchFrame (fieldStride valueHistory widthHistory chunk comparisonHistory comparisonResult residual)
open BuilderLiteralSearchAdvance (ordinalSuffix ordinalSuffix_length chunk_ordinal)
open PipelineStateNamespace (renameConfiguration)

def signHistory (ordinal : Nat) (positive : Bool) : List Nat :=
  BuilderPayloadFieldCopy.scratch fieldStride 0 16 ordinal ++ [signValue positive]
def history (ordinal count position value : Nat) (positive : Bool) : List Nat :=
  chunk ordinal count position value ++ signHistory ordinal positive
def argumentEnvironment (ordinal count position value : Nat) (positive : Bool) (index : Fin 23) : Nat :=
  match index.val with
  | 0 => ordinal
  | 1 => count
  | 2 => position
  | 3 | 17 => fieldStride
  | 4 | 18 => ordinal
  | 5 | 19 => fieldStride * ordinal
  | 6 => 8
  | 7 => fieldStride * ordinal + 8
  | 8 | 9 => value
  | 10 => 2
  | 11 | 15 => value + 2
  | 12 => BuilderRegisterCompareResidual.environment (comparisonResult position value) ⟨0, by decide⟩
  | 13 => BuilderRegisterCompareResidual.environment (comparisonResult position value) ⟨1, by decide⟩
  | 14 => BuilderRegisterCompareResidual.environment (comparisonResult position value) ⟨2, by decide⟩
  | 16 => residual position value
  | 20 => 21
  | 21 => fieldStride * ordinal + 21
  | _ => signValue positive
def argumentFields : List (BuilderRegisterPack.Field 23) :=
  [.argument ⟨22, by decide⟩, .argument ⟨8, by decide⟩, .argument ⟨2, by decide⟩]

theorem signHistory_length (ordinal : Nat) (positive : Bool) : (signHistory ordinal positive).length = 6 := rfl
theorem history_length (ordinal count position value : Nat) (positive : Bool) :
    (history ordinal count position value positive).length = 23 := by
  simp only [history, List.length_append, BuilderLiteralSearchFrame.chunk_length,
    signHistory_length, BuilderLiteralSearchFrame.historyStride]
theorem environment_values (ordinal count position value : Nat) (positive : Bool) :
    List.ofFn (argumentEnvironment ordinal count position value positive) =
      history ordinal count position value positive := by
  have hRestored :
      [BuilderRegisterCompareResidual.environment (comparisonResult position value) ⟨0, by decide⟩,
       BuilderRegisterCompareResidual.environment (comparisonResult position value) ⟨1, by decide⟩,
       BuilderRegisterCompareResidual.environment (comparisonResult position value) ⟨2, by decide⟩] =
        BuilderRegisterLessThan.resultValues (comparisonResult position value) :=
    BuilderRegisterCompareResidual.environment_ofFn _
  simp only [comparisonResult] at hRestored
  simp only [history, chunk, comparisonHistory, BuilderRegisterCompareResidual.outputValues,
    comparisonResult, BuilderRegisterCompareResidual.resultBoundary_eq,
    BuilderRegisterCompareResidual.resultCoordinate_eq]
  rw [← hRestored]
  rfl
theorem packed_values (ordinal count position value : Nat) (positive : Bool) :
    BuilderRegisterPack.values argumentFields (argumentEnvironment ordinal count position value positive) =
      BuilderLiteralTokenSelector.frame positive value position := rfl

def prepareMachine : WorkMachine :=
  WorkMachineChain.machine (BuilderPayloadFieldCopy.machine fieldStride 0 16) (BuilderRegisterPack.machine argumentFields 0)
def machine : WorkMachine := WorkMachineChain.machine prepareMachine BuilderLiteralTokenSelector.machine
def prepareSteps (payload prior : List Nat) (ordinal count position value : Nat) (positive : Bool) : Nat :=
  BuilderPayloadFieldCopy.workSteps fieldStride 0 16 ordinal (ordinalSuffix ordinal count position value)
    (prior.reverse ++ payload) (signValue positive) + 1 +
      BuilderRegisterPack.workSteps argumentFields (argumentEnvironment ordinal count position value positive) []
def workSteps (payload prior : List Nat) (ordinal count position value : Nat) (positive : Bool) : Nat :=
  prepareSteps payload prior ordinal count position value positive + 1 +
    BuilderLiteralTokenSelector.workSteps positive value position
def signOutside (ordinal : Nat) (positive : Bool) (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop (BuilderPayloadFieldCopy.allocation fieldStride 0 16 ordinal (signValue positive))
def prepareOutside (ordinal position value : Nat) (positive : Bool) (outside : List WorkSymbol) : List WorkSymbol :=
  (signOutside ordinal positive outside).drop (registerWord (BuilderLiteralTokenSelector.frame positive value position)).length
def baseValues (payload older prior : List Nat) : List Nat := older ++ payload.reverse ++ prior
def initialValues (payload older prior : List Nat) (ordinal count position value : Nat) : List Nat :=
  baseValues payload older prior ++ chunk ordinal count position value
def prepareOlder (payload older prior : List Nat) (ordinal count position value : Nat) (positive : Bool) : List Nat :=
  baseValues payload older prior ++ history ordinal count position value positive
def prepareTape (payload older prior : List Nat) (ordinal count position value : Nat) (positive : Bool)
    (inside outside : List WorkSymbol) : WorkTape :=
  endTape (prepareOlder payload older prior ordinal count position value positive ++
    BuilderLiteralTokenSelector.frame positive value position) inside (prepareOutside ordinal position value positive outside)
def initialConfiguration (payload older prior : List Nat) (ordinal count position value : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues payload older prior ordinal count position value) inside outside)
def finalConfiguration (payload older prior : List Nat) (ordinal count position value : Nat) (positive : Bool)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderLiteralTokenSelector.finalConfiguration positive value position
      (prepareOlder payload older prior ordinal count position value positive) inside
      (prepareOutside ordinal position value positive outside))
def observe (configuration : WorkConfiguration) : Option CNFToken :=
  if configuration.state = WorkMachineChain.secondState 0 then some .t
  else if configuration.state = WorkMachineChain.secondState 1 then some .f else none

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem prepare_workRunExact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine
      (prepareSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive)
      (workStartConfiguration prepareMachine
        (endTape (initialValues (literalListValues literals) older prior index.val count position literals[index.val].index.val) inside outside)) =
      some {state := prepareMachine.acceptState,
            tape := prepareTape (literalListValues literals) older prior index.val count position
              literals[index.val].index.val literals[index.val].positive inside outside} := by
  let value := literals[index.val].index.val
  let positive := literals[index.val].positive
  let payload := literalListValues literals
  let base := baseValues payload older prior
  have hSign := BuilderLiteralSearchFrame.field_workRunExact literals index prior hPrior ⟨0, by decide⟩
    16 older (ordinalSuffix index.val count position value) (ordinalSuffix_length _ _ _ _) inside outside
  have hPack := BuilderRegisterPack.workRunExact argumentFields 0 base
    (argumentEnvironment index.val count position value positive) [] inside (signOutside index.val positive outside) rfl
  have hFirst : workRunExact? (BuilderPayloadFieldCopy.machine fieldStride 0 16)
      (BuilderPayloadFieldCopy.workSteps fieldStride 0 16 index.val (ordinalSuffix index.val count position value)
        (prior.reverse ++ payload) (signValue positive))
      (workStartConfiguration (BuilderPayloadFieldCopy.machine fieldStride 0 16)
        (endTape (initialValues payload older prior index.val count position value) inside outside)) =
      some {state := (BuilderPayloadFieldCopy.machine fieldStride 0 16).acceptState,
            tape := endTape (prepareOlder payload older prior index.val count position value positive)
              inside (signOutside index.val positive outside)} := by
    simpa only [BuilderPayloadFieldCopy.literalField, ite_true, BuilderLiteralSearchFrame.payloadReader,
      initialValues, prepareOlder, baseValues, history, chunk_ordinal, signHistory, signOutside,
      payload, positive, value, List.append_assoc] using hSign
  have hSecond : workRunExact? (BuilderRegisterPack.machine argumentFields 0)
      (BuilderRegisterPack.workSteps argumentFields (argumentEnvironment index.val count position value positive) [])
      (workStartConfiguration (BuilderRegisterPack.machine argumentFields 0)
        (endTape (prepareOlder payload older prior index.val count position value positive) inside
          (signOutside index.val positive outside))) =
      some {state := (BuilderRegisterPack.machine argumentFields 0).acceptState,
            tape := prepareTape payload older prior index.val count position value positive inside outside} := by
    simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
      environment_values, packed_values, List.append_nil, prepareOlder, prepareTape, prepareOutside, base] using hPack
  exact chain_run _ _ _ _ _ _ _ hFirst hSecond

theorem workRunExact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine
      (workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive)
      (initialConfiguration (literalListValues literals) older prior index.val count position literals[index.val].index.val inside outside) =
      some (finalConfiguration (literalListValues literals) older prior index.val count position
        literals[index.val].index.val literals[index.val].positive inside outside) := by
  have hPrepare := prepare_workRunExact literals index prior hPrior count position older inside outside
  have hSelect := BuilderLiteralTokenSelector.workRunExact literals[index.val].positive literals[index.val].index.val position
    (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val literals[index.val].positive)
    inside (prepareOutside index.val position literals[index.val].index.val literals[index.val].positive outside)
  have h := WorkMachineChain.workRunExact _ _ _ _ _ _ _ hPrepare rfl hSelect
  have hInitial (tape : WorkTape) :
      renameConfiguration WorkMachineChain.firstState (workStartConfiguration prepareMachine tape) =
        workStartConfiguration machine tape := rfl
  rw [hInitial] at h
  exact h

theorem run_compile_exact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine)
      (6 * workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive)
      (encodeWorkConfiguration (initialConfiguration (literalListValues literals) older prior index.val count position literals[index.val].index.val inside outside)) =
      encodeWorkConfiguration (finalConfiguration (literalListValues literals) older prior index.val count position
        literals[index.val].index.val literals[index.val].positive inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact literals index prior hPrior count position older inside outside)

theorem observe_renamed (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderLiteralTokenSelector.observe configuration := by
  have hZero : WorkMachineChain.secondState configuration.state = WorkMachineChain.secondState 0 ↔ configuration.state = 0 :=
    ⟨fun h => WorkMachineChain.secondState_injective h, fun h => congrArg WorkMachineChain.secondState h⟩
  have hOne : WorkMachineChain.secondState configuration.state = WorkMachineChain.secondState 1 ↔ configuration.state = 1 :=
    ⟨fun h => WorkMachineChain.secondState_injective h, fun h => congrArg WorkMachineChain.secondState h⟩
  simp only [observe, renameConfiguration, BuilderLiteralTokenSelector.observe, hZero, hOne]

theorem canonical_result {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior older : List Nat) (count position : Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration (literalListValues literals) older prior index.val count position
      literals[index.val].index.val literals[index.val].positive inside outside) =
      DirectToken.literalSlot literals[index.val].emit position := by
  rw [finalConfiguration, observe_renamed, BuilderLiteralTokenSelector.canonical_result]
  rfl

theorem workRun_observes_literal {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun machine
      (workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive)
      (initialConfiguration (literalListValues literals) older prior index.val count position literals[index.val].index.val inside outside)) =
      DirectToken.literalSlot literals[index.val].emit position := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact literals index prior hPrior count position older inside outside)]
  exact canonical_result literals index prior older count position inside outside

theorem hit_terminal (payload older prior : List Nat) (ordinal count position value : Nat) (positive : Bool)
    (inside outside : List WorkSymbol) (hHit : position < value + 2) :
    (finalConfiguration payload older prior ordinal count position value positive inside outside).state = machine.acceptState ∨
    (finalConfiguration payload older prior ordinal count position value positive inside outside).state = machine.rejectState := by
  have hEndpoint : BuilderLiteralTokenSelector.endpoint positive value position = .accept ∨
      BuilderLiteralTokenSelector.endpoint positive value position = .reject := by
    unfold BuilderLiteralTokenSelector.endpoint
    by_cases hZero : position = 0
    · rw [if_pos hZero]
      cases positive
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rw [if_neg hZero]
      unfold BuilderLiteralTokenSelector.unaryEndpoint
      by_cases hLess : position - 1 < value
      · rw [if_pos hLess]
        exact Or.inl rfl
      · have hEqual : position - 1 = value := by omega
        rw [if_neg hLess, if_pos hEqual]
        exact Or.inr rfl
  rcases hEndpoint with hAccept | hReject
  · left
    change WorkMachineChain.secondState
      (WorkMachineProgramGraph.endpointConfiguration (BuilderLiteralTokenSelector.endpoint positive value position) _).state =
        WorkMachineChain.secondState 0
    rw [hAccept]
    rfl
  · right
    change WorkMachineChain.secondState
      (WorkMachineProgramGraph.endpointConfiguration (BuilderLiteralTokenSelector.endpoint positive value position) _).state =
        WorkMachineChain.secondState 1
    rw [hReject]
    rfl

theorem final_tape (payload older prior : List Nat) (ordinal count position value : Nat) (positive : Bool)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count position value positive inside outside).tape =
      endTape (BuilderLiteralTokenSelector.finalValues positive value position
        (prepareOlder payload older prior ordinal count position value positive))
        inside (BuilderLiteralTokenSelector.finalOutside positive value position
          (prepareOutside ordinal position value positive outside)) := rfl

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧ program.acceptState ≠ program.rejectState
private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem field_good : Good (BuilderPayloadFieldCopy.machine fieldStride 0 16) :=
  ⟨BuilderPayloadFieldCopy.rules_pairwise_query_distinct _ _ _, BuilderPayloadFieldCopy.noRuleAtAccept _ _ _,
   BuilderPayloadFieldCopy.noRuleAtReject _ _ _, BuilderPayloadFieldCopy.acceptState_ne_rejectState _ _ _⟩
private theorem pack_good : Good (BuilderRegisterPack.machine argumentFields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct _ _, BuilderRegisterPack.noRuleAtAccept _ _,
   BuilderRegisterPack.noRuleAtReject _ _, BuilderRegisterPack.acceptState_ne_rejectState _ _⟩
private theorem prepare_good : Good prepareMachine := chain_good _ _ field_good pack_good
private theorem selector_good : Good BuilderLiteralTokenSelector.machine :=
  ⟨BuilderLiteralTokenSelector.rules_pairwise_query_distinct, BuilderLiteralTokenSelector.noRuleAtAccept,
   BuilderLiteralTokenSelector.noRuleAtReject, BuilderLiteralTokenSelector.acceptState_ne_rejectState⟩
private theorem good : Good machine := chain_good _ _ prepare_good selector_good

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct := good.1
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := good.2.2.2
theorem noRuleAtPadding : WorkMachineProgramGraph.NoRuleAt machine (WorkMachineChain.secondState 2) :=
  WorkMachineChain.noRuleAtAccept prepareMachine
    {BuilderLiteralTokenSelector.machine with acceptState := 2}
    (WorkMachineProgramGraph.noRuleAt_globalDead BuilderLiteralTokenSelector.graph)

def signSpanPolynomial (bound : NatPolynomial) : NatPolynomial := BuilderPayloadFieldCopy.spanPolynomial fieldStride 0 16 bound
def prepareSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.spanPolynomial argumentFields (signSpanPolynomial bound)) (signSpanPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := BuilderLiteralTokenSelector.spanPolynomial (prepareSpanPolynomial bound)
def prepareRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderPayloadFieldCopy.rawTimePolynomial fieldStride 0 16 bound) (.constant 6))
    (BuilderRegisterPack.rawTimePolynomial argumentFields (signSpanPolynomial bound))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (prepareRawTimePolynomial bound) (.constant 6))
    (BuilderLiteralTokenSelector.rawTimePolynomial (prepareSpanPolynomial bound))

theorem prepare_source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older prior index.val count position literals[index.val].index.val)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val literals[index.val].positive ++
      BuilderLiteralTokenSelector.frame literals[index.val].positive literals[index.val].index.val position)).length +
      (prepareOutside index.val position literals[index.val].index.val literals[index.val].positive outside).length ≤
      (prepareSpanPolynomial bound).eval input ∧
    6 * prepareSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive ≤
      (prepareRawTimePolynomial bound).eval input := by
  let value := literals[index.val].index.val
  let positive := literals[index.val].positive
  let payload := literalListValues literals
  let base := baseValues payload older prior
  have hInitial : (registerWord (older ++ (literalListValues literals).reverse ++ prior ++ [index.val] ++
      ordinalSuffix index.val count position value)).length + outside.length ≤ bound.eval input := by
    simpa only [initialValues, baseValues, chunk_ordinal, value, List.append_assoc] using hSpan
  have hSign := BuilderLiteralSearchFrame.field_source_polynomial_bounds literals index prior hPrior ⟨0, by decide⟩
    16 older (ordinalSuffix index.val count position value) (ordinalSuffix_length _ _ _ _) outside bound input hInitial
  have hAfterSign : (registerWord (prepareOlder payload older prior index.val count position value positive)).length +
      (signOutside index.val positive outside).length ≤ (signSpanPolynomial bound).eval input := by
    simpa only [BuilderPayloadFieldCopy.literalField, ite_true, prepareOlder, baseValues, history,
      chunk_ordinal, signHistory, signOutside, signSpanPolynomial, payload, positive, value, List.append_assoc] using hSign.1
  have hPackInput : (registerWord (base ++ List.ofFn (argumentEnvironment index.val count position value positive) ++ [])).length ≤
      (signSpanPolynomial bound).eval input := by
    rw [environment_values, List.append_nil]
    exact Nat.le_trans (Nat.le_add_right _ _) hAfterSign
  have hPack := BuilderRegisterPack.source_polynomial_bounds argumentFields (signSpanPolynomial bound) input base
    (argumentEnvironment index.val count position value positive) [] hPackInput
  simp only [environment_values, packed_values, List.append_nil] at hPack
  constructor
  · have hExterior : (signOutside index.val positive outside).length ≤ (signSpanPolynomial bound).eval input := by omega
    simp only [prepareSpanPolynomial, NatPolynomial.eval_add, prepareOutside, List.length_drop]
    change (registerWord ((base ++ history index.val count position value positive) ++
      BuilderLiteralTokenSelector.frame positive value position)).length +
      ((signOutside index.val positive outside).length - (registerWord (BuilderLiteralTokenSelector.frame positive value position)).length) ≤ _
    omega
  · have hSignTime := hSign.2
    simp only [BuilderPayloadFieldCopy.literalField, ite_true, BuilderLiteralSearchFrame.payloadReader] at hSignTime
    simp only [prepareSteps, prepareRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    dsimp only [positive, value, payload] at hPack hSignTime ⊢
    omega

theorem source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older prior index.val count position literals[index.val].index.val)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (BuilderLiteralTokenSelector.finalValues literals[index.val].positive literals[index.val].index.val position
      (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val literals[index.val].positive))).length +
      (BuilderLiteralTokenSelector.finalOutside literals[index.val].positive literals[index.val].index.val position
        (prepareOutside index.val position literals[index.val].index.val literals[index.val].positive outside)).length ≤
      (spanPolynomial bound).eval input ∧
    6 * workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val literals[index.val].positive ≤
      (rawTimePolynomial bound).eval input := by
  have hPrepare := prepare_source_polynomial_bounds literals index prior hPrior count position older outside bound input hSpan
  have hSelect := BuilderLiteralTokenSelector.source_polynomial_bounds literals[index.val].positive literals[index.val].index.val position
    (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val literals[index.val].positive)
    (prepareOutside index.val position literals[index.val].index.val literals[index.val].positive outside)
    (prepareSpanPolynomial bound) input hPrepare.1
  constructor
  · exact hSelect.1
  · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderLiteralSearchSelect
