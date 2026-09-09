/-
Copyright (c) 2026 PNP Labs.

Physical token selection for every indexed literal in an actual canonical list.
The ordinal and token position are read from registers. Two runtime field reads
and a fixed pack produce the selector arguments; no literal or verdict generates
control. True, false and padding remain distinct through sequential composition.

The full variable-width list locator, ordered-pair coordinate derivation and
source-bound formula builder remain separate required construction edges.
-/

import PNP.Concrete.CookLevinBuilderPayloadFieldCopy
import PNP.Concrete.CookLevinBuilderRegisterPack
import PNP.Concrete.CookLevinBuilderLiteralTokenSelector

namespace PNP.Concrete.CookLevin.BuilderIndexedLiteralTokenSelector

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues signValue)
open PipelineStateNamespace (renameConfiguration)

def valueHistory (ordinal value : Nat) : List Nat :=
  BuilderPayloadFieldCopy.scratch 2 1 1 ordinal ++ [value]
def signHistory (ordinal : Nat) (positive : Bool) : List Nat :=
  BuilderPayloadFieldCopy.scratch 2 0 7 ordinal ++ [signValue positive]
def afterValue (ordinal position value : Nat) : List Nat := [position] ++ valueHistory ordinal value
def history (ordinal position : Nat) (positive : Bool) (value : Nat) : List Nat :=
  [ordinal] ++ afterValue ordinal position value ++ signHistory ordinal positive

def argumentEnvironment (ordinal position : Nat) (positive : Bool) (value : Nat) (index : Fin 14) : Nat :=
  match index.val with
  | 0 => ordinal
  | 1 => position
  | 2 | 8 => 2
  | 3 | 9 => ordinal
  | 4 | 10 => 2 * ordinal
  | 5 => 7
  | 6 => 2 * ordinal + 7
  | 7 => value
  | 11 => 12
  | 12 => 2 * ordinal + 12
  | _ => signValue positive

def argumentFields : List (BuilderRegisterPack.Field 14) :=
  [.argument ⟨13, by decide⟩, .argument ⟨7, by decide⟩, .argument ⟨1, by decide⟩]

theorem valueHistory_length (ordinal value : Nat) : (valueHistory ordinal value).length = 6 := rfl
theorem afterValue_length (ordinal position value : Nat) : (afterValue ordinal position value).length = 7 := rfl
theorem history_length (ordinal position : Nat) (positive : Bool) (value : Nat) :
    (history ordinal position positive value).length = 14 := rfl
theorem environment_values (ordinal position : Nat) (positive : Bool) (value : Nat) :
    List.ofFn (argumentEnvironment ordinal position positive value) = history ordinal position positive value := rfl
theorem packed_values (ordinal position : Nat) (positive : Bool) (value : Nat) :
    BuilderRegisterPack.values argumentFields (argumentEnvironment ordinal position positive value) =
      BuilderLiteralTokenSelector.frame positive value position := rfl

def prepareMachine : WorkMachine :=
  WorkMachineChain.machine (BuilderPayloadFieldCopy.machine 2 1 1)
    (WorkMachineChain.machine (BuilderPayloadFieldCopy.machine 2 0 7)
      (BuilderRegisterPack.machine argumentFields 0))
def machine : WorkMachine := WorkMachineChain.machine prepareMachine BuilderLiteralTokenSelector.machine

def prepareSteps (payload : List Nat) (ordinal position : Nat) (positive : Bool) (value : Nat) : Nat :=
  BuilderPayloadFieldCopy.workSteps 2 1 1 ordinal [position] payload value + 1 +
    (BuilderPayloadFieldCopy.workSteps 2 0 7 ordinal (afterValue ordinal position value) payload (signValue positive) + 1 +
      BuilderRegisterPack.workSteps argumentFields (argumentEnvironment ordinal position positive value) [])

def workSteps (payload : List Nat) (ordinal position : Nat) (positive : Bool) (value : Nat) : Nat :=
  prepareSteps payload ordinal position positive value + 1 + BuilderLiteralTokenSelector.workSteps positive value position

def valueOutside (ordinal value : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop (BuilderPayloadFieldCopy.allocation 2 1 1 ordinal value)
def signOutside (ordinal value : Nat) (positive : Bool) (outside : List WorkSymbol) : List WorkSymbol :=
  (valueOutside ordinal value outside).drop (BuilderPayloadFieldCopy.allocation 2 0 7 ordinal (signValue positive))
def prepareOutside (ordinal position : Nat) (positive : Bool) (value : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (signOutside ordinal value positive outside).drop (registerWord (BuilderLiteralTokenSelector.frame positive value position)).length

def initialValues (payload older : List Nat) (ordinal position : Nat) : List Nat :=
  older ++ payload.reverse ++ [ordinal, position]
def prepareOlder (payload older : List Nat) (ordinal position : Nat) (positive : Bool) (value : Nat) : List Nat :=
  older ++ payload.reverse ++ history ordinal position positive value
def prepareTape (payload older : List Nat) (ordinal position : Nat) (positive : Bool) (value : Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  endTape (prepareOlder payload older ordinal position positive value ++ BuilderLiteralTokenSelector.frame positive value position)
    inside (prepareOutside ordinal position positive value outside)

def initialConfiguration (payload older : List Nat) (ordinal position : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues payload older ordinal position) inside outside)
def finalConfiguration (payload older : List Nat) (ordinal position : Nat) (positive : Bool) (value : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderLiteralTokenSelector.finalConfiguration positive value position
      (prepareOlder payload older ordinal position positive value) inside (prepareOutside ordinal position positive value outside))

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

/-- The complete operand preparation reads both fields from the actual list. -/
theorem prepare_workRunExact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine
      (prepareSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val)
      (workStartConfiguration prepareMachine (endTape (initialValues (literalListValues literals) older index.val position) inside outside)) =
      some {state := prepareMachine.acceptState,
            tape := prepareTape (literalListValues literals) older index.val position
              literals[index.val].positive literals[index.val].index.val inside outside} := by
  let positive := literals[index.val].positive
  let value := literals[index.val].index.val
  let payload := literalListValues literals
  have hValue := BuilderPayloadFieldCopy.workRun_literal_field literals index ⟨1, by decide⟩ 1 older [position] inside outside rfl
  have hSign := BuilderPayloadFieldCopy.workRun_literal_field literals index ⟨0, by decide⟩ 7 older
    (afterValue index.val position value) inside (valueOutside index.val value outside) (afterValue_length _ _ _)
  have hPack := BuilderRegisterPack.workRunExact argumentFields 0 (older ++ payload.reverse)
    (argumentEnvironment index.val position positive value) [] inside (signOutside index.val value positive outside) rfl
  have hLast : workRunExact? (BuilderRegisterPack.machine argumentFields 0)
      (BuilderRegisterPack.workSteps argumentFields (argumentEnvironment index.val position positive value) [])
      (workStartConfiguration (BuilderRegisterPack.machine argumentFields 0)
        (endTape (prepareOlder payload older index.val position positive value) inside (signOutside index.val value positive outside))) =
      some {state := (BuilderRegisterPack.machine argumentFields 0).acceptState,
            tape := prepareTape payload older index.val position positive value inside outside} := by
    simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
      environment_values, packed_values, List.append_nil, prepareOlder, prepareTape, prepareOutside] using hPack
  have hSecond : workRunExact? (BuilderPayloadFieldCopy.machine 2 0 7)
      (BuilderPayloadFieldCopy.workSteps 2 0 7 index.val (afterValue index.val position value) payload (signValue positive))
      (workStartConfiguration (BuilderPayloadFieldCopy.machine 2 0 7)
        (endTape (BuilderPayloadFieldCopy.initialValues payload older index.val (afterValue index.val position value))
          inside (valueOutside index.val value outside))) =
      some {state := (BuilderPayloadFieldCopy.machine 2 0 7).acceptState,
            tape := endTape (prepareOlder payload older index.val position positive value)
              inside (signOutside index.val value positive outside)} := by
    simpa only [BuilderPayloadFieldCopy.initialConfiguration, BuilderPayloadFieldCopy.finalConfiguration,
      BuilderPayloadFieldCopy.finalValues, BuilderPayloadFieldCopy.initialValues, BuilderPayloadFieldCopy.literalField,
      ite_true, signOutside, prepareOlder, history, signHistory, payload, positive, value, List.append_assoc] using hSign
  have hRest := chain_run _ _ _ _ _ _ _ hSecond hLast
  have hFirst : workRunExact? (BuilderPayloadFieldCopy.machine 2 1 1)
      (BuilderPayloadFieldCopy.workSteps 2 1 1 index.val [position] payload value)
      (workStartConfiguration (BuilderPayloadFieldCopy.machine 2 1 1)
        (endTape (initialValues payload older index.val position) inside outside)) =
      some {state := (BuilderPayloadFieldCopy.machine 2 1 1).acceptState,
            tape := endTape (BuilderPayloadFieldCopy.initialValues payload older index.val (afterValue index.val position value))
              inside (valueOutside index.val value outside)} := by
    simpa only [BuilderPayloadFieldCopy.initialConfiguration, BuilderPayloadFieldCopy.finalConfiguration,
      BuilderPayloadFieldCopy.finalValues, BuilderPayloadFieldCopy.initialValues, BuilderPayloadFieldCopy.literalField,
      Nat.one_ne_zero, ite_false, valueOutside, initialValues, afterValue, valueHistory, payload, value,
      List.append_assoc, List.cons_append, List.nil_append] using hValue
  have h := chain_run _ _ _ _ _ _ _ hFirst hRest
  exact h

theorem workRunExact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine
      (workSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val)
      (initialConfiguration (literalListValues literals) older index.val position inside outside) =
      some (finalConfiguration (literalListValues literals) older index.val position
        literals[index.val].positive literals[index.val].index.val inside outside) := by
  have hPrepare := prepare_workRunExact literals index position older inside outside
  have hSelect := BuilderLiteralTokenSelector.workRunExact literals[index.val].positive literals[index.val].index.val position
    (prepareOlder (literalListValues literals) older index.val position literals[index.val].positive literals[index.val].index.val)
    inside (prepareOutside index.val position literals[index.val].positive literals[index.val].index.val outside)
  have h := WorkMachineChain.workRunExact _ _ _ _ _ _ _ hPrepare rfl hSelect
  have hInitial (tape : WorkTape) :
      renameConfiguration WorkMachineChain.firstState (workStartConfiguration prepareMachine tape) =
        workStartConfiguration machine tape := rfl
  rw [hInitial] at h
  exact h

theorem run_compile_exact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine)
      (6 * workSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val)
      (encodeWorkConfiguration (initialConfiguration (literalListValues literals) older index.val position inside outside)) =
      encodeWorkConfiguration (finalConfiguration (literalListValues literals) older index.val position
        literals[index.val].positive literals[index.val].index.val inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact literals index position older inside outside)

theorem observe_renamed (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderLiteralTokenSelector.observe configuration := by
  have hZero : WorkMachineChain.secondState configuration.state = WorkMachineChain.secondState 0 ↔ configuration.state = 0 :=
    ⟨fun h => WorkMachineChain.secondState_injective h, fun h => congrArg WorkMachineChain.secondState h⟩
  have hOne : WorkMachineChain.secondState configuration.state = WorkMachineChain.secondState 1 ↔ configuration.state = 1 :=
    ⟨fun h => WorkMachineChain.secondState_injective h, fun h => congrArg WorkMachineChain.secondState h⟩
  simp only [observe, renameConfiguration, BuilderLiteralTokenSelector.observe, hZero, hOne]

theorem canonical_result {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration (literalListValues literals) older index.val position
      literals[index.val].positive literals[index.val].index.val inside outside) =
      DirectToken.literalSlot literals[index.val].emit position := by
  rw [finalConfiguration, observe_renamed, BuilderLiteralTokenSelector.canonical_result]
  rfl

theorem workRun_observes_literal {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    observe (workRun machine
      (workSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val)
      (initialConfiguration (literalListValues literals) older index.val position inside outside)) =
      DirectToken.literalSlot literals[index.val].emit position := by
  rw [workRun_eq_of_workRunExact _ _ _ _ (workRunExact literals index position older inside outside)]
  exact canonical_result literals index position older inside outside

theorem final_tape (payload older : List Nat) (ordinal position : Nat) (positive : Bool) (value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older ordinal position positive value inside outside).tape =
      endTape (BuilderLiteralTokenSelector.finalValues positive value position (prepareOlder payload older ordinal position positive value))
        inside (BuilderLiteralTokenSelector.finalOutside positive value position (prepareOutside ordinal position positive value outside)) := rfl

theorem original_frame_preserved (payload older : List Nat) (ordinal position : Nat) (positive : Bool) (value : Nat) :
    ∃ scratch, BuilderLiteralTokenSelector.finalValues positive value position (prepareOlder payload older ordinal position positive value) =
      initialValues payload older ordinal position ++ scratch := by
  refine ⟨valueHistory ordinal value ++ signHistory ordinal positive ++
    BuilderLiteralTokenSelector.frame positive value position ++
      (if position = 0 then [] else BuilderRegisterCompareResidual.outputValues (BuilderLiteralTokenSelector.comparisonResult value position)), ?_⟩
  simp only [BuilderLiteralTokenSelector.finalValues, prepareOlder, initialValues, history, afterValue,
    List.append_assoc, List.cons_append, List.nil_append]

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

private theorem field_good (slot count : Nat) : Good (BuilderPayloadFieldCopy.machine 2 slot count) :=
  ⟨BuilderPayloadFieldCopy.rules_pairwise_query_distinct _ _ _, BuilderPayloadFieldCopy.noRuleAtAccept _ _ _,
   BuilderPayloadFieldCopy.noRuleAtReject _ _ _, BuilderPayloadFieldCopy.acceptState_ne_rejectState _ _ _⟩
private theorem pack_good : Good (BuilderRegisterPack.machine argumentFields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct _ _, BuilderRegisterPack.noRuleAtAccept _ _,
   BuilderRegisterPack.noRuleAtReject _ _, BuilderRegisterPack.acceptState_ne_rejectState _ _⟩
private theorem prepare_good : Good prepareMachine := chain_good _ _ (field_good 1 1) (chain_good _ _ (field_good 0 7) pack_good)
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

def valueSpanPolynomial (bound : NatPolynomial) : NatPolynomial := BuilderPayloadFieldCopy.spanPolynomial 2 1 1 bound
def signSpanPolynomial (bound : NatPolynomial) : NatPolynomial := BuilderPayloadFieldCopy.spanPolynomial 2 0 7 (valueSpanPolynomial bound)
def prepareSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.spanPolynomial argumentFields (signSpanPolynomial bound)) (signSpanPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := BuilderLiteralTokenSelector.spanPolynomial (prepareSpanPolynomial bound)
def prepareRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderPayloadFieldCopy.rawTimePolynomial 2 1 1 bound) (.constant 6))
    (.add (.add (BuilderPayloadFieldCopy.rawTimePolynomial 2 0 7 (valueSpanPolynomial bound)) (.constant 6))
      (BuilderRegisterPack.rawTimePolynomial argumentFields (signSpanPolynomial bound)))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (prepareRawTimePolynomial bound) (.constant 6))
    (BuilderLiteralTokenSelector.rawTimePolynomial (prepareSpanPolynomial bound))

theorem prepare_source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older index.val position)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder (literalListValues literals) older index.val position literals[index.val].positive literals[index.val].index.val ++
      BuilderLiteralTokenSelector.frame literals[index.val].positive literals[index.val].index.val position)).length +
      (prepareOutside index.val position literals[index.val].positive literals[index.val].index.val outside).length ≤
      (prepareSpanPolynomial bound).eval input ∧
    6 * prepareSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val ≤
      (prepareRawTimePolynomial bound).eval input := by
  let positive := literals[index.val].positive
  let value := literals[index.val].index.val
  let payload := literalListValues literals
  have hInitial : (registerWord (BuilderPayloadFieldCopy.initialValues payload older index.val [position])).length +
      outside.length ≤ bound.eval input := by
    simpa only [BuilderPayloadFieldCopy.initialValues, initialValues, List.append_assoc, List.cons_append, List.nil_append] using hSpan
  have hValue := BuilderPayloadFieldCopy.literal_source_polynomial_bounds literals index ⟨1, by decide⟩ 1 older [position]
    outside bound input rfl hInitial
  have hAfterValue : (registerWord (BuilderPayloadFieldCopy.initialValues payload older index.val (afterValue index.val position value))).length +
      (valueOutside index.val value outside).length ≤ (valueSpanPolynomial bound).eval input := by
    simpa only [BuilderPayloadFieldCopy.finalValues, BuilderPayloadFieldCopy.initialValues, BuilderPayloadFieldCopy.literalField,
      Nat.one_ne_zero, ite_false, valueOutside, valueSpanPolynomial, afterValue, valueHistory, payload, value,
      List.append_assoc, List.cons_append, List.nil_append] using hValue.1
  have hSign := BuilderPayloadFieldCopy.literal_source_polynomial_bounds literals index ⟨0, by decide⟩ 7 older
    (afterValue index.val position value) (valueOutside index.val value outside) (valueSpanPolynomial bound) input
    (afterValue_length _ _ _) hAfterValue
  have hAfterSign : (registerWord (prepareOlder payload older index.val position positive value)).length +
      (signOutside index.val value positive outside).length ≤ (signSpanPolynomial bound).eval input := by
    simpa only [BuilderPayloadFieldCopy.finalValues, BuilderPayloadFieldCopy.initialValues, BuilderPayloadFieldCopy.literalField,
      ite_true, signOutside, signSpanPolynomial, prepareOlder, history, signHistory, payload, positive, value, List.append_assoc] using hSign.1
  have hPackInput : (registerWord ((older ++ payload.reverse) ++ List.ofFn (argumentEnvironment index.val position positive value) ++ [])).length ≤
      (signSpanPolynomial bound).eval input := by
    rw [environment_values, List.append_nil]
    exact Nat.le_trans (Nat.le_add_right _ _) hAfterSign
  have hPack := BuilderRegisterPack.source_polynomial_bounds argumentFields (signSpanPolynomial bound) input
    (older ++ payload.reverse) (argumentEnvironment index.val position positive value) [] hPackInput
  simp only [environment_values, packed_values, List.append_nil] at hPack
  constructor
  · simp only [prepareSpanPolynomial, NatPolynomial.eval_add, prepareOutside, List.length_drop]
    change (registerWord ((older ++ payload.reverse ++ history index.val position positive value) ++ BuilderLiteralTokenSelector.frame positive value position)).length +
      ((signOutside index.val value positive outside).length - (registerWord (BuilderLiteralTokenSelector.frame positive value position)).length) ≤ _
    have hExterior : (signOutside index.val value positive outside).length ≤ (signSpanPolynomial bound).eval input := by omega
    omega
  · have hValueTime := hValue.2
    have hSignTime := hSign.2
    simp only [BuilderPayloadFieldCopy.literalField, Nat.one_ne_zero, ite_false, ite_true] at hValueTime hSignTime
    simp only [prepareSteps, prepareRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    dsimp only [positive, value, payload] at hPack hValueTime hSignTime ⊢
    omega

theorem source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older index.val position)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (BuilderLiteralTokenSelector.finalValues literals[index.val].positive literals[index.val].index.val position
      (prepareOlder (literalListValues literals) older index.val position literals[index.val].positive literals[index.val].index.val))).length +
      (BuilderLiteralTokenSelector.finalOutside literals[index.val].positive literals[index.val].index.val position
        (prepareOutside index.val position literals[index.val].positive literals[index.val].index.val outside)).length ≤
      (spanPolynomial bound).eval input ∧
    6 * workSteps (literalListValues literals) index.val position literals[index.val].positive literals[index.val].index.val ≤
      (rawTimePolynomial bound).eval input := by
  have hPrepare := prepare_source_polynomial_bounds literals index position older outside bound input hSpan
  have hSelect := BuilderLiteralTokenSelector.source_polynomial_bounds literals[index.val].positive literals[index.val].index.val position
    (prepareOlder (literalListValues literals) older index.val position literals[index.val].positive literals[index.val].index.val)
    (prepareOutside index.val position literals[index.val].positive literals[index.val].index.val outside)
    (prepareSpanPolynomial bound) input hPrepare.1
  constructor
  · exact hSelect.1
  · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderIndexedLiteralTokenSelector
