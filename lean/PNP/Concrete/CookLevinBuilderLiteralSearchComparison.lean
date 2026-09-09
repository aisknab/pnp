/-
Copyright (c) 2026 PNP Labs.

Read the current literal's actual index through the accumulated search history,
construct its index-plus-two token width, and compare the runtime residual
position. One fixed sequential machine returns a hit or a miss with a usable
residual. Every argument is physically read or constructed, never supplied as a
selection verdict. The complete cyclic list locator remains to be composed.
-/

import PNP.Concrete.CookLevinBuilderLiteralSearchFrame
import PNP.Concrete.CookLevinBuilderRegisterPack

namespace PNP.Concrete.CookLevin.BuilderLiteralSearchComparison

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (literalListValues)
open BuilderLiteralSearchFrame (fieldStride valueHistory widthExpression widthHistory
  valueEnvironment valueEnvironment_values widthExpression_values chunk comparisonResult comparisonHistory)
open PipelineStateNamespace (renameConfiguration)

def packedEnvironment (ordinal count position value : Nat) (index : Fin 12) : Nat :=
  match index.val with
  | 0 => ordinal
  | 1 => count
  | 2 => position
  | 3 => fieldStride
  | 4 => ordinal
  | 5 => fieldStride * ordinal
  | 6 => 8
  | 7 => fieldStride * ordinal + 8
  | 8 | 9 => value
  | 10 => 2
  | _ => value + 2
def argumentFields : List (BuilderRegisterPack.Field 12) :=
  [.argument ⟨2, by decide⟩, .argument ⟨11, by decide⟩]
def preparationHistory (ordinal count position value : Nat) : List Nat :=
  [ordinal, count, position] ++ valueHistory ordinal value ++ widthHistory value

theorem environment_values (ordinal count position value : Nat) :
    List.ofFn (packedEnvironment ordinal count position value) =
      preparationHistory ordinal count position value := rfl
theorem packed_values (ordinal count position value : Nat) :
    BuilderRegisterPack.values argumentFields (packedEnvironment ordinal count position value) =
      [position, value + 2] := rfl
theorem preparationHistory_length (ordinal count position value : Nat) :
    (preparationHistory ordinal count position value).length = 12 := rfl
theorem chunk_eq (ordinal count position value : Nat) :
    chunk ordinal count position value =
      preparationHistory ordinal count position value ++ comparisonHistory position value := rfl

def prepareMachine : WorkMachine :=
  WorkMachineChain.machine (BuilderPayloadFieldCopy.machine fieldStride 1 2)
    (WorkMachineChain.machine (BuilderRegisterExpression.machine widthExpression 0)
      (BuilderRegisterPack.machine argumentFields 0))
def machine : WorkMachine := WorkMachineChain.machine prepareMachine BuilderRegisterCompareResidual.machine

def prepareSteps (payload prior : List Nat) (ordinal count position value : Nat) : Nat :=
  BuilderPayloadFieldCopy.workSteps fieldStride 1 2 ordinal [count, position]
    (prior.reverse ++ payload) value + 1 +
    (BuilderRegisterExpression.workSteps widthExpression (valueEnvironment ordinal count position value) [] + 1 +
      BuilderRegisterPack.workSteps argumentFields (packedEnvironment ordinal count position value) [])
def workSteps (payload prior : List Nat) (ordinal count position value : Nat) : Nat :=
  prepareSteps payload prior ordinal count position value + 1 +
    BuilderRegisterCompareResidual.workSteps position (value + 2)

def valueOutside (ordinal value : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop (BuilderPayloadFieldCopy.allocation fieldStride 1 2 ordinal value)
def widthOutside (ordinal value : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (valueOutside ordinal value outside).drop (registerWord (widthHistory value)).length
def prepareOutside (ordinal position value : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (widthOutside ordinal value outside).drop (registerWord [position, value + 2]).length
def finalOutside (ordinal position value : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (prepareOutside ordinal position value outside).drop
    (BuilderRegisterCompareResidual.allocatedCells (comparisonResult position value))

def baseValues (payload older prior : List Nat) : List Nat := older ++ payload.reverse ++ prior
def initialValues (payload older prior : List Nat) (ordinal count position : Nat) : List Nat :=
  baseValues payload older prior ++ [ordinal, count, position]
def prepareOlder (payload older prior : List Nat) (ordinal count position value : Nat) : List Nat :=
  baseValues payload older prior ++ preparationHistory ordinal count position value
def prepareTape (payload older prior : List Nat) (ordinal count position value : Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  endTape (prepareOlder payload older prior ordinal count position value ++ [position, value + 2])
    inside (prepareOutside ordinal position value outside)
def finalValues (payload older prior : List Nat) (ordinal count position value : Nat) : List Nat :=
  baseValues payload older prior ++ chunk ordinal count position value

def initialConfiguration (payload older prior : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues payload older prior ordinal count position) inside outside)
def finalConfiguration (payload older prior : List Nat) (ordinal count position value : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderRegisterCompareResidual.finalConfiguration position (value + 2)
      (prepareOlder payload older prior ordinal count position value) inside
      (prepareOutside ordinal position value outside))

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

/-- Derive both comparison operands from the actual list and current loop frame. -/
theorem prepare_workRunExact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine
      (prepareSteps (literalListValues literals) prior index.val count position literals[index.val].index.val)
      (workStartConfiguration prepareMachine
        (endTape (initialValues (literalListValues literals) older prior index.val count position) inside outside)) =
      some {state := prepareMachine.acceptState,
            tape := prepareTape (literalListValues literals) older prior index.val count position
              literals[index.val].index.val inside outside} := by
  let value := literals[index.val].index.val
  let payload := literalListValues literals
  let base := baseValues payload older prior
  have hField := BuilderLiteralSearchFrame.field_workRunExact literals index prior hPrior
    ⟨1, by decide⟩ 2 older [count, position] rfl inside outside
  have hWidth := BuilderRegisterExpression.workRunExact widthExpression 0 base
    (valueEnvironment index.val count position value) [] inside (valueOutside index.val value outside) rfl
  have hPack := BuilderRegisterPack.workRunExact argumentFields 0 base
    (packedEnvironment index.val count position value) [] inside (widthOutside index.val value outside) rfl
  have hLast : workRunExact? (BuilderRegisterPack.machine argumentFields 0)
      (BuilderRegisterPack.workSteps argumentFields (packedEnvironment index.val count position value) [])
      (workStartConfiguration (BuilderRegisterPack.machine argumentFields 0)
        (endTape (prepareOlder payload older prior index.val count position value) inside (widthOutside index.val value outside))) =
      some {state := (BuilderRegisterPack.machine argumentFields 0).acceptState,
            tape := prepareTape payload older prior index.val count position value inside outside} := by
    simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
      environment_values, packed_values, List.append_nil, prepareOlder, prepareTape, prepareOutside, base] using hPack
  have hSecond : workRunExact? (BuilderRegisterExpression.machine widthExpression 0)
      (BuilderRegisterExpression.workSteps widthExpression (valueEnvironment index.val count position value) [])
      (workStartConfiguration (BuilderRegisterExpression.machine widthExpression 0)
        (endTape (base ++ [index.val, count, position] ++ valueHistory index.val value) inside
          (valueOutside index.val value outside))) =
      some {state := (BuilderRegisterExpression.machine widthExpression 0).acceptState,
            tape := endTape (prepareOlder payload older prior index.val count position value)
              inside (widthOutside index.val value outside)} := by
    simpa only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
      valueEnvironment_values, widthExpression_values, List.append_nil, List.append_assoc,
      preparationHistory, prepareOlder, widthOutside, base] using hWidth
  have hRest := chain_run _ _ _ _ _ _ _ hSecond hLast
  have hFirst : workRunExact? (BuilderPayloadFieldCopy.machine fieldStride 1 2)
      (BuilderPayloadFieldCopy.workSteps fieldStride 1 2 index.val [count, position]
        (prior.reverse ++ payload) value)
      (workStartConfiguration (BuilderPayloadFieldCopy.machine fieldStride 1 2)
        (endTape (initialValues payload older prior index.val count position) inside outside)) =
      some {state := (BuilderPayloadFieldCopy.machine fieldStride 1 2).acceptState,
            tape := endTape (base ++ [index.val, count, position] ++ valueHistory index.val value)
              inside (valueOutside index.val value outside)} := by
    simpa only [BuilderPayloadFieldCopy.literalField, Nat.one_ne_zero, ite_false,
      BuilderLiteralSearchFrame.payloadReader, valueOutside, initialValues, baseValues,
      valueHistory, base, payload, value, List.append_assoc, List.cons_append, List.nil_append] using hField
  exact chain_run _ _ _ _ _ _ _ hFirst hRest

theorem workRunExact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine
      (workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val)
      (initialConfiguration (literalListValues literals) older prior index.val count position inside outside) =
      some (finalConfiguration (literalListValues literals) older prior index.val count position
        literals[index.val].index.val inside outside) := by
  have hPrepare := prepare_workRunExact literals index prior hPrior count position older inside outside
  have hCompare := BuilderRegisterCompareResidual.workRunExact position (literals[index.val].index.val + 2)
    (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val)
    inside (prepareOutside index.val position literals[index.val].index.val outside)
  have h := WorkMachineChain.workRunExact _ _ _ _ _ _ _ hPrepare rfl hCompare
  have hInitial (tape : WorkTape) :
      renameConfiguration WorkMachineChain.firstState (workStartConfiguration prepareMachine tape) =
        workStartConfiguration machine tape := rfl
  rw [hInitial] at h
  exact h

theorem run_compile_exact {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine)
      (6 * workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val)
      (encodeWorkConfiguration (initialConfiguration (literalListValues literals) older prior index.val count position inside outside)) =
      encodeWorkConfiguration (finalConfiguration (literalListValues literals) older prior index.val count position
        literals[index.val].index.val inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact literals index prior hPrior count position older inside outside)

theorem final_accept_iff (payload older prior : List Nat) (ordinal count position value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count position value inside outside).state = machine.acceptState ↔
      position < value + 2 := by
  change WorkMachineChain.secondState
      (BuilderRegisterCompareResidual.finalConfiguration position (value + 2)
        (prepareOlder payload older prior ordinal count position value) inside
        (prepareOutside ordinal position value outside)).state =
    WorkMachineChain.secondState BuilderRegisterCompareResidual.machine.acceptState ↔ _
  constructor
  · intro h
    exact (BuilderRegisterCompareResidual.final_accept_iff position (value + 2) _ inside _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegisterCompareResidual.final_accept_iff position (value + 2) _ inside _).2 h)

theorem final_reject_iff (payload older prior : List Nat) (ordinal count position value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count position value inside outside).state = machine.rejectState ↔
      value + 2 ≤ position := by
  change WorkMachineChain.secondState
      (BuilderRegisterCompareResidual.finalConfiguration position (value + 2)
        (prepareOlder payload older prior ordinal count position value) inside
        (prepareOutside ordinal position value outside)).state =
    WorkMachineChain.secondState BuilderRegisterCompareResidual.machine.rejectState ↔ _
  constructor
  · intro h
    exact (BuilderRegisterCompareResidual.final_reject_iff position (value + 2) _ inside _).1
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegisterCompareResidual.final_reject_iff position (value + 2) _ inside _).2 h)

theorem final_tape (payload older prior : List Nat) (ordinal count position value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration payload older prior ordinal count position value inside outside).tape =
      endTape (finalValues payload older prior ordinal count position value) inside
        (finalOutside ordinal position value outside) := by
  change BuilderRegisterCompareResidual.outputTape (comparisonResult position value)
    (prepareOlder payload older prior ordinal count position value) inside
    (prepareOutside ordinal position value outside) = _
  simp only [BuilderRegisterCompareResidual.outputTape, finalValues, finalOutside,
    prepareOlder, chunk_eq, comparisonHistory, List.append_assoc]

theorem finalOutside_length_le (ordinal position value : Nat) (outside : List WorkSymbol) :
    (finalOutside ordinal position value outside).length ≤ outside.length := by
  simp only [finalOutside, prepareOutside, widthOutside, valueOutside, List.length_drop]
  omega

/-- Charge the actual history once; the cyclic proof must not iterate a loose span polynomial. -/
theorem final_span_le_initial_add_chunk (payload older prior : List Nat) (ordinal count position value : Nat)
    (outside : List WorkSymbol) :
    (registerWord (finalValues payload older prior ordinal count position value)).length +
      (finalOutside ordinal position value outside).length ≤
      (registerWord (initialValues payload older prior ordinal count position)).length + outside.length +
        (registerWord (chunk ordinal count position value)).length := by
  have hOutside := finalOutside_length_le ordinal position value outside
  simp only [finalValues, initialValues, registerWord_append, List.length_append]
  omega

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
private theorem field_good : Good (BuilderPayloadFieldCopy.machine fieldStride 1 2) :=
  ⟨BuilderPayloadFieldCopy.rules_pairwise_query_distinct _ _ _, BuilderPayloadFieldCopy.noRuleAtAccept _ _ _,
   BuilderPayloadFieldCopy.noRuleAtReject _ _ _, BuilderPayloadFieldCopy.acceptState_ne_rejectState _ _ _⟩
private theorem width_good : Good (BuilderRegisterExpression.machine widthExpression 0) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct _ _, BuilderRegisterExpression.noRuleAtAccept _ _,
   BuilderRegisterExpression.noRuleAtReject _ _, BuilderRegisterExpression.acceptState_ne_rejectState _ _⟩
private theorem pack_good : Good (BuilderRegisterPack.machine argumentFields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct _ _, BuilderRegisterPack.noRuleAtAccept _ _,
   BuilderRegisterPack.noRuleAtReject _ _, BuilderRegisterPack.acceptState_ne_rejectState _ _⟩
private theorem compare_good : Good BuilderRegisterCompareResidual.machine :=
  ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct, BuilderRegisterCompareResidual.noRuleAtAccept,
   BuilderRegisterCompareResidual.noRuleAtReject, BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩
private theorem prepare_good : Good prepareMachine := chain_good _ _ field_good (chain_good _ _ width_good pack_good)
private theorem good : Good machine := chain_good _ _ prepare_good compare_good

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct := good.1
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := good.2.2.2

def valueSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderPayloadFieldCopy.spanPolynomial fieldStride 1 2 bound
def widthSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterExpression.spanPolynomial widthExpression (valueSpanPolynomial bound)) (valueSpanPolynomial bound)
def prepareSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.spanPolynomial argumentFields (widthSpanPolynomial bound)) (widthSpanPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterCompareResidual.spanPolynomial (prepareSpanPolynomial bound)) (prepareSpanPolynomial bound)
def prepareRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderPayloadFieldCopy.rawTimePolynomial fieldStride 1 2 bound) (.constant 6))
    (.add (.add (BuilderRegisterExpression.rawTimePolynomial widthExpression (valueSpanPolynomial bound)) (.constant 6))
      (BuilderRegisterPack.rawTimePolynomial argumentFields (widthSpanPolynomial bound)))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (prepareRawTimePolynomial bound) (.constant 6))
    (BuilderRegisterCompareResidual.rawTimePolynomial (prepareSpanPolynomial bound))

theorem prepare_source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older prior index.val count position)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val ++
      [position, literals[index.val].index.val + 2])).length +
      (prepareOutside index.val position literals[index.val].index.val outside).length ≤
      (prepareSpanPolynomial bound).eval input ∧
    6 * prepareSteps (literalListValues literals) prior index.val count position literals[index.val].index.val ≤
      (prepareRawTimePolynomial bound).eval input := by
  let value := literals[index.val].index.val
  let payload := literalListValues literals
  let base := baseValues payload older prior
  have hInitial : (registerWord (older ++ (literalListValues literals).reverse ++ prior ++ [index.val] ++ [count, position])).length +
      outside.length ≤ bound.eval input := by
    simpa only [initialValues, baseValues, List.append_assoc, List.cons_append, List.nil_append] using hSpan
  have hValue := BuilderLiteralSearchFrame.field_source_polynomial_bounds literals index prior hPrior ⟨1, by decide⟩
    2 older [count, position] rfl outside bound input hInitial
  have hAfterValue : (registerWord (base ++ [index.val, count, position] ++ valueHistory index.val value)).length +
      (valueOutside index.val value outside).length ≤ (valueSpanPolynomial bound).eval input := by
    simpa only [BuilderPayloadFieldCopy.literalField, Nat.one_ne_zero, ite_false,
      valueOutside, valueSpanPolynomial, valueHistory, base, baseValues, value, payload,
      List.append_assoc, List.cons_append, List.nil_append] using hValue.1
  have hWidthInput : (registerWord (base ++ List.ofFn (valueEnvironment index.val count position value) ++ [])).length ≤
      (valueSpanPolynomial bound).eval input := by
    simpa only [valueEnvironment_values, List.append_nil, List.append_assoc] using
      Nat.le_trans (Nat.le_add_right _ _) hAfterValue
  have hWidth := BuilderRegisterExpression.source_polynomial_bounds widthExpression (valueSpanPolynomial bound)
    input base (valueEnvironment index.val count position value) [] hWidthInput
  simp only [valueEnvironment_values, widthExpression_values, List.append_nil, List.append_assoc] at hWidth
  have hAfterWidth : (registerWord (prepareOlder payload older prior index.val count position value)).length +
      (widthOutside index.val value outside).length ≤ (widthSpanPolynomial bound).eval input := by
    have hExterior : (valueOutside index.val value outside).length ≤ (valueSpanPolynomial bound).eval input := by omega
    simp only [widthSpanPolynomial, NatPolynomial.eval_add, widthOutside, List.length_drop,
      prepareOlder, preparationHistory, List.append_assoc]
    change (registerWord (base ++ ([index.val, count, position] ++
      (valueHistory index.val value ++ widthHistory value)))).length + _ ≤ _
    omega
  have hPackInput : (registerWord (base ++ List.ofFn (packedEnvironment index.val count position value) ++ [])).length ≤
      (widthSpanPolynomial bound).eval input := by
    rw [environment_values, List.append_nil]
    exact Nat.le_trans (Nat.le_add_right _ _) hAfterWidth
  have hPack := BuilderRegisterPack.source_polynomial_bounds argumentFields (widthSpanPolynomial bound) input base
    (packedEnvironment index.val count position value) [] hPackInput
  simp only [environment_values, packed_values, List.append_nil] at hPack
  constructor
  · have hExterior : (widthOutside index.val value outside).length ≤ (widthSpanPolynomial bound).eval input := by omega
    simp only [prepareSpanPolynomial, NatPolynomial.eval_add, prepareOutside, List.length_drop]
    change (registerWord ((base ++ preparationHistory index.val count position value) ++ [position, value + 2])).length +
      ((widthOutside index.val value outside).length - (registerWord [position, value + 2]).length) ≤ _
    omega
  · have hValueTime := hValue.2
    simp only [BuilderPayloadFieldCopy.literalField, Nat.one_ne_zero, ite_false, BuilderLiteralSearchFrame.payloadReader] at hValueTime
    simp only [prepareSteps, prepareRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    dsimp only [value, payload] at hPack hValueTime hWidth ⊢
    omega

theorem source_polynomial_bounds {width : Nat} (literals : List (BoundedLiteral width)) (index : Fin literals.length)
    (prior : List Nat) (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * index.val)
    (count position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues (literalListValues literals) older prior index.val count position)).length +
      outside.length ≤ bound.eval input) :
    (registerWord (finalValues (literalListValues literals) older prior index.val count position literals[index.val].index.val)).length +
      (finalOutside index.val position literals[index.val].index.val outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * workSteps (literalListValues literals) prior index.val count position literals[index.val].index.val ≤
      (rawTimePolynomial bound).eval input := by
  have hPrepare := prepare_source_polynomial_bounds literals index prior hPrior count position older outside bound input hSpan
  have hCompare := BuilderRegisterCompareResidual.source_polynomial_bounds position (literals[index.val].index.val + 2)
    (prepareOlder (literalListValues literals) older prior index.val count position literals[index.val].index.val)
    (prepareSpanPolynomial bound) input (Nat.le_trans (Nat.le_add_right _ _) hPrepare.1)
  constructor
  · have hExterior : (prepareOutside index.val position literals[index.val].index.val outside).length ≤
        (prepareSpanPolynomial bound).eval input := by omega
    have hOutput : (registerWord (finalValues (literalListValues literals) older prior index.val count position literals[index.val].index.val)).length ≤
        (BuilderRegisterCompareResidual.spanPolynomial (prepareSpanPolynomial bound)).eval input := by
      simpa only [finalValues, prepareOlder, chunk_eq, comparisonHistory, comparisonResult, List.append_assoc] using hCompare.1
    simp only [spanPolynomial, NatPolynomial.eval_add, finalOutside, List.length_drop]
    omega
  · simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderLiteralSearchComparison
