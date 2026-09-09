/-
Copyright (c) 2026 PNP Labs.

Derive the exact exclusion-clause finish boundary from the two actual retained
source values, then compare it with the physical clause position. A fixed
expression and copy feed the existing restored comparator. Its residual
distinguishes finish from a body position; all nine scratch registers are
explicit. No boundary, branch result or token is supplied to the program.
-/

import PNP.Concrete.CookLevinBuilderExclusionPairLiteralTokens

namespace PNP.Concrete.CookLevin.BuilderExclusionClauseBoundary

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open BuilderExclusionPairLiteralTokens (frame environment environment_values initialValues)
open BuilderRegisterExpression (Expr)
open PipelineStateNamespace (renameConfiguration)

def boundary (first second : Nat) : Nat := first + second + 5
def boundaryExpression : Expr 14 :=
  .binary .add (.binary .add (.argument ⟨0, by decide⟩) (.argument ⟨12, by decide⟩)) (.constant 5)
def positionExpression : Expr 14 := .argument ⟨13, by decide⟩
def boundaryPrefix (first second : Nat) : List Nat := [first, second, first + second, 5]
def boundaryValues (first second : Nat) : List Nat := boundaryPrefix first second ++ [boundary first second]
def result (first second position : Nat) : RawRouter.ComparisonResult :=
  RawRouter.compareResult 0 (boundary first second) position
def scratch (first second position : Nat) : List Nat :=
  boundaryPrefix first second ++ BuilderRegisterCompareResidual.outputValues (result first second position)
def preparedValues (first second position : Nat) (retained older : List Nat) : List Nat :=
  (initialValues first second position retained older ++ boundaryPrefix first second) ++ [boundary first second, position]
def finalValues (first second position : Nat) (retained older : List Nat) : List Nat :=
  (initialValues first second position retained older ++ boundaryPrefix first second) ++
    BuilderRegisterCompareResidual.outputValues (result first second position)

theorem boundary_positive (first second : Nat) : 0 < boundary first second := by
  unfold boundary
  omega
theorem boundary_values (first second position : Nat) (retained : List Nat) (hRetained : retained.length = 11) :
    BuilderRegisterExpression.values boundaryExpression (environment first second position retained hRetained) =
      boundaryValues first second := by
  change [environment first second position retained hRetained ⟨0, by decide⟩,
    environment first second position retained hRetained ⟨12, by decide⟩,
    environment first second position retained hRetained ⟨0, by decide⟩ +
      environment first second position retained hRetained ⟨12, by decide⟩, 5,
    environment first second position retained hRetained ⟨0, by decide⟩ +
      environment first second position retained hRetained ⟨12, by decide⟩ + 5] = _
  rw [BuilderExclusionPairLiteralTokens.environment_first, BuilderExclusionPairLiteralTokens.environment_second]
  rfl
theorem boundary_nodeCount : BuilderRegisterExpression.nodeCount boundaryExpression = 5 := rfl
theorem boundaryValues_length (first second : Nat) : (boundaryValues first second).length = 5 := rfl
theorem position_values (first second position : Nat) (retained : List Nat) (hRetained : retained.length = 11) :
    BuilderRegisterExpression.values positionExpression (environment first second position retained hRetained) = [position] := by
  change [environment first second position retained hRetained ⟨13, by decide⟩] = [position]
  rw [BuilderExclusionPairLiteralTokens.environment_position]
theorem scratch_length (first second position : Nat) : (scratch first second position).length = 9 := by
  simp only [scratch, boundaryPrefix, List.length_append, BuilderRegisterCompareResidual.outputValues_length,
    List.length_cons, List.length_nil]
theorem final_values_layout (first second position : Nat) (retained older : List Nat) :
    finalValues first second position retained older =
      initialValues first second position retained older ++ scratch first second position := by
  simp only [finalValues, scratch, List.append_assoc]
theorem residual_eq (first second position : Nat) (hInside : position ≤ boundary first second) :
    BuilderRegisterCompareResidual.resultCoordinate (result first second position) =
      boundary first second - position := by
  rw [result, BuilderRegisterCompareResidual.resultCoordinate_eq, if_neg (Nat.not_lt.mpr hInside)]
theorem residual_suffix (first second position : Nat) (retained older : List Nat)
    (hInside : position ≤ boundary first second) :
    finalValues first second position retained older =
      (initialValues first second position retained older ++ boundaryPrefix first second ++
        BuilderRegisterLessThan.resultValues (result first second position) ++ [position]) ++
        [boundary first second - position] := by
  simp only [finalValues, BuilderRegisterCompareResidual.outputValues,
    show BuilderRegisterCompareResidual.resultBoundary (result first second position) = position from
      BuilderRegisterCompareResidual.resultBoundary_eq _ _,
    residual_eq first second position hInside, List.append_assoc, List.cons_append, List.nil_append]

def prepareMachine : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterExpression.machine boundaryExpression 0)
    (BuilderRegisterExpression.machine positionExpression 5)
def machine : WorkMachine := WorkMachineChain.machine prepareMachine BuilderRegisterCompareResidual.machine
def prepareSteps (first second position : Nat) (retained : List Nat) (hRetained : retained.length = 11) : Nat :=
  BuilderRegisterExpression.workSteps boundaryExpression (environment first second position retained hRetained) [] + 1 +
    BuilderRegisterExpression.workSteps positionExpression (environment first second position retained hRetained)
      (boundaryValues first second)
def workSteps (first second position : Nat) (retained : List Nat) (hRetained : retained.length = 11) : Nat :=
  prepareSteps first second position retained hRetained + 1 +
    BuilderRegisterCompareResidual.workSteps (boundary first second) position
def prepareOutside (first second position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (outside.drop (registerWord (boundaryValues first second)).length).drop (position + 1)
def finalOutside (first second position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (prepareOutside first second position outside).drop
    (BuilderRegisterCompareResidual.allocatedCells (result first second position))
def initialConfiguration (first second position : Nat) (retained older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues first second position retained older) inside outside)
def finalConfiguration (first second position : Nat) (retained older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (BuilderRegisterCompareResidual.finalConfiguration (boundary first second) position
      (initialValues first second position retained older ++ boundaryPrefix first second) inside
      (prepareOutside first second position outside))

private theorem chain_result (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle : WorkTape) (final : WorkConfiguration)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) = some final) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some (renameConfiguration WorkMachineChain.secondState final) :=
  WorkMachineChain.workRunExact first second firstSteps secondSteps _ _ _ hFirst rfl hSecond

private theorem chain_accept_result (first second : WorkMachine) (firstSteps secondSteps : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first firstSteps (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second secondSteps (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (firstSteps + 1 + secondSteps)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  chain_result first second firstSteps secondSteps initial middle _ hFirst hSecond

theorem prepare_workRunExact (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine (prepareSteps first second position retained hRetained)
      (workStartConfiguration prepareMachine (endTape (initialValues first second position retained older) inside outside)) =
      some {
        state := prepareMachine.acceptState
        tape := endTape (preparedValues first second position retained older) inside
          (prepareOutside first second position outside) } := by
  have hFirst := BuilderRegisterExpression.workRunExact boundaryExpression 0 older
    (environment first second position retained hRetained) [] inside outside rfl
  simp only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    List.append_nil, environment_values, boundary_values] at hFirst
  have hSecond := BuilderRegisterExpression.workRunExact positionExpression 5 older
    (environment first second position retained hRetained) (boundaryValues first second) inside
    (outside.drop (registerWord (boundaryValues first second)).length) (boundaryValues_length first second)
  simp only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    environment_values, position_values, registerWord, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil, Nat.add_zero] at hSecond
  have h := chain_accept_result _ _ _ _ _ _ _ hFirst hSecond
  simpa only [prepareMachine, prepareSteps, preparedValues, prepareOutside, initialValues, boundaryValues, boundaryPrefix,
    List.append_assoc, List.cons_append, List.nil_append] using h

theorem workRunExact (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps first second position retained hRetained)
      (initialConfiguration first second position retained older inside outside) =
      some (finalConfiguration first second position retained older inside outside) := by
  have hPrepare := prepare_workRunExact first second position retained older hRetained inside outside
  have hCompare := BuilderRegisterCompareResidual.workRunExact (boundary first second) position
    (initialValues first second position retained older ++ boundaryPrefix first second) inside
    (prepareOutside first second position outside)
  exact chain_result _ _ _ _ _ _ _ hPrepare hCompare

theorem run_compile_exact (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps first second position retained hRetained)
      (encodeWorkConfiguration (initialConfiguration first second position retained older inside outside)) =
      encodeWorkConfiguration (finalConfiguration first second position retained older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact first second position retained older hRetained inside outside)

theorem final_tape (first second position : Nat) (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).tape =
      endTape (finalValues first second position retained older) inside (finalOutside first second position outside) := rfl

private theorem accept_projection :
    machine.acceptState = WorkMachineChain.secondState BuilderRegisterCompareResidual.machine.acceptState := rfl
private theorem reject_projection :
    machine.rejectState = WorkMachineChain.secondState BuilderRegisterCompareResidual.machine.rejectState := rfl

theorem final_accept_iff (first second position : Nat) (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).state = machine.acceptState ↔
      boundary first second < position := by
  simp only [finalConfiguration, renameConfiguration, accept_projection]
  constructor
  · intro h
    exact (BuilderRegisterCompareResidual.final_accept_iff _ _ _ _ _).mp
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegisterCompareResidual.final_accept_iff _ _ _ _ _).mpr h)

theorem final_reject_iff (first second position : Nat) (retained older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration first second position retained older inside outside).state = machine.rejectState ↔
      position ≤ boundary first second := by
  simp only [finalConfiguration, renameConfiguration, reject_projection]
  constructor
  · intro h
    exact (BuilderRegisterCompareResidual.final_reject_iff _ _ _ _ _).mp
      (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderRegisterCompareResidual.final_reject_iff _ _ _ _ _).mpr h)

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
private theorem expression_good (expression : Expr 14) (afterCount : Nat) :
    Good (BuilderRegisterExpression.machine expression afterCount) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct _ _, BuilderRegisterExpression.noRuleAtAccept _ _,
   BuilderRegisterExpression.noRuleAtReject _ _, BuilderRegisterExpression.acceptState_ne_rejectState _ _⟩
private theorem good : Good machine :=
  chain_good _ _ (chain_good _ _ (expression_good boundaryExpression 0) (expression_good positionExpression 5))
    ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct, BuilderRegisterCompareResidual.noRuleAtAccept,
     BuilderRegisterCompareResidual.noRuleAtReject, BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct := good.1
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := good.2.2.2

def preparedSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial positionExpression
    (BuilderRegisterExpression.spanPolynomial boundaryExpression bound)
def prepareRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterExpression.rawTimePolynomial boundaryExpression bound) (.constant 6))
    (BuilderRegisterExpression.rawTimePolynomial positionExpression
      (BuilderRegisterExpression.spanPolynomial boundaryExpression bound))
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterCompareResidual.spanPolynomial (preparedSpanPolynomial bound)) bound
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (prepareRawTimePolynomial bound) (.constant 6))
    (BuilderRegisterCompareResidual.rawTimePolynomial (preparedSpanPolynomial bound))

theorem prepare_polynomial_bounds (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first second position retained older)).length ≤ bound.eval input) :
    (registerWord (preparedValues first second position retained older)).length ≤ (preparedSpanPolynomial bound).eval input ∧
      6 * prepareSteps first second position retained hRetained ≤ (prepareRawTimePolynomial bound).eval input := by
  have hInput : (registerWord (older ++ List.ofFn (environment first second position retained hRetained) ++ [])).length ≤
      bound.eval input := by
    simpa only [environment_values, List.append_nil, initialValues] using hSpan
  have hFirst := BuilderRegisterExpression.source_polynomial_bounds boundaryExpression bound input older
    (environment first second position retained hRetained) [] hInput
  rw [boundary_values] at hFirst
  have hMiddle : (registerWord (older ++ List.ofFn (environment first second position retained hRetained) ++
      boundaryValues first second)).length ≤ (BuilderRegisterExpression.spanPolynomial boundaryExpression bound).eval input := by
    simpa only [List.append_nil] using hFirst.1
  have hSecond := BuilderRegisterExpression.source_polynomial_bounds positionExpression
    (BuilderRegisterExpression.spanPolynomial boundaryExpression bound) input older
    (environment first second position retained hRetained) (boundaryValues first second) hMiddle
  rw [position_values] at hSecond
  constructor
  · simpa only [preparedSpanPolynomial, environment_values, preparedValues, initialValues, boundaryValues, boundaryPrefix,
      List.append_assoc, List.cons_append, List.nil_append] using hSecond.1
  · have hFirstTime := hFirst.2
    have hSecondTime := hSecond.2
    simp only [prepareSteps, prepareRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem source_polynomial_bounds (first second position : Nat) (retained older : List Nat)
    (hRetained : retained.length = 11) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues first second position retained older)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues first second position retained older)).length +
        (finalOutside first second position outside).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps first second position retained hRetained ≤ (rawTimePolynomial bound).eval input := by
  have hPrepare := prepare_polynomial_bounds first second position retained older hRetained bound input (by omega)
  have hCompare := BuilderRegisterCompareResidual.source_polynomial_bounds (boundary first second) position
    (initialValues first second position retained older ++ boundaryPrefix first second) (preparedSpanPolynomial bound) input hPrepare.1
  have hOutside : (finalOutside first second position outside).length ≤ outside.length := by
    simp only [finalOutside, prepareOutside, List.length_drop]
    omega
  constructor
  · have hOutput : (registerWord (finalValues first second position retained older)).length ≤
        (BuilderRegisterCompareResidual.spanPolynomial (preparedSpanPolynomial bound)).eval input := hCompare.1
    simp only [spanPolynomial, NatPolynomial.eval_add]
    omega
  · have hPrepareTime := hPrepare.2
    have hCompareTime := hCompare.2
    simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderExclusionClauseBoundary
