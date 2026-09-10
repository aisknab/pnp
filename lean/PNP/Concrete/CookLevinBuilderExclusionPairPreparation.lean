/-
Copyright (c) 2026 PNP Labs.

Physical pair-ordinal arithmetic from the two written count/ordinal registers.
The fixed expression compiler, halver and residual comparator derive every
operand. A comparison accept means invalid; its reject means a valid pair slot.
The fresh outer frontier is explicit and preserved through all fixed phases.

This prepares actual row-selection data, not source-payload extraction, variable
field reads, or a complete formula builder. No runtime value generates control.
-/

import PNP.Concrete.CookLevinBuilderExclusionPairRow
import PNP.Concrete.CookLevinBuilderRegisterHalve

namespace PNP.Concrete.CookLevin.BuilderExclusionPairPreparation

open BuilderUnaryPolynomial
open BuilderArbitrarySlotHeaderRouter
open BuilderDividerOperands (endTape)
open BuilderExclusionPairSelection (reverseCoordinate)
open LocalConstraint (pairCount)

def product (count : Nat) : Nat := count * (count + 1)
def quotient (count : Nat) : Nat := product count / 2
def boundary (count coordinate : Nat) : Nat := count + coordinate + 1

theorem product_twice (count : Nat) : product count = 2 * (pairCount count + count) := by
  have h := BuilderExactlyOneClauseOccupancy.pairCount_twice count
  simp only [product, Nat.mul_add, Nat.mul_one]
  omega

theorem quotient_eq (count : Nat) : quotient count = pairCount count + count := by
  rw [quotient, product_twice]
  exact Nat.mul_div_right (pairCount count + count) (show 0 < 2 from by decide)

theorem valid_iff (count coordinate : Nat) :
    boundary count coordinate ≤ quotient count ↔ coordinate < pairCount count := by
  rw [quotient_eq]
  unfold boundary
  constructor <;> intro h <;> omega

theorem invalid_iff (count coordinate : Nat) :
    quotient count < boundary count coordinate ↔ pairCount count ≤ coordinate := by
  rw [quotient_eq]
  unfold boundary
  constructor <;> intro h <;> omega

theorem valid_count (count coordinate : Nat) (hValid : coordinate < pairCount count) : 2 ≤ count := by
  cases count with
  | zero => simp only [pairCount] at hValid; omega
  | succ count =>
      cases count with
      | zero => simp only [pairCount] at hValid; omega
      | succ count => omega

theorem valid_residual (count coordinate : Nat) (hValid : coordinate < pairCount count) :
    quotient count - boundary count coordinate = reverseCoordinate count coordinate := by
  rw [quotient_eq]
  simp only [boundary, reverseCoordinate, if_pos hValid]
  omega

def inputEnvironment (count coordinate : Nat) (index : Fin 2) : Nat :=
  match index.val with
  | 0 => count
  | _ => coordinate

def productExpression : BuilderRegisterExpression.Expr 2 :=
  .binary .mul (.argument ⟨0, by decide⟩)
    (.binary .add (.argument ⟨0, by decide⟩) (.constant 1))

def rootValues (count coordinate : Nat) : List Nat := [count, coordinate, count, count, 1, count + 1]
def halvedValues (count coordinate : Nat) : List Nat :=
  rootValues count coordinate ++ BuilderRegisterHalve.outputValues (product count)

def halvedEnvironment (count coordinate : Nat) (index : Fin 15) : Nat :=
  match index.val with
  | 0 | 2 | 3 => count
  | 1 => coordinate
  | 4 => 1
  | 5 => count + 1
  | 6 => product count
  | 7 | 8 => 0
  | 9 => quotient count * 2
  | 10 | 14 => product count % 2
  | 11 => 2
  | _ => quotient count

def boundaryExpression : BuilderRegisterExpression.Expr 15 :=
  .binary .add (.binary .add (.argument ⟨0, by decide⟩) (.argument ⟨1, by decide⟩)) (.constant 1)

def arithmeticValues (count coordinate : Nat) : List Nat :=
  halvedValues count coordinate ++ [count, coordinate, count + coordinate, 1, boundary count coordinate]

def arithmeticEnvironment (count coordinate : Nat) (index : Fin 20) : Nat :=
  match index.val with
  | 0 | 2 | 3 | 15 => count
  | 1 | 16 => coordinate
  | 4 | 18 => 1
  | 5 => count + 1
  | 6 => product count
  | 7 | 8 => 0
  | 9 => quotient count * 2
  | 10 | 14 => product count % 2
  | 11 => 2
  | 12 | 13 => quotient count
  | 17 => count + coordinate
  | _ => boundary count coordinate

def comparisonFields : List (BuilderRegisterPack.Field 20) :=
  [.argument ⟨13, by decide⟩, .argument ⟨19, by decide⟩]

theorem inputEnvironment_ofFn (count coordinate : Nat) :
    List.ofFn (inputEnvironment count coordinate) = [count, coordinate] := rfl

theorem product_values (count coordinate : Nat) :
    [count, coordinate] ++ BuilderRegisterExpression.values productExpression (inputEnvironment count coordinate) =
      rootValues count coordinate ++ [product count] := rfl

theorem halvedEnvironment_ofFn (count coordinate : Nat) :
    List.ofFn (halvedEnvironment count coordinate) = halvedValues count coordinate := rfl

theorem boundary_values (count coordinate : Nat) :
    halvedValues count coordinate ++
      BuilderRegisterExpression.values boundaryExpression (halvedEnvironment count coordinate) =
        arithmeticValues count coordinate := rfl

theorem arithmeticEnvironment_ofFn (count coordinate : Nat) :
    List.ofFn (arithmeticEnvironment count coordinate) = arithmeticValues count coordinate := rfl

theorem comparison_values (count coordinate : Nat) :
    BuilderRegisterPack.values comparisonFields (arithmeticEnvironment count coordinate) =
      [quotient count, boundary count coordinate] := rfl

def prefixMachine : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterExpression.machine productExpression 0)
    (WorkMachineChain.machine BuilderRegisterHalve.machine
      (WorkMachineChain.machine (BuilderRegisterExpression.machine boundaryExpression 0)
        (BuilderRegisterPack.machine comparisonFields 0)))

def machine : WorkMachine := WorkMachineChain.machine prefixMachine BuilderRegisterCompareResidual.machine

def prefixSteps (count coordinate : Nat) : Nat :=
  BuilderRegisterExpression.workSteps productExpression (inputEnvironment count coordinate) [] + 1 +
    (BuilderRegisterHalve.workSteps (product count) + 1 +
      (BuilderRegisterExpression.workSteps boundaryExpression (halvedEnvironment count coordinate) [] + 1 +
        BuilderRegisterPack.workSteps comparisonFields (arithmeticEnvironment count coordinate) []))

def workSteps (count coordinate : Nat) : Nat :=
  prefixSteps count coordinate + 1 +
    BuilderRegisterCompareResidual.workSteps (quotient count) (boundary count coordinate)

def history (count coordinate : Nat) : List Nat :=
  arithmeticValues count coordinate ++
    BuilderRegisterCompareResidual.outputValues (RawRouter.compareResult 0 (quotient count) (boundary count coordinate))

theorem history_length (count coordinate : Nat) : (history count coordinate).length = 25 := by
  rw [history, List.length_append, BuilderRegisterCompareResidual.outputValues_length]
  rfl

def initialConfiguration (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    WorkConfiguration := workStartConfiguration machine (endTape (older ++ [count, coordinate]) inside [])

def finalConfiguration (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    WorkConfiguration :=
  PipelineStateNamespace.renameConfiguration WorkMachineChain.secondState
    (BuilderRegisterCompareResidual.finalConfiguration (quotient count) (boundary count coordinate)
      (older ++ arithmeticValues count coordinate) inside [])

private theorem chain_run (first second : WorkMachine) (n m : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

private theorem prefix_run (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? prefixMachine (prefixSteps count coordinate)
      (workStartConfiguration prefixMachine (endTape (older ++ [count, coordinate]) inside [])) =
      some {
        state := prefixMachine.acceptState
        tape := endTape (older ++ arithmeticValues count coordinate ++
          [quotient count, boundary count coordinate]) inside [] } := by
  have hProduct := BuilderRegisterExpression.workRunExact productExpression 0 older
    (inputEnvironment count coordinate) [] inside [] rfl
  simp only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    inputEnvironment_ofFn, List.append_nil, List.drop_nil] at hProduct
  have hHalf := BuilderRegisterHalve.workRunExact (product count) (older ++ rootValues count coordinate) inside
  simp only [BuilderRegisterHalve.initialConfiguration, BuilderRegisterHalve.finalConfiguration] at hHalf
  have hBoundary := BuilderRegisterExpression.workRunExact boundaryExpression 0 older
    (halvedEnvironment count coordinate) [] inside [] rfl
  simp only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    halvedEnvironment_ofFn, List.append_nil, List.drop_nil] at hBoundary
  have hPack := BuilderRegisterPack.workRunExact comparisonFields 0 older
    (arithmeticEnvironment count coordinate) [] inside [] rfl
  simp only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    arithmeticEnvironment_ofFn, comparison_values, List.append_nil, List.drop_nil] at hPack
  have hFirstTape : (older ++ [count, coordinate]) ++
      BuilderRegisterExpression.values productExpression (inputEnvironment count coordinate) =
        (older ++ rootValues count coordinate) ++ [product count] := by
    rw [List.append_assoc, product_values, ← List.append_assoc]
  rw [hFirstTape] at hProduct
  have hHalfTape : (older ++ rootValues count coordinate) ++ BuilderRegisterHalve.outputValues (product count) =
      older ++ halvedValues count coordinate := by simp only [halvedValues, List.append_assoc]
  rw [hHalfTape] at hHalf
  have hBoundaryTape : (older ++ halvedValues count coordinate) ++
      BuilderRegisterExpression.values boundaryExpression (halvedEnvironment count coordinate) =
        older ++ arithmeticValues count coordinate := by rw [List.append_assoc, boundary_values]
  rw [hBoundaryTape] at hBoundary
  have hBP := chain_run _ _ _ _ _ _ _ hBoundary hPack
  have hHBP := chain_run _ _ _ _ _ _ _ hHalf hBP
  have hAll := chain_run _ _ _ _ _ _ _ hProduct hHBP
  simpa only [prefixMachine, prefixSteps] using hAll

private theorem chain_run_result (first second : WorkMachine) (n m : Nat)
    (initial middle : WorkTape) (final : WorkConfiguration)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) = some final) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some (PipelineStateNamespace.renameConfiguration WorkMachineChain.secondState final) :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem workRunExact (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps count coordinate) (initialConfiguration count coordinate older inside) =
      some (finalConfiguration count coordinate older inside) := by
  have hCompare := BuilderRegisterCompareResidual.workRunExact (quotient count) (boundary count coordinate)
    (older ++ arithmeticValues count coordinate) inside []
  simp only [BuilderRegisterCompareResidual.initialConfiguration] at hCompare
  have hAll := chain_run_result prefixMachine BuilderRegisterCompareResidual.machine
    (prefixSteps count coordinate)
    (BuilderRegisterCompareResidual.workSteps (quotient count) (boundary count coordinate))
    _ _ _ (prefix_run count coordinate older inside) hCompare
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration] using hAll

theorem run_compile_exact (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count coordinate)
      (encodeWorkConfiguration (initialConfiguration count coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration count coordinate older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact count coordinate older inside)

theorem final_valid_iff (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).state = machine.rejectState ↔
      coordinate < pairCount count := by
  have h := BuilderRegisterCompareResidual.final_reject_iff (quotient count) (boundary count coordinate)
    (older ++ arithmeticValues count coordinate) inside []
  change WorkMachineChain.secondState _ = WorkMachineChain.secondState _ ↔ _
  constructor
  · intro hState
    exact (valid_iff count coordinate).mp (h.mp (WorkMachineChain.secondState_injective hState))
  · intro hValid
    exact congrArg WorkMachineChain.secondState (h.mpr ((valid_iff count coordinate).mpr hValid))

theorem final_invalid_iff (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).state = machine.acceptState ↔
      pairCount count ≤ coordinate := by
  have h := BuilderRegisterCompareResidual.final_accept_iff (quotient count) (boundary count coordinate)
    (older ++ arithmeticValues count coordinate) inside []
  change WorkMachineChain.secondState _ = WorkMachineChain.secondState _ ↔ _
  constructor
  · intro hState
    exact (invalid_iff count coordinate).mp (h.mp (WorkMachineChain.secondState_injective hState))
  · intro hInvalid
    exact congrArg WorkMachineChain.secondState (h.mpr ((invalid_iff count coordinate).mpr hInvalid))

theorem final_tape (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).tape =
      endTape (older ++ history count coordinate) inside [] := by
  change (BuilderRegisterCompareResidual.finalConfiguration (quotient count) (boundary count coordinate)
    (older ++ arithmeticValues count coordinate) inside []).tape = _
  rw [BuilderRegisterCompareResidual.final_tape]
  simp only [history, BuilderRegisterCompareResidual.outputValues,
    BuilderRegisterCompareResidual.resultBoundary_eq, BuilderRegisterCompareResidual.resultCoordinate_eq,
    List.append_assoc, List.drop_nil]

theorem final_frontier (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).tape.left = [] := by
  rw [final_tape]
  rfl

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
    WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
    WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
    WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩

private theorem expression_good {arity : Nat} (expression : BuilderRegisterExpression.Expr arity) :
    Good (BuilderRegisterExpression.machine expression 0) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct expression 0,
    BuilderRegisterExpression.noRuleAtAccept expression 0,
    BuilderRegisterExpression.noRuleAtReject expression 0,
    BuilderRegisterExpression.acceptState_ne_rejectState expression 0⟩

private theorem good : Good machine :=
  chain_good _ _
    (chain_good _ _ (expression_good productExpression)
      (chain_good _ _
        ⟨BuilderRegisterHalve.rules_pairwise_query_distinct, BuilderRegisterHalve.noRuleAtAccept,
          BuilderRegisterHalve.noRuleAtReject, BuilderRegisterHalve.acceptState_ne_rejectState⟩
        (chain_good _ _ (expression_good boundaryExpression)
          ⟨BuilderRegisterPack.rules_pairwise_query_distinct comparisonFields 0,
            BuilderRegisterPack.noRuleAtAccept comparisonFields 0,
            BuilderRegisterPack.noRuleAtReject comparisonFields 0,
            BuilderRegisterPack.acceptState_ne_rejectState comparisonFields 0⟩)))
    ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct, BuilderRegisterCompareResidual.noRuleAtAccept,
      BuilderRegisterCompareResidual.noRuleAtReject, BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := good.1
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := good.2.2.2

def productSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial productExpression bound
def halvedSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterHalve.spanPolynomial (productSpanPolynomial bound)
def arithmeticSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial boundaryExpression (halvedSpanPolynomial bound)
def preparedSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial comparisonFields (arithmeticSpanPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterCompareResidual.spanPolynomial (preparedSpanPolynomial bound)

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterExpression.rawTimePolynomial productExpression bound)
    (.add (BuilderRegisterHalve.rawTimePolynomial (productSpanPolynomial bound))
      (.add (BuilderRegisterExpression.rawTimePolynomial boundaryExpression (halvedSpanPolynomial bound))
        (.add (BuilderRegisterPack.rawTimePolynomial comparisonFields (arithmeticSpanPolynomial bound))
          (.add (BuilderRegisterCompareResidual.rawTimePolynomial (preparedSpanPolynomial bound)) (.constant 24)))))

/-- Every fixed phase and all four joins are charged in the original input's encoded size. -/
theorem source_polynomial_bounds (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [count, coordinate])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ history count coordinate)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count coordinate ≤ (rawTimePolynomial bound).eval inputLength := by
  have hProduct := BuilderRegisterExpression.source_polynomial_bounds productExpression bound inputLength
    older (inputEnvironment count coordinate) [] (by
      simpa only [inputEnvironment_ofFn, List.append_nil] using hSpan)
  have hProductSpan :
      (registerWord ((older ++ rootValues count coordinate) ++ [product count])).length ≤
        (productSpanPolynomial bound).eval inputLength := by
    simpa only [productSpanPolynomial, inputEnvironment_ofFn, List.append_nil, List.append_assoc, product_values] using hProduct.1
  have hHalf := BuilderRegisterHalve.source_polynomial_bounds (product count)
    (older ++ rootValues count coordinate) (productSpanPolynomial bound) inputLength hProductSpan
  have hHalfSpan :
      (registerWord (older ++ List.ofFn (halvedEnvironment count coordinate) ++ [])).length ≤
        (halvedSpanPolynomial bound).eval inputLength := by
    simpa only [halvedSpanPolynomial, halvedEnvironment_ofFn, halvedValues, List.append_nil, List.append_assoc] using hHalf.1
  have hBoundary := BuilderRegisterExpression.source_polynomial_bounds boundaryExpression
    (halvedSpanPolynomial bound) inputLength older (halvedEnvironment count coordinate) [] hHalfSpan
  have hArithmeticSpan :
      (registerWord (older ++ List.ofFn (arithmeticEnvironment count coordinate) ++ [])).length ≤
        (arithmeticSpanPolynomial bound).eval inputLength := by
    simpa only [arithmeticSpanPolynomial, halvedEnvironment_ofFn, arithmeticEnvironment_ofFn, List.append_nil,
      List.append_assoc, boundary_values] using hBoundary.1
  have hPack := BuilderRegisterPack.source_polynomial_bounds comparisonFields
    (arithmeticSpanPolynomial bound) inputLength older (arithmeticEnvironment count coordinate) [] hArithmeticSpan
  have hPreparedSpan :
      (registerWord ((older ++ arithmeticValues count coordinate) ++
        [quotient count, boundary count coordinate])).length ≤ (preparedSpanPolynomial bound).eval inputLength := by
    simpa only [preparedSpanPolynomial, arithmeticEnvironment_ofFn, comparison_values, List.append_nil] using hPack.1
  have hCompare := BuilderRegisterCompareResidual.source_polynomial_bounds
    (quotient count) (boundary count coordinate) (older ++ arithmeticValues count coordinate)
    (preparedSpanPolynomial bound) inputLength hPreparedSpan
  constructor
  · simpa only [spanPolynomial, history, List.append_assoc] using hCompare.1
  · simp only [workSteps, prefixSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

end PNP.Concrete.CookLevin.BuilderExclusionPairPreparation
