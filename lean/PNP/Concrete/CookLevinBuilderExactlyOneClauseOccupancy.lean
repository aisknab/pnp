/-
Copyright (c) 2026 PNP Labs.

Physical exactly-one clause occupancy from the actual index and list-count
registers. A doubled pair-count identity reduces occupancy to ordinary
addition, multiplication and strict comparison without enumerating pairs.
Both outcomes preserve the original frame, retain the computed arithmetic
history and account for every allocated and cleared exterior cell.

Source-payload operand extraction and token emission remain separate edges.
This general register program is not a complete formula-builder claim.
-/

import PNP.Concrete.CookLevinBuilderRegisterPack
import PNP.Concrete.CookLevinBuilderRegisterLessThan
import PNP.Concrete.CookLevinClauseOccupancy

namespace PNP.Concrete.CookLevin.BuilderExactlyOneClauseOccupancy

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

theorem pairCount_twice (count : Nat) :
    2 * LocalConstraint.pairCount count + count = count * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [LocalConstraint.pairCount, Nat.mul_add, Nat.mul_succ, Nat.succ_mul,
        Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
      omega

def leftValue (index count : Nat) : Nat := 2 * index + count
def rightValue (count : Nat) : Nat := count * count + 2

theorem occupancy_iff (index count : Nat) :
    index < 1 + LocalConstraint.pairCount count ↔ leftValue index count < rightValue count := by
  have h := pairCount_twice count
  unfold leftValue rightValue
  constructor <;> intro hIndex <;> omega

def leftExpression : BuilderRegisterExpression.Expr 2 :=
  .binary .add (.binary .mul (.constant 2) (.argument ⟨0, by decide⟩)) (.argument ⟨1, by decide⟩)
def rightExpression : BuilderRegisterExpression.Expr 2 :=
  .binary .add (.binary .mul (.argument ⟨1, by decide⟩) (.argument ⟨1, by decide⟩)) (.constant 2)
def environment (index count : Nat) (coordinate : Fin 2) : Nat :=
  match coordinate.val with
  | 0 => index
  | _ => count
def leftValues (index count : Nat) : List Nat :=
  BuilderRegisterExpression.values leftExpression (environment index count)
def rightValues (index count : Nat) : List Nat :=
  BuilderRegisterExpression.values rightExpression (environment index count)
def arithmeticValues (index count : Nat) : List Nat := leftValues index count ++ rightValues index count
def history (index count : Nat) : List Nat := [index, count] ++ arithmeticValues index count

private theorem environment_ofFn (index count : Nat) : List.ofFn (environment index count) = [index, count] := rfl
private theorem left_values (index count : Nat) :
    leftValues index count = [2, index, 2 * index, count, leftValue index count] := rfl
private theorem right_values (index count : Nat) :
    rightValues index count = [count, count, count * count, 2, rightValue count] := rfl

def argumentEnvironment (index count : Nat) (coordinate : Fin 10) : Nat :=
  match coordinate.val with
  | 0 => 2
  | 1 => index
  | 2 => 2 * index
  | 3 => count
  | 4 => leftValue index count
  | 5 | 6 => count
  | 7 => count * count
  | 8 => 2
  | _ => rightValue count
def argumentFields : List (BuilderRegisterPack.Field 10) :=
  [.argument ⟨4, by decide⟩, .argument ⟨9, by decide⟩]

private theorem argumentEnvironment_ofFn (index count : Nat) :
    List.ofFn (argumentEnvironment index count) = arithmeticValues index count := rfl
private theorem argument_values (index count : Nat) :
    BuilderRegisterPack.values argumentFields (argumentEnvironment index count) =
      [leftValue index count, rightValue count] := rfl

def prepareMachine : WorkMachine :=
  WorkMachineChain.machine (BuilderRegisterExpression.machine leftExpression 0)
    (WorkMachineChain.machine (BuilderRegisterExpression.machine rightExpression 5)
      (BuilderRegisterPack.machine argumentFields 0))
def machine : WorkMachine := WorkMachineChain.machine prepareMachine BuilderRegisterLessThan.machine

def prepareSteps (index count : Nat) : Nat :=
  BuilderRegisterExpression.workSteps leftExpression (environment index count) [] + 1 +
    (BuilderRegisterExpression.workSteps rightExpression (environment index count) (leftValues index count) + 1 +
      BuilderRegisterPack.workSteps argumentFields (argumentEnvironment index count) [])
def workSteps (index count : Nat) : Nat :=
  prepareSteps index count + 1 + BuilderRegisterLessThan.workSteps (leftValue index count) (rightValue count)
def scratchValues (index count : Nat) : List Nat :=
  arithmeticValues index count ++ [leftValue index count, rightValue count]
def preparedOutside (index count : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop (registerWord (scratchValues index count)).length
def finalOutside (index count : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (leftValue index count + rightValue count + 3) WorkSymbol.blank ++
    (preparedOutside index count outside).drop 1

def initialConfiguration (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [index, count]) inside outside)
def finalConfiguration (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) : WorkConfiguration :=
  PipelineStateNamespace.renameConfiguration WorkMachineChain.secondState
    (BuilderRegisterLessThan.finalConfiguration (leftValue index count) (rightValue count)
      (older ++ history index count) inside (preparedOutside index count outside))

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

private theorem prepare_run (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? prepareMachine (prepareSteps index count)
      (workStartConfiguration prepareMachine (endTape (older ++ [index, count]) inside outside)) =
      some {
        state := prepareMachine.acceptState
        tape := endTape (older ++ history index count ++ [leftValue index count, rightValue count])
          inside (preparedOutside index count outside) } := by
  have hLeft := BuilderRegisterExpression.workRunExact leftExpression 0 older
    (environment index count) [] inside outside rfl
  have hRight := BuilderRegisterExpression.workRunExact rightExpression 5 older
    (environment index count) (leftValues index count) inside
    (outside.drop (registerWord (leftValues index count)).length) rfl
  have hPack := BuilderRegisterPack.workRunExact argumentFields 0 (older ++ [index, count])
    (argumentEnvironment index count) [] inside
    ((outside.drop (registerWord (leftValues index count)).length).drop
      (registerWord (rightValues index count)).length) rfl
  simp only [BuilderRegisterExpression.initialConfiguration, BuilderRegisterExpression.finalConfiguration,
    environment_ofFn, List.append_nil] at hLeft hRight
  simp only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    argumentEnvironment_ofFn, argument_values, List.append_nil] at hPack
  have hNext := chain_run (BuilderRegisterExpression.machine rightExpression 5)
    (BuilderRegisterPack.machine argumentFields 0)
    (BuilderRegisterExpression.workSteps rightExpression (environment index count) (leftValues index count))
    (BuilderRegisterPack.workSteps argumentFields (argumentEnvironment index count) [])
    _ _ _ hRight (by simpa only [arithmeticValues, rightValues, leftValues, List.append_assoc] using hPack)
  have h := chain_run (BuilderRegisterExpression.machine leftExpression 0)
    (WorkMachineChain.machine (BuilderRegisterExpression.machine rightExpression 5)
      (BuilderRegisterPack.machine argumentFields 0))
    (BuilderRegisterExpression.workSteps leftExpression (environment index count) []) _ _ _ _ hLeft hNext
  simpa only [prepareMachine, prepareSteps, history, preparedOutside, scratchValues, arithmeticValues,
    leftValues, rightValues, List.drop_drop, registerWord_append, List.length_append, List.append_assoc, Nat.add_assoc] using h

private theorem chain_run_result (first second : WorkMachine) (n m : Nat)
    (initial middle : WorkTape) (final : WorkConfiguration)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) = some final) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some (PipelineStateNamespace.renameConfiguration WorkMachineChain.secondState final) :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem workRunExact (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps index count) (initialConfiguration index count older inside outside) =
      some (finalConfiguration index count older inside outside) := by
  have hCompare := BuilderRegisterLessThan.workRunExact (leftValue index count) (rightValue count)
    (older ++ history index count) inside (preparedOutside index count outside)
  simp only [BuilderRegisterLessThan.initialConfiguration] at hCompare
  have h := chain_run_result prepareMachine BuilderRegisterLessThan.machine
    (prepareSteps index count) (BuilderRegisterLessThan.workSteps (leftValue index count) (rightValue count))
    _ _ _ (prepare_run index count older inside outside) hCompare
  simpa only [machine, workSteps, initialConfiguration, finalConfiguration] using h

theorem run_compile_exact (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps index count)
      (encodeWorkConfiguration (initialConfiguration index count older inside outside)) =
      encodeWorkConfiguration (finalConfiguration index count older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact index count older inside outside)

theorem final_accept_iff (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration index count older inside outside).state = machine.acceptState ↔
      index < 1 + LocalConstraint.pairCount count := by
  have h := BuilderRegisterLessThan.final_accept_iff (leftValue index count) (rightValue count)
    (older ++ history index count) inside (preparedOutside index count outside)
  change WorkMachineChain.secondState _ = WorkMachineChain.secondState _ ↔ _
  constructor
  · intro hState
    exact (occupancy_iff index count).mpr (h.mp (WorkMachineChain.secondState_injective hState))
  · intro hIndex
    exact congrArg WorkMachineChain.secondState (h.mpr ((occupancy_iff index count).mp hIndex))

theorem final_reject_iff (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration index count older inside outside).state = machine.rejectState ↔
      1 + LocalConstraint.pairCount count ≤ index := by
  have h := BuilderRegisterLessThan.final_reject_iff (leftValue index count) (rightValue count)
    (older ++ history index count) inside (preparedOutside index count outside)
  have hOccupied := occupancy_iff index count
  change WorkMachineChain.secondState _ = WorkMachineChain.secondState _ ↔ _
  constructor
  · intro hState
    have hNot := h.mp (WorkMachineChain.secondState_injective hState)
    exact Nat.le_of_not_gt (fun hIndex => (Nat.not_lt.mpr hNot) (hOccupied.mp hIndex))
  · intro hIndex
    have hNot : rightValue count ≤ leftValue index count :=
      Nat.le_of_not_gt (fun hLess => (Nat.not_lt.mpr hIndex) (hOccupied.mpr hLess))
    exact congrArg WorkMachineChain.secondState (h.mpr hNot)

theorem canonical_occupancy {width : Nat} (variables : List (Fin width)) (index : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration index variables.length older inside outside).state = machine.acceptState ↔
      ClauseOccupancy.localSlot (.exactlyOne variables) index = true := by
  rw [final_accept_iff]
  simp only [ClauseOccupancy.localSlot, LocalConstraint.clauseCount, decide_eq_true_eq]

theorem final_tape (index count : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration index count older inside outside).tape =
      endTape (older ++ history index count) inside (finalOutside index count outside) := rfl

theorem final_outside_length_le (index count : Nat) (outside : List WorkSymbol) :
    (finalOutside index count outside).length ≤ leftValue index count + rightValue count + 3 + outside.length := by
  simp only [finalOutside, preparedOutside, List.length_append, List.length_replicate, List.length_drop]
  omega

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineChain.QueryDistinct ∧
    WorkMachineChain.NoRuleAtAccept program ∧ WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
      program.acceptState ≠ program.rejectState
private theorem chain_good (first second : WorkMachine) (hFirst : Good first) (hSecond : Good second) :
    Good (WorkMachineChain.machine first second) :=
  ⟨WorkMachineChain.rules_pairwise_query_distinct _ _ hFirst.1 hSecond.1 hFirst.2.1,
   WorkMachineChain.noRuleAtAccept _ _ hSecond.2.1,
   WorkMachineChain.noRuleAtAccept first {second with acceptState := second.rejectState} hSecond.2.2.1,
   WorkMachineChain.machine_acceptState_ne_rejectState _ _ hSecond.2.2.2⟩
private theorem expression_good (expression : BuilderRegisterExpression.Expr 2) (afterCount : Nat) :
    Good (BuilderRegisterExpression.machine expression afterCount) :=
  ⟨BuilderRegisterExpression.rules_pairwise_query_distinct expression afterCount,
   BuilderRegisterExpression.noRuleAtAccept expression afterCount,
   BuilderRegisterExpression.noRuleAtReject expression afterCount,
   BuilderRegisterExpression.acceptState_ne_rejectState expression afterCount⟩
private theorem good : Good machine :=
  chain_good _ _ (chain_good _ _ (expression_good leftExpression 0)
    (chain_good _ _ (expression_good rightExpression 5)
      ⟨BuilderRegisterPack.rules_pairwise_query_distinct argumentFields 0,
       BuilderRegisterPack.noRuleAtAccept argumentFields 0, BuilderRegisterPack.noRuleAtReject argumentFields 0,
       BuilderRegisterPack.acceptState_ne_rejectState argumentFields 0⟩))
    ⟨BuilderRegisterLessThan.rules_pairwise_query_distinct, BuilderRegisterLessThan.noRuleAtAccept,
     BuilderRegisterLessThan.noRuleAtReject, BuilderRegisterLessThan.acceptState_ne_rejectState⟩

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct := good.1
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := good.2.2.2

def leftSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial leftExpression bound
def arithmeticSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterExpression.spanPolynomial rightExpression (leftSpanPolynomial bound)
def preparedSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial argumentFields (arithmeticSpanPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 3) (preparedSpanPolynomial bound)) (.add bound (.constant 3))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (.add
    (BuilderRegisterExpression.rawTimePolynomial leftExpression bound)
    (BuilderRegisterExpression.rawTimePolynomial rightExpression (leftSpanPolynomial bound)))
    (BuilderRegisterPack.rawTimePolynomial argumentFields (arithmeticSpanPolynomial bound)))
    (.add (BuilderRegisterLessThan.rawTimePolynomial (preparedSpanPolynomial bound)) (.constant 18))

theorem source_polynomial_bounds (index count : Nat) (older : List Nat) (outside : List WorkSymbol)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [index, count])).length + outside.length ≤ bound.eval inputLength) :
    (registerWord (older ++ history index count)).length + (finalOutside index count outside).length ≤
        (spanPolynomial bound).eval inputLength ∧
      6 * workSteps index count ≤ (rawTimePolynomial bound).eval inputLength := by
  have hInitial : (registerWord (older ++ [index, count])).length ≤ bound.eval inputLength := by omega
  have hOutside : outside.length ≤ bound.eval inputLength := by omega
  have hLeft := BuilderRegisterExpression.source_polynomial_bounds leftExpression bound inputLength older
    (environment index count) [] (by simpa only [environment_ofFn, List.append_nil] using hInitial)
  have hLeftSpan :
      (registerWord (older ++ List.ofFn (environment index count) ++ leftValues index count)).length ≤
        (leftSpanPolynomial bound).eval inputLength := by
    simpa only [List.append_nil, leftValues, leftSpanPolynomial] using hLeft.1
  have hRight := BuilderRegisterExpression.source_polynomial_bounds rightExpression (leftSpanPolynomial bound)
    inputLength older (environment index count) (leftValues index count) hLeftSpan
  have hArithmetic :
      (registerWord ((older ++ [index, count]) ++ List.ofFn (argumentEnvironment index count) ++ [])).length ≤
        (arithmeticSpanPolynomial bound).eval inputLength := by
    simpa only [argumentEnvironment_ofFn, arithmeticValues, environment_ofFn, List.append_nil,
      leftValues, rightValues, List.append_assoc, arithmeticSpanPolynomial] using hRight.1
  have hPack := BuilderRegisterPack.source_polynomial_bounds argumentFields (arithmeticSpanPolynomial bound)
    inputLength (older ++ [index, count]) (argumentEnvironment index count) [] hArithmetic
  have hPrepared :
      (registerWord (older ++ history index count ++ [leftValue index count, rightValue count])).length ≤
        (preparedSpanPolynomial bound).eval inputLength := by
    simpa only [argumentEnvironment_ofFn, argument_values, history, List.append_nil, List.append_assoc, preparedSpanPolynomial] using hPack.1
  have hParts :
      (registerWord (older ++ history index count)).length ≤ (preparedSpanPolynomial bound).eval inputLength ∧
      leftValue index count ≤ (preparedSpanPolynomial bound).eval inputLength ∧
      rightValue count ≤ (preparedSpanPolynomial bound).eval inputLength := by
    have hPair : (registerWord [leftValue index count, rightValue count]).length =
        leftValue index count + rightValue count + 2 := by
      simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
      omega
    rw [registerWord_append, List.length_append, hPair] at hPrepared
    constructor
    · omega
    · constructor <;> omega
  have hCompare := BuilderRegisterLessThan.raw_time_polynomial (leftValue index count) (rightValue count)
    (preparedSpanPolynomial bound) inputLength hParts.2.1 hParts.2.2
  have hExterior := final_outside_length_le index count outside
  constructor
  · simp only [spanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  · simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant, workSteps, prepareSteps]
    omega

end PNP.Concrete.CookLevin.BuilderExactlyOneClauseOccupancy
