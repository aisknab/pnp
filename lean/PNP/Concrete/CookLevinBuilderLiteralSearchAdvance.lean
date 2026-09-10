/-
Copyright (c) 2026 PNP Labs.

Physically advance a literal-search frame after the runtime comparison.
The actual ordinal is copied and incremented, the actual positive remaining
count is copied and decremented, and the comparator's actual residual is copied.
One fixed five-stage machine retains the entire comparison history.

The complete locator must derive this branch from its count and width guards.
No selected ordinal, residual verdict or runtime-sized control is supplied.
-/

import PNP.Concrete.CookLevinBuilderLiteralSearchFrame

namespace PNP.Concrete.CookLevin.BuilderLiteralSearchAdvance

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderLiteralSearchFrame (valueHistory widthHistory comparisonHistory comparisonResult chunk residual)

def ordinalSuffix (ordinal count position value : Nat) : List Nat :=
  [count, position] ++ valueHistory ordinal value ++ widthHistory value ++ comparisonHistory position value
def countSuffix (ordinal position value : Nat) : List Nat :=
  [position] ++ valueHistory ordinal value ++ widthHistory value ++ comparisonHistory position value ++ [ordinal + 1]
def beforeResidual (ordinal count position value : Nat) : List Nat :=
  [ordinal, count, position] ++ valueHistory ordinal value ++ widthHistory value ++
    BuilderRegisterLessThan.resultValues (comparisonResult position value) ++ [value + 2]

theorem ordinalSuffix_length (ordinal count position value : Nat) :
    (ordinalSuffix ordinal count position value).length = 16 := by
  simp only [ordinalSuffix, List.length_append, BuilderLiteralSearchFrame.valueHistory_length,
    widthHistory, comparisonHistory, BuilderRegisterCompareResidual.outputValues_length,
    List.length_cons, List.length_nil] <;> rfl
theorem countSuffix_length (ordinal position value : Nat) :
    (countSuffix ordinal position value).length = 16 := by
  simp only [countSuffix, List.length_append, BuilderLiteralSearchFrame.valueHistory_length,
    widthHistory, comparisonHistory, BuilderRegisterCompareResidual.outputValues_length,
    List.length_cons, List.length_nil] <;> rfl
theorem chunk_ordinal (ordinal count position value : Nat) :
    chunk ordinal count position value = [ordinal] ++ ordinalSuffix ordinal count position value := by
  simp only [chunk, ordinalSuffix, List.append_assoc, List.cons_append, List.nil_append]
theorem chunk_count (ordinal count position value : Nat) :
    chunk ordinal count position value ++ [ordinal + 1] =
      [ordinal, count] ++ countSuffix ordinal position value := by
  simp only [chunk, countSuffix, List.append_assoc, List.cons_append, List.nil_append]
theorem chunk_residual (ordinal count position value : Nat) :
    chunk ordinal count position value = beforeResidual ordinal count position value ++ [residual position value] := by
  simp only [chunk, beforeResidual, comparisonHistory, BuilderRegisterCompareResidual.outputValues,
    comparisonResult, BuilderRegisterCompareResidual.resultBoundary_eq,
    BuilderRegisterCompareResidual.resultCoordinate_eq, residual, List.append_assoc,
    List.cons_append, List.nil_append]

def machine : WorkMachine :=
  WorkMachineChain.machine (RegisterCopy.machine 16)
    (WorkMachineChain.machine BuilderConstraintRegionAssembly.Increment.machine
      (WorkMachineChain.machine (RegisterCopy.machine 16)
        (WorkMachineChain.machine BuilderRegisterCountdownControl.decrement (RegisterCopy.machine 2))))
def workSteps (ordinal remaining position value : Nat) : Nat :=
  RegisterCopy.steps (ordinalSuffix ordinal (remaining + 1) position value) ordinal + 1 +
    (2 + 1 + (RegisterCopy.steps (countSuffix ordinal position value) (remaining + 1) + 1 +
      (2 + 1 + RegisterCopy.steps [ordinal + 1, remaining] (residual position value))))

def initialValues (older : List Nat) (ordinal remaining position value : Nat) : List Nat :=
  older ++ chunk ordinal (remaining + 1) position value
def finalValues (older : List Nat) (ordinal remaining position value : Nat) : List Nat :=
  initialValues older ordinal remaining position value ++ [ordinal + 1, remaining, residual position value]
def ordinalOutside (ordinal : Nat) (outside : List WorkSymbol) : List WorkSymbol := outside.drop (ordinal + 1)
def incrementOutside (ordinal : Nat) (outside : List WorkSymbol) : List WorkSymbol := (ordinalOutside ordinal outside).drop 1
def countOutside (ordinal remaining : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (incrementOutside ordinal outside).drop (remaining + 2)
def finalOutside (ordinal remaining position value : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (WorkSymbol.blank :: countOutside ordinal remaining outside).drop (residual position value + 1)
def initialConfiguration (older : List Nat) (ordinal remaining position value : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues older ordinal remaining position value) inside outside)
def finalConfiguration (older : List Nat) (ordinal remaining position value : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  {state := machine.acceptState,
   tape := endTape (finalValues older ordinal remaining position value) inside
     (finalOutside ordinal remaining position value outside)}

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem workRunExact (older : List Nat) (ordinal remaining position value : Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps ordinal remaining position value)
      (initialConfiguration older ordinal remaining position value inside outside) =
      some (finalConfiguration older ordinal remaining position value inside outside) := by
  let frame := initialValues older ordinal remaining position value
  have hFirst := BuilderRegionComparisonOperands.copy_workRunExact 16 older
    (ordinalSuffix ordinal (remaining + 1) position value) ordinal inside outside
    (ordinalSuffix_length _ _ _ _)
  have hIncrement := BuilderConstraintRegionAssembly.Increment.workRunExact frame ordinal inside (ordinalOutside ordinal outside)
  have hCount := BuilderRegionComparisonOperands.copy_workRunExact 16 (older ++ [ordinal])
    (countSuffix ordinal position value) (remaining + 1) inside (incrementOutside ordinal outside)
    (countSuffix_length _ _ _)
  have hDecrement := BuilderRegisterLessThan.decrement_workRunExact remaining (frame ++ [ordinal + 1])
    inside (countOutside ordinal remaining outside)
  have hResidual := BuilderRegionComparisonOperands.copy_workRunExact 2
    (older ++ beforeResidual ordinal (remaining + 1) position value) [ordinal + 1, remaining]
    (residual position value) inside (WorkSymbol.blank :: countOutside ordinal remaining outside) rfl
  have hResidualFrame : (older ++ beforeResidual ordinal (remaining + 1) position value) ++
      [residual position value] ++ [ordinal + 1, remaining] = frame ++ [ordinal + 1, remaining] := by
    simp only [frame, initialValues, chunk_residual, List.append_assoc]
  rw [hResidualFrame] at hResidual
  have hLast : workRunExact? (RegisterCopy.machine 2)
      (RegisterCopy.steps [ordinal + 1, remaining] (residual position value))
      (workStartConfiguration (RegisterCopy.machine 2)
        (endTape (frame ++ [ordinal + 1, remaining]) inside
          (WorkSymbol.blank :: countOutside ordinal remaining outside))) =
      some {state := (RegisterCopy.machine 2).acceptState,
            tape := endTape (finalValues older ordinal remaining position value) inside
              (finalOutside ordinal remaining position value outside)} := by
    simpa only [finalValues, finalOutside, frame, List.append_assoc, List.cons_append, List.nil_append] using hResidual
  have hDec : workRunExact? BuilderRegisterCountdownControl.decrement 2
      (workStartConfiguration BuilderRegisterCountdownControl.decrement
        (endTape (frame ++ [ordinal + 1, remaining + 1]) inside (countOutside ordinal remaining outside))) =
      some {state := BuilderRegisterCountdownControl.decrement.acceptState,
            tape := endTape (frame ++ [ordinal + 1, remaining]) inside
              (WorkSymbol.blank :: countOutside ordinal remaining outside)} := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hDecrement
  have hTail := chain_run _ _ _ _ _ _ _ hDec hLast
  have hCountFrame : (older ++ [ordinal]) ++ [remaining + 1] ++ countSuffix ordinal position value =
      frame ++ [ordinal + 1] := by
    simp only [frame, initialValues, chunk, countSuffix, List.append_assoc, List.cons_append, List.nil_append]
  have hCopyCount : workRunExact? (RegisterCopy.machine 16)
      (RegisterCopy.steps (countSuffix ordinal position value) (remaining + 1))
      (workStartConfiguration (RegisterCopy.machine 16)
        (endTape (frame ++ [ordinal + 1]) inside (incrementOutside ordinal outside))) =
      some {state := (RegisterCopy.machine 16).acceptState,
            tape := endTape (frame ++ [ordinal + 1, remaining + 1]) inside (countOutside ordinal remaining outside)} := by
    rw [hCountFrame] at hCount
    simpa only [countOutside, Nat.add_assoc, List.append_assoc, List.cons_append, List.nil_append] using hCount
  have hMiddle := chain_run _ _ _ _ _ _ _ hCopyCount hTail
  have hInc : workRunExact? BuilderConstraintRegionAssembly.Increment.machine 2
      (workStartConfiguration BuilderConstraintRegionAssembly.Increment.machine
        (endTape (frame ++ [ordinal]) inside (ordinalOutside ordinal outside))) =
      some {state := BuilderConstraintRegionAssembly.Increment.machine.acceptState,
            tape := endTape (frame ++ [ordinal + 1]) inside (incrementOutside ordinal outside)} := hIncrement
  have hRest := chain_run _ _ _ _ _ _ _ hInc hMiddle
  have hCopyOrdinal : workRunExact? (RegisterCopy.machine 16)
      (RegisterCopy.steps (ordinalSuffix ordinal (remaining + 1) position value) ordinal)
      (workStartConfiguration (RegisterCopy.machine 16) (endTape frame inside outside)) =
      some {state := (RegisterCopy.machine 16).acceptState,
            tape := endTape (frame ++ [ordinal]) inside (ordinalOutside ordinal outside)} := by
    simpa only [frame, initialValues, chunk_ordinal, ordinalOutside, List.append_assoc] using hFirst
  exact chain_run _ _ _ _ _ _ _ hCopyOrdinal hRest

theorem run_compile_exact (older : List Nat) (ordinal remaining position value : Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps ordinal remaining position value)
      (encodeWorkConfiguration (initialConfiguration older ordinal remaining position value inside outside)) =
      encodeWorkConfiguration (finalConfiguration older ordinal remaining position value inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact older ordinal remaining position value inside outside)

theorem final_tape (older : List Nat) (ordinal remaining position value : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older ordinal remaining position value inside outside).tape =
      endTape (finalValues older ordinal remaining position value) inside
        (finalOutside ordinal remaining position value outside) := rfl

theorem finalOutside_eq (ordinal remaining position value : Nat) (outside : List WorkSymbol) :
    finalOutside ordinal remaining position value outside =
      (countOutside ordinal remaining outside).drop (residual position value) := rfl
theorem finalOutside_length_le (ordinal remaining position value : Nat) (outside : List WorkSymbol) :
    (finalOutside ordinal remaining position value outside).length ≤ outside.length := by
  simp only [finalOutside_eq, countOutside, incrementOutside, ordinalOutside, List.length_drop]
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
private theorem copy_good (offset : Nat) : Good (RegisterCopy.machine offset) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct offset, ?_, ?_,
    RegisterCopy.machine_acceptState_ne_rejectState offset⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState offset rule hRule)
  · intro rule hRule
    have h := RegisterCopy.rule_source_lt_acceptState offset rule hRule
    rw [RegisterCopy.machine_acceptState] at h
    rw [RegisterCopy.machine_rejectState]
    omega
private theorem increment_good : Good BuilderConstraintRegionAssembly.Increment.machine := by
  refine ⟨BuilderConstraintRegionAssembly.Increment.rules_pairwise_query_distinct,
    BuilderConstraintRegionAssembly.Increment.noRuleAtAccept, ?_,
    BuilderConstraintRegionAssembly.Increment.acceptState_ne_rejectState⟩
  intro rule hRule
  decide +revert
private theorem decrement_good : Good BuilderRegisterCountdownControl.decrement :=
  BuilderRegisterCountdownControl.decrement_control
private theorem good : Good machine :=
  chain_good _ _ (copy_good 16)
    (chain_good _ _ increment_good (chain_good _ _ (copy_good 16) (chain_good _ _ decrement_good (copy_good 2))))

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct := good.1
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := good.2.1
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := good.2.2.1
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := good.2.2.2

theorem final_frame_length (older : List Nat) (ordinal remaining position value : Nat) :
    (finalValues older ordinal remaining position value).length = older.length + 20 := by
  simp only [finalValues, initialValues, List.length_append, BuilderLiteralSearchFrame.chunk_length,
    List.length_cons, List.length_nil, BuilderLiteralSearchFrame.historyStride]

theorem next_history_length (prior : List Nat) (ordinal remaining position value : Nat)
    (hPrior : prior.length = BuilderLiteralSearchFrame.historyStride * ordinal) :
    (prior ++ chunk ordinal (remaining + 1) position value).length =
      BuilderLiteralSearchFrame.historyStride * (ordinal + 1) :=
  BuilderLiteralSearchFrame.history_step prior ordinal (remaining + 1) position value hPrior

theorem miss_next_frame (older : List Nat) (ordinal remaining position value : Nat) (hMiss : value + 2 ≤ position) :
    finalValues older ordinal remaining position value =
      initialValues older ordinal remaining position value ++ [ordinal + 1, remaining, position - (value + 2)] := by
  have hNot : ¬ position < value + 2 := by omega
  simp only [finalValues, residual, if_neg hNot]

private theorem scalar_bounds (older : List Nat) (ordinal remaining position value bound : Nat)
    (hSpan : (registerWord (initialValues older ordinal remaining position value)).length ≤ bound) :
    ordinal ≤ bound ∧ remaining + 1 ≤ bound ∧ position ≤ bound ∧ residual position value ≤ bound := by
  rw [initialValues, registerWord_append, List.length_append, BuilderLiteralSearchFrame.chunk_word_length] at hSpan
  have hResidual := BuilderLiteralSearchFrame.residual_le position value
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

def copyBound (bound : Nat) : Nat := 4 * (bound + 1) * (bound + 1) + 9 * (bound + 1) + 5
def workBound (bound : Nat) : Nat := 3 * copyBound (2 * bound + 3) + 8
def spanBound (bound : Nat) : Nat := 4 * bound + 4

theorem space_time_bounds (older : List Nat) (ordinal remaining position value bound : Nat)
    (outside : List WorkSymbol)
    (hSpan : (registerWord (initialValues older ordinal remaining position value)).length + outside.length ≤ bound) :
    (registerWord (finalValues older ordinal remaining position value)).length +
      (finalOutside ordinal remaining position value outside).length ≤ spanBound bound ∧
    workSteps ordinal remaining position value ≤ workBound bound := by
  have hInput : (registerWord (initialValues older ordinal remaining position value)).length ≤ bound := by omega
  rcases scalar_bounds older ordinal remaining position value bound hInput with ⟨hOrdinal, hRemaining, hPosition, hResidual⟩
  have hOrdinalTail : (ordinalSuffix ordinal (remaining + 1) position value).length +
      (ordinalSuffix ordinal (remaining + 1) position value).sum ≤ 2 * bound + 3 := by
    have h := hInput
    simp only [initialValues, chunk_ordinal, registerWord_length, List.length_append,
      List.sum_append, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at h
    omega
  have hCountFrame : (registerWord (initialValues older ordinal remaining position value ++ [ordinal + 1])).length ≤ 2 * bound + 2 := by
    rw [registerWord_append, List.length_append]
    simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    rw [registerWord_length] at hInput
    omega
  have hCountTail : (countSuffix ordinal position value).length + (countSuffix ordinal position value).sum ≤ 2 * bound + 3 := by
    have h := hCountFrame
    simp only [initialValues, List.append_assoc, chunk_count, registerWord_length,
      List.length_append, List.sum_append, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at h
    omega
  have hResidualTail : [ordinal + 1, remaining].length + [ordinal + 1, remaining].sum ≤ 2 * bound + 3 := by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hCopyOrdinal := RegisterCopy.steps_le (ordinalSuffix ordinal (remaining + 1) position value) ordinal (2 * bound + 3)
    (by omega) hOrdinalTail
  have hCopyCount := RegisterCopy.steps_le (countSuffix ordinal position value) (remaining + 1) (2 * bound + 3)
    (by omega) hCountTail
  have hCopyResidual := RegisterCopy.steps_le [ordinal + 1, remaining] (residual position value) (2 * bound + 3)
    (by omega) hResidualTail
  constructor
  · have hOutside := finalOutside_length_le ordinal remaining position value outside
    simp only [finalValues, registerWord_append, List.length_append, spanBound]
    simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    rw [registerWord_length] at hSpan
    omega
  · simp only [workSteps, workBound, copyBound]
    omega

def argumentBoundPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 2) bound) (.constant 3)
def copyBoundPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (.mul (.mul (.constant 4) (.add bound (.constant 1))) (.add bound (.constant 1)))
    (.mul (.constant 9) (.add bound (.constant 1)))) (.constant 5)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6) (.add (.mul (.constant 3) (copyBoundPolynomial (argumentBoundPolynomial bound))) (.constant 8))
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 4) bound) (.constant 4)

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := rfl
theorem spanPolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = spanBound (bound.eval input) := rfl

theorem source_polynomial_bounds (older : List Nat) (ordinal remaining position value : Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues older ordinal remaining position value)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues older ordinal remaining position value)).length +
      (finalOutside ordinal remaining position value outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * workSteps ordinal remaining position value ≤ (rawTimePolynomial bound).eval input := by
  have h := space_time_bounds older ordinal remaining position value (bound.eval input) outside hSpan
  rw [spanPolynomial_eval, rawTimePolynomial_eval]
  exact ⟨h.1, Nat.mul_le_mul_left 6 h.2⟩

end PNP.Concrete.CookLevin.BuilderLiteralSearchAdvance
