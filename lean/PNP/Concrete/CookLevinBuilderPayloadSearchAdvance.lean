/-
Copyright (c) 2026 PNP Labs.

Reuse the existing fixed five-stage literal-search advance machine with any
fourteen intervening scratch registers. Actual ordinal, positive remaining count
and residual are read at their fixed physical positions; scratch contents do
not select a program or supply a correctness verdict.

The enclosing source-clause search must derive the positive-count and miss
branch. This is its reusable physical cursor contract, not a completed builder.
-/
import PNP.Concrete.CookLevinBuilderLiteralSearchAdvance

namespace PNP.Concrete.CookLevin.BuilderPayloadSearchAdvance

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

/-- The verified control table is reused unchanged. -/
def machine : WorkMachine := BuilderLiteralSearchAdvance.machine

def ordinalSuffix (remaining residual : Nat) (middle : List Nat) : List Nat :=
  [remaining + 1] ++ middle ++ [residual]
def countSuffix (ordinal residual : Nat) (middle : List Nat) : List Nat :=
  middle ++ [residual, ordinal + 1]
def initialValues (older middle : List Nat) (ordinal remaining residual : Nat) : List Nat :=
  older ++ [ordinal, remaining + 1] ++ middle ++ [residual]
def finalValues (older middle : List Nat) (ordinal remaining residual : Nat) : List Nat :=
  initialValues older middle ordinal remaining residual ++ [ordinal + 1, remaining, residual]
def workSteps (middle : List Nat) (ordinal remaining residual : Nat) : Nat :=
  RegisterCopy.steps (ordinalSuffix remaining residual middle) ordinal + 1 +
    (2 + 1 + (RegisterCopy.steps (countSuffix ordinal residual middle) (remaining + 1) + 1 +
      (2 + 1 + RegisterCopy.steps [ordinal + 1, remaining] residual)))

def ordinalOutside (ordinal : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop (ordinal + 1)
def incrementOutside (ordinal : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (ordinalOutside ordinal outside).drop 1
def countOutside (ordinal remaining : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (incrementOutside ordinal outside).drop (remaining + 2)
def finalOutside (ordinal remaining residual : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (WorkSymbol.blank :: countOutside ordinal remaining outside).drop (residual + 1)

def initialConfiguration (older middle : List Nat) (ordinal remaining residual : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (initialValues older middle ordinal remaining residual) inside outside)
def finalConfiguration (older middle : List Nat) (ordinal remaining residual : Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  {state := machine.acceptState, tape := endTape (finalValues older middle ordinal remaining residual) inside (finalOutside ordinal remaining residual outside)}

theorem machine_unchanged : machine = BuilderLiteralSearchAdvance.machine := rfl
theorem ordinalSuffix_length (remaining residual : Nat) (middle : List Nat) (hMiddle : middle.length = 14) :
    (ordinalSuffix remaining residual middle).length = 16 := by
  simp only [ordinalSuffix, List.length_append, List.length_cons, List.length_nil, hMiddle]
theorem countSuffix_length (ordinal residual : Nat) (middle : List Nat) (hMiddle : middle.length = 14) :
    (countSuffix ordinal residual middle).length = 16 := by
  simp only [countSuffix, List.length_append, List.length_cons, List.length_nil, hMiddle]

private theorem chain_run (first second : WorkMachine) (n m : Nat) (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

theorem workRunExact (older middle : List Nat) (ordinal remaining residual : Nat)
    (inside outside : List WorkSymbol) (hMiddle : middle.length = 14) :
    workRunExact? machine (workSteps middle ordinal remaining residual)
      (initialConfiguration older middle ordinal remaining residual inside outside) =
      some (finalConfiguration older middle ordinal remaining residual inside outside) := by
  let frame := initialValues older middle ordinal remaining residual
  have hFirst := BuilderRegionComparisonOperands.copy_workRunExact 16 older
    (ordinalSuffix remaining residual middle) ordinal inside outside
    (ordinalSuffix_length _ _ _ hMiddle)
  have hIncrement := BuilderConstraintRegionAssembly.Increment.workRunExact frame ordinal
    inside (ordinalOutside ordinal outside)
  have hCount := BuilderRegionComparisonOperands.copy_workRunExact 16 (older ++ [ordinal])
    (countSuffix ordinal residual middle) (remaining + 1) inside (incrementOutside ordinal outside)
    (countSuffix_length _ _ _ hMiddle)
  have hDecrement := BuilderRegisterLessThan.decrement_workRunExact remaining (frame ++ [ordinal + 1])
    inside (countOutside ordinal remaining outside)
  have hResidual := BuilderRegionComparisonOperands.copy_workRunExact 2
    (older ++ [ordinal, remaining + 1] ++ middle) [ordinal + 1, remaining]
    residual inside (WorkSymbol.blank :: countOutside ordinal remaining outside) rfl
  have hResidualFrame : (older ++ [ordinal, remaining + 1] ++ middle) ++ [residual] ++
      [ordinal + 1, remaining] = frame ++ [ordinal + 1, remaining] := rfl
  rw [hResidualFrame] at hResidual
  have hLast : workRunExact? (RegisterCopy.machine 2)
      (RegisterCopy.steps [ordinal + 1, remaining] residual)
      (workStartConfiguration (RegisterCopy.machine 2)
        (endTape (frame ++ [ordinal + 1, remaining]) inside (WorkSymbol.blank :: countOutside ordinal remaining outside))) =
      some {state := (RegisterCopy.machine 2).acceptState, tape := endTape (finalValues older middle ordinal remaining residual) inside (finalOutside ordinal remaining residual outside)} := by
    simpa only [finalValues, finalOutside, frame, List.append_assoc, List.cons_append, List.nil_append] using hResidual
  have hDec : workRunExact? BuilderRegisterCountdownControl.decrement 2
      (workStartConfiguration BuilderRegisterCountdownControl.decrement
        (endTape (frame ++ [ordinal + 1, remaining + 1]) inside (countOutside ordinal remaining outside))) =
      some {state := BuilderRegisterCountdownControl.decrement.acceptState, tape := endTape (frame ++ [ordinal + 1, remaining]) inside (WorkSymbol.blank :: countOutside ordinal remaining outside)} := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hDecrement
  have hTail := chain_run _ _ _ _ _ _ _ hDec hLast
  have hCountFrame : (older ++ [ordinal]) ++ [remaining + 1] ++ countSuffix ordinal residual middle =
      frame ++ [ordinal + 1] := by
    simp only [frame, initialValues, countSuffix, List.append_assoc, List.cons_append, List.nil_append]
  have hCopyCount : workRunExact? (RegisterCopy.machine 16)
      (RegisterCopy.steps (countSuffix ordinal residual middle) (remaining + 1))
      (workStartConfiguration (RegisterCopy.machine 16)
        (endTape (frame ++ [ordinal + 1]) inside (incrementOutside ordinal outside))) =
      some {state := (RegisterCopy.machine 16).acceptState, tape := endTape (frame ++ [ordinal + 1, remaining + 1]) inside (countOutside ordinal remaining outside)} := by
    rw [hCountFrame] at hCount
    simpa only [countOutside, Nat.add_assoc, List.append_assoc, List.cons_append, List.nil_append] using hCount
  have hMiddleRun := chain_run _ _ _ _ _ _ _ hCopyCount hTail
  have hInc : workRunExact? BuilderConstraintRegionAssembly.Increment.machine 2
      (workStartConfiguration BuilderConstraintRegionAssembly.Increment.machine
        (endTape (frame ++ [ordinal]) inside (ordinalOutside ordinal outside))) =
      some {state := BuilderConstraintRegionAssembly.Increment.machine.acceptState, tape := endTape (frame ++ [ordinal + 1]) inside (incrementOutside ordinal outside)} := hIncrement
  have hRest := chain_run _ _ _ _ _ _ _ hInc hMiddleRun
  have hCopyOrdinal : workRunExact? (RegisterCopy.machine 16)
      (RegisterCopy.steps (ordinalSuffix remaining residual middle) ordinal)
      (workStartConfiguration (RegisterCopy.machine 16) (endTape frame inside outside)) =
      some {state := (RegisterCopy.machine 16).acceptState, tape := endTape (frame ++ [ordinal]) inside (ordinalOutside ordinal outside)} := by
    simpa only [frame, initialValues, ordinalSuffix, ordinalOutside, List.append_assoc,
      List.cons_append, List.nil_append] using hFirst
  exact chain_run _ _ _ _ _ _ _ hCopyOrdinal hRest

theorem run_compile_exact (older middle : List Nat) (ordinal remaining residual : Nat)
    (inside outside : List WorkSymbol) (hMiddle : middle.length = 14) :
    run (compileWorkMachine machine) (6 * workSteps middle ordinal remaining residual)
      (encodeWorkConfiguration (initialConfiguration older middle ordinal remaining residual inside outside)) =
      encodeWorkConfiguration (finalConfiguration older middle ordinal remaining residual inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact older middle ordinal remaining residual inside outside hMiddle)

theorem final_tape (older middle : List Nat) (ordinal remaining residual : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older middle ordinal remaining residual inside outside).tape =
      endTape (finalValues older middle ordinal remaining residual) inside (finalOutside ordinal remaining residual outside) := rfl
theorem finalOutside_eq (ordinal remaining residual : Nat) (outside : List WorkSymbol) :
    finalOutside ordinal remaining residual outside = (countOutside ordinal remaining outside).drop residual := rfl
theorem finalOutside_length_le (ordinal remaining residual : Nat) (outside : List WorkSymbol) :
    (finalOutside ordinal remaining residual outside).length ≤ outside.length := by
  simp only [finalOutside_eq, countOutside, incrementOutside, ordinalOutside, List.length_drop]
  omega

theorem final_frame_length (older middle : List Nat) (ordinal remaining residual : Nat)
    (hMiddle : middle.length = 14) :
    (finalValues older middle ordinal remaining residual).length = older.length + 20 := by
  simp only [finalValues, initialValues, List.length_append, List.length_cons, List.length_nil, hMiddle]
theorem next_history_length (prior middle : List Nat) (ordinal remaining residual : Nat)
    (hPrior : prior.length = 17 * ordinal) (hMiddle : middle.length = 14) :
    (initialValues prior middle ordinal remaining residual).length = 17 * (ordinal + 1) := by
  simp only [initialValues, List.length_append, List.length_cons, List.length_nil, hPrior, hMiddle]
  omega
theorem original_frame_preserved (older middle : List Nat) (ordinal remaining residual : Nat) :
    finalValues older middle ordinal remaining residual =
      initialValues older middle ordinal remaining residual ++ [ordinal + 1, remaining, residual] := rfl

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderLiteralSearchAdvance.rules_pairwise_query_distinct
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := BuilderLiteralSearchAdvance.noRuleAtAccept
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := BuilderLiteralSearchAdvance.noRuleAtReject
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := BuilderLiteralSearchAdvance.acceptState_ne_rejectState

def workBound := BuilderLiteralSearchAdvance.workBound
def spanBound := BuilderLiteralSearchAdvance.spanBound
def rawTimePolynomial := BuilderLiteralSearchAdvance.rawTimePolynomial
def spanPolynomial := BuilderLiteralSearchAdvance.spanPolynomial

theorem space_time_bounds (older middle : List Nat) (ordinal remaining residual bound : Nat)
    (outside : List WorkSymbol)
    (hSpan : (registerWord (initialValues older middle ordinal remaining residual)).length + outside.length ≤ bound) :
    (registerWord (finalValues older middle ordinal remaining residual)).length +
      (finalOutside ordinal remaining residual outside).length ≤ spanBound bound ∧
    workSteps middle ordinal remaining residual ≤ workBound bound := by
  have hInput : (registerWord (initialValues older middle ordinal remaining residual)).length ≤ bound := by omega
  have hParts := hInput
  simp only [initialValues, registerWord_length, List.length_append, List.sum_append,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hParts
  have hOrdinal : ordinal ≤ bound := by omega
  have hRemaining : remaining + 1 ≤ bound := by omega
  have hResidual : residual ≤ bound := by omega
  have hOrdinalTail : (ordinalSuffix remaining residual middle).length +
      (ordinalSuffix remaining residual middle).sum ≤ 2 * bound + 3 := by
    simp only [ordinalSuffix, List.length_append, List.sum_append,
      List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hCountTail : (countSuffix ordinal residual middle).length +
      (countSuffix ordinal residual middle).sum ≤ 2 * bound + 3 := by
    simp only [countSuffix, List.length_append, List.sum_append,
      List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hResidualTail : [ordinal + 1, remaining].length + [ordinal + 1, remaining].sum ≤ 2 * bound + 3 := by
    simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    omega
  have hCopyOrdinal := RegisterCopy.steps_le (ordinalSuffix remaining residual middle) ordinal
    (2 * bound + 3) (by omega) hOrdinalTail
  have hCopyCount := RegisterCopy.steps_le (countSuffix ordinal residual middle) (remaining + 1)
    (2 * bound + 3) (by omega) hCountTail
  have hCopyResidual := RegisterCopy.steps_le [ordinal + 1, remaining] residual
    (2 * bound + 3) (by omega) hResidualTail
  constructor
  · have hOutside := finalOutside_length_le ordinal remaining residual outside
    simp only [finalValues, registerWord_append, List.length_append, spanBound, BuilderLiteralSearchAdvance.spanBound]
    simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
    rw [registerWord_length] at hSpan
    omega
  · simp only [workSteps, workBound, BuilderLiteralSearchAdvance.workBound, BuilderLiteralSearchAdvance.copyBound]
    omega

theorem source_polynomial_bounds (older middle : List Nat) (ordinal remaining residual : Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues older middle ordinal remaining residual)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues older middle ordinal remaining residual)).length +
      (finalOutside ordinal remaining residual outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * workSteps middle ordinal remaining residual ≤ (rawTimePolynomial bound).eval input := by
  have h := space_time_bounds older middle ordinal remaining residual (bound.eval input) outside hSpan
  rw [spanPolynomial, BuilderLiteralSearchAdvance.spanPolynomial_eval,
    rawTimePolynomial, BuilderLiteralSearchAdvance.rawTimePolynomial_eval]
  exact ⟨h.1, Nat.mul_le_mul_left 6 h.2⟩

end PNP.Concrete.CookLevin.BuilderPayloadSearchAdvance
