/-
Copyright (c) 2026 PNP Labs.

Universal cursor contracts over arbitrary intervening scratch values.
-/
import PNP.Concrete.CookLevinBuilderPayloadSearchAdvance

open PNP.Concrete PNP.Concrete.CookLevin
open PNP.Concrete.CookLevin.BuilderPayloadSearchAdvance
open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example : BuilderPayloadSearchAdvance.machine = BuilderLiteralSearchAdvance.machine := by
  apply BuilderPayloadSearchAdvance.machine_unchanged <;> assumption

example (remaining residual : Nat) (middle : List Nat) (hMiddle : middle.length = 14) :
    (ordinalSuffix remaining residual middle).length = 16 := by
  apply BuilderPayloadSearchAdvance.ordinalSuffix_length <;> assumption

example (ordinal residual : Nat) (middle : List Nat) (hMiddle : middle.length = 14) :
    (countSuffix ordinal residual middle).length = 16 := by
  apply BuilderPayloadSearchAdvance.countSuffix_length <;> assumption

example (older middle : List Nat) (ordinal remaining residual : Nat)
    (inside outside : List WorkSymbol) (hMiddle : middle.length = 14) :
    workRunExact? BuilderPayloadSearchAdvance.machine (workSteps middle ordinal remaining residual)
      (initialConfiguration older middle ordinal remaining residual inside outside) =
      some (finalConfiguration older middle ordinal remaining residual inside outside) := by
  apply BuilderPayloadSearchAdvance.workRunExact <;> assumption

example (older middle : List Nat) (ordinal remaining residual : Nat)
    (inside outside : List WorkSymbol) (hMiddle : middle.length = 14) :
    run (compileWorkMachine BuilderPayloadSearchAdvance.machine) (6 * workSteps middle ordinal remaining residual)
      (encodeWorkConfiguration (initialConfiguration older middle ordinal remaining residual inside outside)) =
      encodeWorkConfiguration (finalConfiguration older middle ordinal remaining residual inside outside) := by
  apply BuilderPayloadSearchAdvance.run_compile_exact <;> assumption

example (older middle : List Nat) (ordinal remaining residual : Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration older middle ordinal remaining residual inside outside).tape =
      endTape (finalValues older middle ordinal remaining residual) inside (finalOutside ordinal remaining residual outside) := by
  apply BuilderPayloadSearchAdvance.final_tape <;> assumption

example (ordinal remaining residual : Nat) (outside : List WorkSymbol) :
    finalOutside ordinal remaining residual outside = (countOutside ordinal remaining outside).drop residual := by
  apply BuilderPayloadSearchAdvance.finalOutside_eq <;> assumption

example (ordinal remaining residual : Nat) (outside : List WorkSymbol) :
    (finalOutside ordinal remaining residual outside).length ≤ outside.length := by
  apply BuilderPayloadSearchAdvance.finalOutside_length_le <;> assumption

example (older middle : List Nat) (ordinal remaining residual : Nat)
    (hMiddle : middle.length = 14) :
    (finalValues older middle ordinal remaining residual).length = older.length + 20 := by
  apply BuilderPayloadSearchAdvance.final_frame_length <;> assumption

example (prior middle : List Nat) (ordinal remaining residual : Nat)
    (hPrior : prior.length = 17 * ordinal) (hMiddle : middle.length = 14) :
    (initialValues prior middle ordinal remaining residual).length = 17 * (ordinal + 1) := by
  apply BuilderPayloadSearchAdvance.next_history_length <;> assumption

example (older middle : List Nat) (ordinal remaining residual : Nat) :
    finalValues older middle ordinal remaining residual =
      initialValues older middle ordinal remaining residual ++ [ordinal + 1, remaining, residual] := by
  apply BuilderPayloadSearchAdvance.original_frame_preserved <;> assumption

example : BuilderPayloadSearchAdvance.machine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  apply BuilderPayloadSearchAdvance.rules_pairwise_query_distinct <;> assumption

example : WorkMachineChain.NoRuleAtAccept BuilderPayloadSearchAdvance.machine := by
  apply BuilderPayloadSearchAdvance.noRuleAtAccept <;> assumption

example : WorkMachineProgramGraph.NoRuleAt BuilderPayloadSearchAdvance.machine BuilderPayloadSearchAdvance.machine.rejectState := by
  apply BuilderPayloadSearchAdvance.noRuleAtReject <;> assumption

example : BuilderPayloadSearchAdvance.machine.acceptState ≠ BuilderPayloadSearchAdvance.machine.rejectState := by
  apply BuilderPayloadSearchAdvance.acceptState_ne_rejectState <;> assumption

example (older middle : List Nat) (ordinal remaining residual bound : Nat)
    (outside : List WorkSymbol)
    (hSpan : (registerWord (initialValues older middle ordinal remaining residual)).length + outside.length ≤ bound) :
    (registerWord (finalValues older middle ordinal remaining residual)).length +
      (finalOutside ordinal remaining residual outside).length ≤ spanBound bound ∧
    workSteps middle ordinal remaining residual ≤ workBound bound := by
  apply BuilderPayloadSearchAdvance.space_time_bounds <;> assumption

example (older middle : List Nat) (ordinal remaining residual : Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues older middle ordinal remaining residual)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues older middle ordinal remaining residual)).length +
      (finalOutside ordinal remaining residual outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * workSteps middle ordinal remaining residual ≤ (rawTimePolynomial bound).eval input := by
  apply BuilderPayloadSearchAdvance.source_polynomial_bounds <;> assumption

example (middle : List Nat) :
    initialValues [31] middle 4 2 6 = [31,4,3] ++ middle ++ [6] := rfl
example (middle : List Nat) :
    finalValues [31] middle 4 2 6 = [31,4,3] ++ middle ++ [6,5,2,6] := by
  simp only [finalValues, initialValues, List.append_assoc, List.cons_append, List.nil_append]
example (middle : List Nat) :
    ordinalSuffix 2 6 middle = [3] ++ middle ++ [6] := rfl
example (middle : List Nat) :
    countSuffix 4 6 middle = middle ++ [6,5] := rfl
example (ordinal remaining : Nat) (outside : List WorkSymbol) :
    finalOutside ordinal remaining 0 outside = countOutside ordinal remaining outside := rfl
example (ordinal remaining residual : Nat) :
    finalOutside ordinal remaining residual [] = [] := by
  simp only [finalOutside_eq, countOutside, incrementOutside, ordinalOutside, List.drop_nil]
example (bound : Nat) : spanBound bound = 4 * bound + 4 := rfl
example : (initialValues [] (List.replicate 14 99) 0 0 0).length = 17 := rfl
example : (finalValues [] (List.replicate 14 99) 0 0 0).length = 20 := rfl
example : finalValues [] (List.replicate 14 99) 0 0 0 =
    [0,1] ++ List.replicate 14 99 ++ [0,1,0,0] := rfl
