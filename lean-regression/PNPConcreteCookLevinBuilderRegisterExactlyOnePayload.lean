/-
Copyright (c) 2026 PNP Labs.
Prepared contracts for the full descending exactly-one register payload.
The universal tape runs and polynomial bounds, not these finite examples,
establish the complete two-pass constructor.
-/
import PNP.Concrete.CookLevinBuilderRegisterExactlyOnePayload

namespace PNP.Concrete.CookLevin.BuilderRegisterExactlyOnePayload.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example : incrementMachine.rules.length = 10 := rfl
example (inside outside : List WorkSymbol) :
    workRunExact? incrementMachine 2
      (workStartConfiguration incrementMachine
        { left := outside, head := scratchEndSymbol, right := inside }) =
      some {
        state := incrementMachine.acceptState
        tape := { left := outside.drop 1, head := scratchEndSymbol, right := unitSymbol :: inside } } :=
  increment_workRunExact inside outside
example (inside : List WorkSymbol) :
    workRunExact? incrementMachine 2
      (workStartConfiguration incrementMachine
        { left := [], head := scratchEndSymbol, right := inside }) =
      some {
        state := incrementMachine.acceptState
        tape := { left := [], head := scratchEndSymbol, right := unitSymbol :: inside } } :=
  increment_workRunExact inside []
example : incrementMachine.rules.Pairwise WorkMachineChain.QueryDistinct := increment_control.1
example : WorkMachineProgramGraph.NoRuleAt incrementMachine incrementMachine.acceptState := increment_control.2.1
example : WorkMachineProgramGraph.NoRuleAt incrementMachine incrementMachine.rejectState := increment_control.2.2.1
example : incrementMachine.acceptState ≠ incrementMachine.rejectState := increment_control.2.2.2

example : graph.nodes.length = 5 := rfl
example : rangeNode.program = BuilderRegisterDescendingRange.machineWith BuilderRegisterCountdownControl.counterMarker := rfl
example : zeroNode.program = RegisterConstant.machine 0 := rfl
example : consumeNode.program = BuilderRegisterCountdownControl.consume := rfl
example : consumeNode.onAccept = .node incrementNode.reference := rfl
example : consumeNode.onReject = .node tagNode.reference := rfl
example : incrementNode.onAccept = .node consumeNode.reference := rfl
example : tagNode.program = RegisterConstant.machine 4 := rfl
example : tagNode.onAccept = .accept := rfl
example : graph.WellFormed := graph_wellFormed

example (count upper : Nat) :
    payloadValues count upper = BuilderRegisterDescendingRange.values upper count ++ [count, 4] := rfl
example (count upper : Nat) : (payloadValues count upper).length = count + 2 := payload_length count upper
example : payloadValues 3 5 = [4, 3, 2, 3, 4] := rfl
example : payloadValues 3 3 = [2, 1, 0, 3, 4] := rfl
example (upper : Nat) : payloadValues 0 upper = [0, 4] := rfl

-- The count must be read from the original counter, not substituted by a supplied list length.
example (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) (hCount : count ≤ upper) :
    workRunExact? machine (workSteps count upper)
      (workStartConfiguration machine (endTape (older ++ [count, upper]) inside [])) =
      some {
        state := machine.acceptState
        tape := endTape
          (older ++ [count] ++ (BuilderRegisterDescendingRange.values upper count ++ [count, 4])) inside
          ((List.replicate (upper - count + 1) .blank).drop (count + 6)) } :=
  workRunExact count upper older inside hCount
example (upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 0 upper) (initialConfiguration 0 upper older inside) =
      some (finalConfiguration 0 upper older inside) := workRunExact 0 upper older inside (Nat.zero_le _)
example (upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps upper upper) (initialConfiguration upper upper older inside) =
      some (finalConfiguration upper upper older inside) := workRunExact upper upper older inside (Nat.le_refl _)
example (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) (hCount : count ≤ upper) :
    run (compileWorkMachine machine) (6 * workSteps count upper)
      (encodeWorkConfiguration (initialConfiguration count upper older inside)) =
      encodeWorkConfiguration (finalConfiguration count upper older inside) := run_compile_exact count upper older inside hCount

example (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count upper older inside).tape.right =
      (registerWord (payloadValues count upper)).reverse ++
        ((registerWord (older ++ [count])).reverse ++ inside) := final_inside_preserved count upper older inside
example (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count upper older inside).tape.left =
      (List.replicate (upper - count + 1) WorkSymbol.blank).drop (count + 6) := final_exterior count upper older inside
example (upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration 0 upper older inside).tape =
      endTape (older ++ [0, 0, 4]) inside ((List.replicate (upper + 1) .blank).drop 6) := by
  simp only [finalConfiguration, finalTape, payloadValues, BuilderRegisterDescendingRange.values,
    Nat.sub_zero, Nat.zero_add, List.nil_append, List.append_assoc, List.cons_append]

example (spent value : Nat) (emitted : List Nat) :
    loopSteps spent 0 emitted value =
      BuilderRegisterCountdownControl.exhaustedSteps spent (emitted ++ [value]) + 12 := by
  simp only [loopSteps, RegisterConstant.steps]
example (spent remaining value : Nat) (emitted : List Nat) :
    loopSteps spent (remaining + 1) emitted value =
      BuilderRegisterCountdownControl.consumeSteps spent (remaining + 1) (emitted ++ [value]) +
        loopSteps (spent + 1) remaining emitted (value + 1) + 4 := by
  simp only [loopSteps]
  omega
example (spent remaining value bound : Nat) (emitted : List Nat)
    (hCounter : spent + remaining ≤ bound) (hValue : value + remaining ≤ bound)
    (hLength : emitted.length ≤ bound) (hValues : ∀ item ∈ emitted, item ≤ bound) :
    loopSteps spent remaining emitted value ≤ (remaining + 1) * (24 * ((bound + 1) * (bound + 1))) :=
  loopSteps_le spent remaining value bound emitted hCounter hValue hLength hValues
example (count upper bound : Nat) (hCount : count ≤ bound) (hUpper : upper ≤ bound) :
    workSteps count upper ≤ 60 * ((bound + 1) * (bound + 1) * (bound + 1)) := workSteps_le count upper bound hCount hUpper
example (count upper bound : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ bound) (hUpper : upper ≤ bound) (hOlder : (registerWord older).length ≤ bound) :
    (registerWord (older ++ [count] ++ payloadValues count upper)).length +
      (finalConfiguration count upper older inside).tape.left.length ≤ 10 * ((bound + 1) * (bound + 1)) :=
  output_span_le count upper bound older inside hCount hUpper hOlder
example (bound : NatPolynomial) (inputLength count upper : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ bound.eval inputLength) (hUpper : upper ≤ bound.eval inputLength)
    (hOlder : (registerWord older).length ≤ bound.eval inputLength) :
    (registerWord (older ++ [count] ++ payloadValues count upper)).length +
        (finalConfiguration count upper older inside).tape.left.length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count upper ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds bound inputLength count upper older inside hCount hUpper hOlder

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderRegisterExactlyOnePayload.Regression
