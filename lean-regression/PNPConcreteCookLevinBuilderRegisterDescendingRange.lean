/-
Copyright (c) 2026 PNP Labs.
Prepared contracts for the complete finite-program descending-range loop.
The universal run, list and polynomial bounds are the authority; small examples
only reject reversed order, missing zero handling or an extra working duplicate.
-/
import PNP.Concrete.CookLevinBuilderRegisterDescendingRange

namespace PNP.Concrete.CookLevin.BuilderRegisterDescendingRange.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example : graph.nodes.length = 5 := rfl
example : markNode.program = BuilderRegisterCountdownControl.markCounterMachine := rfl
example : consumeNode.program = BuilderRegisterCountdownControl.consume := rfl
example : consumeNode.onAccept = .node decrementNode.reference := rfl
example : consumeNode.onReject = .node eraseNode.reference := rfl
example : copyNode.program = RegisterCopy.machine 0 := rfl
example : copyNode.onAccept = .node consumeNode.reference := rfl
example : eraseNode.program = BuilderRegisterErase.oneMachine := rfl
example : eraseNode.onAccept = .accept := rfl
example : graph.WellFormed := graph_wellFormed

example (upper : Nat) : values upper 0 = [] := rfl
example : values 5 3 = [4, 3, 2] := rfl
example : values 3 3 = [2, 1, 0] := rfl
example : values 0 0 = [] := rfl
example (upper count : Nat) : (values upper count).length = count := values_length upper count
example (upper count : Nat) (index : Fin count) :
    (values upper count)[index.val]'(by rw [values_length]; exact index.isLt) = upper - (index.val + 1) :=
  values_index upper count index
example (upper count item : Nat) (h : item ∈ values upper count) : item ≤ upper := values_le upper count item h

example (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) (hCount : count ≤ upper) :
    workRunExact? machine (workSteps count upper)
      (workStartConfiguration machine (endTape (older ++ [count, upper]) inside [])) =
      some {
        state := machine.acceptState
        tape := endTape (older ++ [count] ++ values upper count) inside
          (List.replicate (upper - count + 1) .blank) } :=
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

example (count upper : Nat) (older : List Nat) :
    (older ++ [count] ++ values upper count).length = older.length + 1 + count :=
  final_register_count count upper older

example (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count upper older inside).tape.right =
      (registerWord (values upper count)).reverse ++
        ((registerWord (older ++ [count])).reverse ++ inside) := final_inside_preserved count upper older inside

example (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count upper older inside).tape.left = List.replicate (upper - count + 1) .blank :=
  final_exterior count upper older inside

-- The zero-count endpoint removes the original working register, not the counter.
example (upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration 0 upper older inside).tape =
      endTape (older ++ [0]) inside (List.replicate (upper + 1) .blank) := by
  simp only [finalConfiguration, finalTape, values, Nat.sub_zero, List.append_nil]

example (spent value : Nat) (emitted : List Nat) :
    loopSteps spent 0 emitted value =
      BuilderRegisterCountdownControl.exhaustedSteps spent (emitted ++ [value]) + value + 4 := by
  simp only [loopSteps]
  omega

example (spent remaining value : Nat) (emitted : List Nat) :
    loopSteps spent (remaining + 1) emitted value =
      BuilderRegisterCountdownControl.consumeSteps spent (remaining + 1) (emitted ++ [value]) +
        RegisterCopy.steps [] (value - 1) +
        loopSteps (spent + 1) remaining (emitted ++ [value - 1]) (value - 1) + 5 := by
  simp only [loopSteps]
  omega

example (spent remaining value bound : Nat) (emitted : List Nat)
    (hCounter : spent + remaining ≤ bound) (hBudget : emitted.length + remaining ≤ bound)
    (hValues : ∀ item ∈ emitted, item ≤ bound) (hValue : value ≤ bound) :
    loopSteps spent remaining emitted value ≤ (remaining + 1) * (20 * ((bound + 1) * (bound + 1))) :=
  loopSteps_le spent remaining value bound emitted hCounter hBudget hValues hValue

example (count upper bound : Nat) (hCount : count ≤ bound) (hUpper : upper ≤ bound) :
    workSteps count upper ≤ 30 * ((bound + 1) * (bound + 1) * (bound + 1)) :=
  workSteps_le count upper bound hCount hUpper

example (count upper bound : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ bound) (hUpper : upper ≤ bound) (hOlder : (registerWord older).length ≤ bound) :
    (registerWord (older ++ [count] ++ values upper count)).length +
      (finalConfiguration count upper older inside).tape.left.length ≤ 4 * ((bound + 1) * (bound + 1)) :=
  output_span_le count upper bound older inside hCount hUpper hOlder

example (bound : NatPolynomial) (inputLength count upper : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ bound.eval inputLength) (hUpper : upper ≤ bound.eval inputLength)
    (hOlder : (registerWord older).length ≤ bound.eval inputLength) :
    (registerWord (older ++ [count] ++ values upper count)).length +
        (finalConfiguration count upper older inside).tape.left.length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count upper ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds bound inputLength count upper older inside hCount hUpper hOlder

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderRegisterDescendingRange.Regression
