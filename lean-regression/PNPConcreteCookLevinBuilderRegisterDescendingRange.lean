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

-- Retain the marker for the following fixed metadata pass; never select a runtime-sized graph.
example : machine = machineWith separatorSymbol := rfl
example (delimiter : WorkSymbol) : (graphWith delimiter).nodes.length = 5 := rfl
example (delimiter : WorkSymbol) : (graphWith delimiter).WellFormed := graphWith_wellFormed delimiter
example (delimiter : WorkSymbol) : copyNode.onAccept = .node (consumeNodeWith delimiter).reference := rfl
example (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ upper) :
    workRunExact? (machineWith delimiter) (workSteps count upper)
      (workStartConfiguration (machineWith delimiter) (endTape (older ++ [count, upper]) inside [])) =
      some {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWith delimiter count upper older inside } :=
  workRunExactWith delimiter count upper older inside hCount
example (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) (hCount : count ≤ upper) :
    workRunExact? (machineWith BuilderRegisterCountdownControl.counterMarker) (workSteps count upper)
      (workStartConfiguration (machineWith BuilderRegisterCountdownControl.counterMarker)
        (endTape (older ++ [count, upper]) inside [])) =
      some {
        state := (machineWith BuilderRegisterCountdownControl.counterMarker).acceptState
        tape := BuilderRegisterCountdownControl.markedTape 0 count (values upper count)
          ((registerWord older).reverse ++ inside) (List.replicate (upper - count + 1) .blank) } := by
  simpa only [finalTapeWith_marker] using
    workRunExactWith BuilderRegisterCountdownControl.counterMarker count upper older inside hCount
example (delimiter : WorkSymbol) (upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? (machineWith delimiter) (workSteps 0 upper)
      (workStartConfiguration (machineWith delimiter) (endTape (older ++ [0, upper]) inside [])) =
      some {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWith delimiter 0 upper older inside } :=
  workRunExactWith delimiter 0 upper older inside (Nat.zero_le _)
example (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hCount : count ≤ upper) :
    run (compileWorkMachine (machineWith delimiter)) (6 * workSteps count upper)
      (encodeWorkConfiguration
        (workStartConfiguration (machineWith delimiter) (endTape (older ++ [count, upper]) inside []))) =
      encodeWorkConfiguration {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWith delimiter count upper older inside } :=
  run_compile_exactWith delimiter count upper older inside hCount
example (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalTapeWith delimiter count upper older inside).left = List.replicate (upper - count + 1) .blank := rfl
example (delimiter : WorkSymbol) : (machineWith delimiter).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rulesWith_pairwise_query_distinct delimiter
example (delimiter : WorkSymbol) : WorkMachineChain.NoRuleAtAccept (machineWith delimiter) := noRuleWithAtAccept delimiter
example (delimiter : WorkSymbol) :
    WorkMachineProgramGraph.NoRuleAt (machineWith delimiter) (machineWith delimiter).rejectState :=
  noRuleWithAtReject delimiter
example (delimiter : WorkSymbol) : (machineWith delimiter).acceptState ≠ (machineWith delimiter).rejectState :=
  acceptWith_ne_rejectState delimiter

-- Arbitrary pre-existing exterior is preserved except for exactly charged allocation.
example (count upper : Nat) (outside : List WorkSymbol) :
    exteriorFrom count upper outside =
      List.replicate (upper - count + 1) .blank ++ outside.drop (values upper count).sum := rfl
example (upper : Nat) (outside : List WorkSymbol) :
    exteriorFrom 0 upper outside = List.replicate (upper + 1) .blank ++ outside := by
  simp only [exteriorFrom, values, List.sum_nil, List.drop_zero, Nat.sub_zero]
example (outside : List WorkSymbol) : exteriorFrom 1 1 outside = [.blank] ++ outside := rfl
example (outside : List WorkSymbol) : exteriorFrom 3 5 outside = List.replicate 3 .blank ++ outside.drop 9 := rfl
example :
    exteriorFrom 3 5 (List.replicate 10 unitSymbol ++ [scratchEndSymbol]) =
      List.replicate 3 .blank ++ [unitSymbol, scratchEndSymbol] := rfl
example (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat) (inside : List WorkSymbol) :
    finalTapeWithOutside delimiter count upper older inside [] = finalTapeWith delimiter count upper older inside :=
  finalTapeWithOutside_nil delimiter count upper older inside
example (count upper : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    finalTapeWithOutside separatorSymbol count upper older inside outside =
      endTape (older ++ [count] ++ values upper count) inside (exteriorFrom count upper outside) :=
  finalTapeWithOutside_separator count upper older inside outside
example (count upper : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    finalTapeWithOutside BuilderRegisterCountdownControl.counterMarker count upper older inside outside =
      BuilderRegisterCountdownControl.markedTape 0 count (values upper count)
        ((registerWord older).reverse ++ inside) (exteriorFrom count upper outside) :=
  finalTapeWithOutside_marker count upper older inside outside
example (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (hCount : count ≤ upper) :
    workRunExact? (machineWith delimiter) (workSteps count upper)
      (workStartConfiguration (machineWith delimiter) (endTape (older ++ [count, upper]) inside outside)) =
      some {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWithOutside delimiter count upper older inside outside } :=
  workRunExactWithOutside delimiter count upper older inside outside hCount
example (delimiter : WorkSymbol) (count upper : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (hCount : count ≤ upper) :
    run (compileWorkMachine (machineWith delimiter)) (6 * workSteps count upper)
      (encodeWorkConfiguration
        (workStartConfiguration (machineWith delimiter) (endTape (older ++ [count, upper]) inside outside))) =
      encodeWorkConfiguration {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWithOutside delimiter count upper older inside outside } :=
  run_compile_exactWithOutside delimiter count upper older inside outside hCount
example (delimiter : WorkSymbol) (upper : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machineWith delimiter) (workSteps 0 upper)
      (workStartConfiguration (machineWith delimiter) (endTape (older ++ [0, upper]) inside outside)) =
      some {
        state := (machineWith delimiter).acceptState
        tape := finalTapeWithOutside delimiter 0 upper older inside outside } :=
  workRunExactWithOutside delimiter 0 upper older inside outside (Nat.zero_le _)
example (count upper : Nat) (outside : List WorkSymbol) :
    (exteriorFrom count upper outside).length ≤ upper - count + 1 + outside.length :=
  exteriorFrom_length_le count upper outside
example (delimiter : WorkSymbol) (count upper bound : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (hCount : count ≤ bound) (hUpper : upper ≤ bound) (hOlder : (registerWord older).length ≤ bound) :
    (registerWord (older ++ [count] ++ values upper count)).length +
        (finalTapeWithOutside delimiter count upper older inside outside).left.length ≤
      4 * ((bound + 1) * (bound + 1)) + outside.length :=
  output_span_withOutside_le delimiter count upper bound older inside outside hCount hUpper hOlder
example (delimiter : WorkSymbol) (bound outsideBound : NatPolynomial) (inputLength count upper : Nat)
    (older : List Nat) (inside outside : List WorkSymbol)
    (hCount : count ≤ bound.eval inputLength) (hUpper : upper ≤ bound.eval inputLength)
    (hOlder : (registerWord older).length ≤ bound.eval inputLength)
    (hOutside : outside.length ≤ outsideBound.eval inputLength) :
    (registerWord (older ++ [count] ++ values upper count)).length +
        (finalTapeWithOutside delimiter count upper older inside outside).left.length ≤
      (NatPolynomial.add (spanPolynomial bound) outsideBound).eval inputLength ∧
    6 * workSteps count upper ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_boundsWithOutside delimiter bound outsideBound inputLength count upper older inside outside
    hCount hUpper hOlder hOutside

end PNP.Concrete.CookLevin.BuilderRegisterDescendingRange.Regression
