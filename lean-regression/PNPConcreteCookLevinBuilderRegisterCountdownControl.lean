/-
Copyright (c) 2026 PNP Labs.
Prepared countdown-control contracts for the complete descending-range loop.
No finite input fixture substitutes for these universal execution statements.
-/
import PNP.Concrete.CookLevinBuilderRegisterCountdownControl

namespace PNP.Concrete.CookLevin.BuilderRegisterCountdownControl.Regression

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example : markCounterMachine.rules.length = 8 := initialize_rules_length
example : consume.rules.length = 17 := consume_rules_length
example : decrement.rules.length = 2 := decrement_rules_length
example : counterMarker ≠ unitSymbol := by decide
example : counterMarker ≠ separatorSymbol := by decide
example : counterMarker ≠ spentSymbol := by decide
example : spentSymbol ≠ unitSymbol := by decide

example (count value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? markCounterMachine (initializeSteps count value)
      (workStartConfiguration markCounterMachine (restoredTape count [value] inside outside)) =
      some {
      state := markCounterMachine.acceptState
      tape := markedTape 0 count [value] inside outside } :=
  initialize_workRunExact count value inside outside

example (value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? markCounterMachine (initializeSteps 0 value)
      (workStartConfiguration markCounterMachine (restoredTape 0 [value] inside outside)) =
      some {
      state := markCounterMachine.acceptState
      tape := markedTape 0 0 [value] inside outside } :=
  initialize_workRunExact 0 value inside outside

example (spent remaining : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? consume (consumeSteps spent (remaining + 1) newer)
      (workStartConfiguration consume (markedTape spent (remaining + 1) newer inside outside)) =
      some {
      state := consume.acceptState
      tape := markedTape (spent + 1) remaining newer inside outside } :=
  consume_workRunExact spent remaining newer inside outside

example (spent : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? consume (consumeSteps spent 1 newer)
      (workStartConfiguration consume (markedTape spent 1 newer inside outside)) =
      some {
      state := consume.acceptState
      tape := markedTape (spent + 1) 0 newer inside outside } :=
  consume_workRunExact spent 0 newer inside outside

example (spent : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? consume (exhaustedSteps spent newer)
      (workStartConfiguration consume (markedTape spent 0 newer inside outside)) =
      some {
      state := consume.rejectState
      tape := restoredTape spent newer inside outside } :=
  exhausted_workRunExact spent newer inside outside

example (spent : Nat) (inside outside : List WorkSymbol) :
    workRunExact? consume (exhaustedSteps spent [])
      (workStartConfiguration consume (markedTape spent 0 [] inside outside)) =
      some {
      state := consume.rejectState
      tape := restoredTape spent [] inside outside } :=
  exhausted_workRunExact spent [] inside outside

example (value : Nat) (older inside outside : List WorkSymbol) :
    workRunExact? decrement 2
      (workStartConfiguration decrement
        {
          left := outside
          head := scratchEndSymbol
          right := List.replicate (value + 1) unitSymbol ++ separatorSymbol :: (older.reverse ++ inside) }) =
      some { state := decrement.acceptState, tape :=
        {
          left := WorkSymbol.blank :: outside
          head := scratchEndSymbol
          right := List.replicate value unitSymbol ++ separatorSymbol :: (older.reverse ++ inside) } } :=
  decrement_workRunExact value older inside outside

-- Underflow cannot impersonate a successful decrement.
example (older inside outside : List WorkSymbol) :
    workRunExact? decrement 2
      (workStartConfiguration decrement
        { left := outside, head := scratchEndSymbol, right := separatorSymbol :: (older.reverse ++ inside) }) = none := by
  rfl

example (count value : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine markCounterMachine) (6 * initializeSteps count value)
      (encodeWorkConfiguration (workStartConfiguration markCounterMachine (restoredTape count [value] inside outside))) =
      encodeWorkConfiguration {
      state := markCounterMachine.acceptState
      tape := markedTape 0 count [value] inside outside } :=
  initialize_run_compile_exact count value inside outside

example (spent remaining : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine consume) (6 * consumeSteps spent (remaining + 1) newer)
      (encodeWorkConfiguration (workStartConfiguration consume (markedTape spent (remaining + 1) newer inside outside))) =
      encodeWorkConfiguration {
      state := consume.acceptState
      tape := markedTape (spent + 1) remaining newer inside outside } :=
  consume_run_compile_exact spent remaining newer inside outside

example (spent : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine consume) (6 * exhaustedSteps spent newer)
      (encodeWorkConfiguration (workStartConfiguration consume (markedTape spent 0 newer inside outside))) =
      encodeWorkConfiguration {
      state := consume.rejectState
      tape := restoredTape spent newer inside outside } :=
  exhausted_run_compile_exact spent newer inside outside

example (count : Nat) (newer older : List Nat) (inside outside : List WorkSymbol) :
    restoredTape count newer ((registerWord older).reverse ++ inside) outside =
      endTape (older ++ count :: newer) inside outside :=
  restoredTape_eq_endTape count newer older inside outside

example (spent remaining : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    (markedTape spent remaining newer inside outside).left = outside := rfl

example (spent remaining : Nat) (newer : List Nat) (inside outside : List WorkSymbol) :
    (markedTape spent remaining newer inside outside).right.length =
      (registerWord newer).length + remaining + spent + 1 + inside.length :=
  markedTape_span spent remaining newer inside outside

example (spent remaining bound : Nat) (newer : List Nat)
    (hCounter : spent + remaining ≤ bound) (hWord : (registerWord newer).length ≤ bound) :
    consumeSteps spent remaining newer ≤ 4 * bound + 3 := consumeSteps_le spent remaining bound newer hCounter hWord

example (spent bound : Nat) (newer : List Nat)
    (hCounter : spent ≤ bound) (hWord : (registerWord newer).length ≤ bound) :
    exhaustedSteps spent newer ≤ 6 * bound + 5 := exhaustedSteps_le spent bound newer hCounter hWord

example : markCounterMachine.rules.Pairwise WorkMachineChain.QueryDistinct := initialize_control.1
example : consume.rules.Pairwise WorkMachineChain.QueryDistinct := consume_control.1
example : decrement.rules.Pairwise WorkMachineChain.QueryDistinct := decrement_control.1
example : WorkMachineProgramGraph.NoRuleAt markCounterMachine markCounterMachine.acceptState := initialize_control.2.1
example : WorkMachineProgramGraph.NoRuleAt consume consume.acceptState := consume_control.2.1
example : WorkMachineProgramGraph.NoRuleAt decrement decrement.acceptState := decrement_control.2.1
example : WorkMachineProgramGraph.NoRuleAt markCounterMachine markCounterMachine.rejectState := initialize_control.2.2.1
example : WorkMachineProgramGraph.NoRuleAt consume consume.rejectState := consume_control.2.2.1
example : WorkMachineProgramGraph.NoRuleAt decrement decrement.rejectState := decrement_control.2.2.1
example : markCounterMachine.acceptState ≠ markCounterMachine.rejectState := initialize_control.2.2.2
example : consume.acceptState ≠ consume.rejectState := consume_control.2.2.2
example : decrement.acceptState ≠ decrement.rejectState := decrement_control.2.2.2

end PNP.Concrete.CookLevin.BuilderRegisterCountdownControl.Regression
