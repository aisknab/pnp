/-
Copyright (c) 2026 PNP Labs.
The unary tag test must be uniform in tape contents and restore both outcomes.
-/
import PNP.Concrete.CookLevinBuilderUnaryTagMatch

namespace PNP.Concrete.CookLevin.BuilderUnaryTagMatch.Regression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example (expected actual : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine expected) (workSteps expected actual)
      (workStartConfiguration (machine expected) (endTape (older ++ [actual]) inside outside)) =
      some (finalConfiguration expected actual older inside outside) :=
  workRunExact expected actual older inside outside

example (expected : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine expected) (workSteps expected expected)
      (workStartConfiguration (machine expected) (endTape (older ++ [expected]) inside outside)) =
      some { state := (machine expected).acceptState, tape := endTape (older ++ [expected]) inside outside } :=
  accept_workRunExact expected older inside outside

example (expected actual : Nat) (older : List Nat) (inside outside : List WorkSymbol) (h : actual ≠ expected) :
    workRunExact? (machine expected) (workSteps expected actual)
      (workStartConfiguration (machine expected) (endTape (older ++ [actual]) inside outside)) =
      some { state := (machine expected).rejectState, tape := endTape (older ++ [actual]) inside outside } :=
  reject_workRunExact expected actual older inside outside h

example (expected actual : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine (machine expected)) (6 * workSteps expected actual)
      (encodeWorkConfiguration (workStartConfiguration (machine expected)
        (endTape (older ++ [actual]) inside outside))) =
      encodeWorkConfiguration (finalConfiguration expected actual older inside outside) :=
  run_compile_exact expected actual older inside outside

example (expected actual : Nat) : workSteps expected actual ≤ 2 * expected + 3 :=
  workSteps_le expected actual

example (expected : Nat) : (machine expected).rules.length = 9 * (expected + 4) := rules_length expected

example (expected : Nat) : (machine expected).rules.Pairwise WorkMachineChain.QueryDistinct :=
  rules_pairwise_query_distinct expected

example (expected : Nat) : WorkMachineChain.NoRuleAtAccept (machine expected) := noRuleAtAccept expected

example (expected : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine expected) (machine expected).rejectState := noRuleAtReject expected

example (expected : Nat) : (machine expected).acceptState ≠ (machine expected).rejectState :=
  acceptState_ne_rejectState expected

example (expected : Nat) (tape : WorkTape) (hHead : tape.head ≠ scratchEndSymbol) :
    workStep? (machine expected) (workStartConfiguration (machine expected) tape) =
      some { state := expected + 6, tape := tape } :=
  invalid_entry expected tape hHead

-- Literal executions do not use the correctness theorem as a decision oracle.
example : workRunExact? (machine 0) 3
    (workStartConfiguration (machine 0) (endTape [0] [] [])) =
    some { state := (machine 0).acceptState, tape := endTape [0] [] [] } := by decide

example : workRunExact? (machine 1) 5
    (workStartConfiguration (machine 1) (endTape [1] [] [])) =
    some { state := (machine 1).acceptState, tape := endTape [1] [] [] } := by decide

example : workRunExact? (machine 2) 7
    (workStartConfiguration (machine 2) (endTape [2] [] [])) =
    some { state := (machine 2).acceptState, tape := endTape [2] [] [] } := by decide

example : workRunExact? (machine 3) 9
    (workStartConfiguration (machine 3) (endTape [3] [] [])) =
    some { state := (machine 3).acceptState, tape := endTape [3] [] [] } := by decide

example : workRunExact? (machine 4) 11
    (workStartConfiguration (machine 4) (endTape [4] [] [])) =
    some { state := (machine 4).acceptState, tape := endTape [4] [] [] } := by decide

example : workRunExact? (machine 4) 3
    (workStartConfiguration (machine 4) (endTape [0] [] [])) =
    some { state := (machine 4).rejectState, tape := endTape [0] [] [] } := by decide

example : workRunExact? (machine 4) 9
    (workStartConfiguration (machine 4) (endTape [3] [] [])) =
    some { state := (machine 4).rejectState, tape := endTape [3] [] [] } := by decide

example : workRunExact? (machine 4) 11
    (workStartConfiguration (machine 4) (endTape [7, 5] [.blank, .oneOne] [.zeroBlank])) =
    some { state := (machine 4).rejectState, tape := endTape [7, 5] [.blank, .oneOne] [.zeroBlank] } := by decide

example : workRunExact? (machine 0) 3
    (workStartConfiguration (machine 0) (endTape [2, 8] [.oneBlank] [.blank, .zeroOne])) =
    some { state := (machine 0).rejectState, tape := endTape [2, 8] [.oneBlank] [.blank, .zeroOne] } := by decide

example : workRunExact? (machine 2) 7
    (workStartConfiguration (machine 2) (endTape [0, 7, 2] [.blank, .oneBlank] [.zeroOne])) =
    some { state := (machine 2).acceptState, tape := endTape [0, 7, 2] [.blank, .oneBlank] [.zeroOne] } := by decide

example : workRunExact? (machine 1) 2
    (workStartConfiguration (machine 1) WorkTape.blank) = none := by decide

example : workRunExact? (machine 1) 3
    (workStartConfiguration (machine 1)
      { left := [], head := scratchEndSymbol, right := [.blank] }) = none := by decide

example : workSteps 4 1000000 = 11 := by decide

example : workSteps 0 1000000 = 3 := by decide

end PNP.Concrete.CookLevin.BuilderUnaryTagMatch.Regression
