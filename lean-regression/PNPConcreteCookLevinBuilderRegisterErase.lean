/-
Copyright (c) 2026 PNP Labs.
General fixed-count erasure contracts prepared before verification.
The retained frame and exterior must survive, and removed cells must be blank.
-/
import PNP.Concrete.CookLevinBuilderRegisterErase
import PNP.Concrete.CookLevinBuilderRegionResidualSelection

namespace PNP.Concrete.CookLevin.BuilderRegisterErase.Regression

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)

example : oneMachine.rules.length = 3 := one_rules_length
example : oneMachine.rules.Pairwise WorkMachineChain.QueryDistinct := one_rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept oneMachine := one_noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt oneMachine oneMachine.rejectState := one_noRuleAtReject
example : oneMachine.acceptState ≠ oneMachine.rejectState := one_acceptState_ne_rejectState

example (older : List Nat) (value : Nat) (inside outside : List WorkSymbol) :
    workRunExact? oneMachine (value + 2)
      (workStartConfiguration oneMachine (endTape (older ++ [value]) inside outside)) =
      some {
        state := oneMachine.acceptState
        tape := endTape older inside (List.replicate (value + 1) .blank ++ outside) } :=
  one_workRunExact older value inside outside

example (older : List Nat) (value : Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine oneMachine) (6 * (value + 2))
      (encodeWorkConfiguration (workStartConfiguration oneMachine (endTape (older ++ [value]) inside outside))) =
      encodeWorkConfiguration {
        state := oneMachine.acceptState
        tape := endTape older inside (List.replicate (value + 1) .blank ++ outside) } :=
  one_run_compile_exact older value inside outside

example (inside outside : List WorkSymbol) :
    workStep? oneMachine (workStartConfiguration oneMachine
      { left := outside, head := .blank, right := inside }) = none := rfl

example (count : Nat) (older values : List Nat) (inside outside : List WorkSymbol)
    (hCount : values.length = count) :
    workRunExact? (machine count) (workSteps values) (initialConfiguration count older values inside outside) =
      some (finalConfiguration count older values inside outside) :=
  workRunExact count older values inside outside hCount

example (count : Nat) (older values : List Nat) (inside outside : List WorkSymbol)
    (hCount : values.length = count) :
    run (compileWorkMachine (machine count)) (6 * workSteps values)
      (encodeWorkConfiguration (initialConfiguration count older values inside outside)) =
      encodeWorkConfiguration (finalConfiguration count older values inside outside) :=
  run_compile_exact count older values inside outside hCount

example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine 0) 0 (initialConfiguration 0 older [] inside outside) =
      some (finalConfiguration 0 older [] inside outside) :=
  workRunExact 0 older [] inside outside rfl

example (count : Nat) (older values : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count older values inside outside).tape.right =
      (registerWord older).reverse ++ inside := final_inside_preserved count older values inside outside
example (count : Nat) (older values : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count older values inside outside).tape.left =
      List.replicate (registerWord values).length .blank ++ outside := final_outside_preserved count older values inside outside
example (count : Nat) (older values : List Nat) (inside : List WorkSymbol) (secret : WorkSymbol) :
    (finalConfiguration count older values inside [secret]).tape.left ≠ [] := by
  simp only [finalConfiguration, endTape]
  intro h
  have hLength := congrArg List.length h
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at hLength
  omega
example (value : Nat) : clearedSpan [value] = value + 1 := by
  simp only [clearedSpan, registerWord, List.append_nil, List.length_cons, List.length_replicate]
example (values : List Nat) : values.length ≤ clearedSpan values := length_le_clearedSpan values
example (values : List Nat) : workSteps values ≤ 3 * clearedSpan values := workSteps_le values
example (bound : NatPolynomial) (inputLength : Nat) (values : List Nat)
    (hSpan : clearedSpan values ≤ bound.eval inputLength) :
    6 * workSteps values ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bound bound inputLength values hSpan

example (result : BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? (machine 4) (workSteps (BuilderRegionResidualSelection.scratchValues result))
      (initialConfiguration 4 older (BuilderRegionResidualSelection.scratchValues result) inside outside) =
      some (finalConfiguration 4 older (BuilderRegionResidualSelection.scratchValues result) inside outside) :=
  workRunExact 4 older _ inside outside (BuilderRegionResidualSelection.scratchValues_length result)

example (count : Nat) : (machine count).rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct count
example (count : Nat) : WorkMachineChain.NoRuleAtAccept (machine count) := noRuleAtAccept count
example (count : Nat) : WorkMachineProgramGraph.NoRuleAt (machine count) (machine count).rejectState := noRuleAtReject count
example (count : Nat) : (machine count).acceptState ≠ (machine count).rejectState := acceptState_ne_rejectState count

end PNP.Concrete.CookLevin.BuilderRegisterErase.Regression
