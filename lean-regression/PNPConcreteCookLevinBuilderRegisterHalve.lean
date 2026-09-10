import PNP.Concrete.CookLevinBuilderRegisterHalve

namespace PNP.Concrete.CookLevin.BuilderRegisterHalveRegression

open BuilderRegisterHalve
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example (value : Nat) : BuilderRegisterPack.values prepareFields (prepareEnvironment value) = [0, 0, value, 2] :=
  prepare_values value
example (value : Nat) : List.ofFn (resultEnvironment value) = restoredValues value := resultEnvironment_ofFn value
example (value : Nat) : BuilderRegisterPack.values resultFields (resultEnvironment value) = [value / 2, value % 2] :=
  result_values value
example (value : Nat) : (outputValues value).length = 9 := outputValues_length value
example : outputValues 0 = [0, 0, 0, 0, 0, 2, 0, 0, 0] := by decide
example : outputValues 1 = [1, 0, 0, 0, 1, 2, 0, 0, 1] := by decide
example : outputValues 2 = [2, 0, 0, 2, 0, 2, 1, 1, 0] := by decide
example : outputValues 3 = [3, 0, 0, 2, 1, 2, 1, 1, 1] := by decide
example : outputValues 4 = [4, 0, 0, 4, 0, 2, 2, 2, 0] := by decide
example : outputValues 17 = [17, 0, 0, 16, 1, 2, 8, 8, 1] := by decide
example : (outputValues 3)[7]? = some 1 := by decide
example : (outputValues 3)[8]? = some 1 := by decide
example : (outputValues 4)[8]? = some 0 := by decide
example : (outputValues 17)[7]? ≠ some 9 := by decide
example : (outputValues 17)[8]? ≠ some 0 := by decide
example (value : Nat) : (outputValues value)[7]? = some (value / 2) := output_quotient value
example (value : Nat) : (outputValues value)[8]? = some (value % 2) := output_remainder value
example (value : Nat) : (value / 2) * 2 + value % 2 = value := quotient_remainder_reconstruct value
example (value : Nat) : value % 2 < 2 := remainder_lt_two value
example (value : Nat) : (registerWord (outputValues value)).length = 3 * value + 11 := output_span value

example (remaining length width coordinate : Nat) :
    BuilderInitialRowLoop.finishOutside remaining length width coordinate [] = [] :=
  row_loop_frontier remaining length width coordinate
example : BuilderInitialRowLoop.finishOutside 0 0 0 0 [] = [] := row_loop_frontier 0 0 0 0
example : BuilderInitialRowLoop.finishOutside 2 0 0 0 [] = [] := row_loop_frontier 2 0 0 0
example : BuilderInitialRowLoop.finishOutside 2 0 2 5 [] = [] := row_loop_frontier 2 0 2 5
example (remaining length width coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (BuilderInitialRowLoop.finalConfiguration remaining length width coordinate older inside []).tape.left = [] :=
  row_loop_final_frontier remaining length width coordinate older inside

example (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (BuilderClauseDividerExecution.divisionFinal 0 value 2 (older ++ [value]) inside).tape =
      BuilderDividerCoordinateRegisters.inputTape (view value)
        ((registerWord (older ++ [value])).reverse ++ inside) [] :=
  division_restore_handoff value older inside

example (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps value) (initialConfiguration value older inside) =
      some (finalConfiguration value older inside) := workRunExact value older inside
example (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 0) (initialConfiguration 0 older inside) =
      some {state := machine.acceptState, tape := endTape (older ++ [0, 0, 0, 0, 0, 2, 0, 0, 0]) inside []} :=
  workRunExact 0 older inside
example (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps 3) (initialConfiguration 3 older inside) =
      some {state := machine.acceptState, tape := endTape (older ++ [3, 0, 0, 2, 1, 2, 1, 1, 1]) inside []} :=
  workRunExact 3 older inside
example :
    workRunExact? machine (workSteps 4) (initialConfiguration 4 [7, 1] [.oneBlank, .blank, .zeroOne]) =
      some (finalConfiguration 4 [7, 1] [.oneBlank, .blank, .zeroOne]) :=
  workRunExact 4 [7, 1] [.oneBlank, .blank, .zeroOne]

example (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps value)
      (encodeWorkConfiguration (initialConfiguration value older inside)) =
      encodeWorkConfiguration (finalConfiguration value older inside) := run_compile_exact value older inside
example (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration value older inside).tape =
      endTape (older ++ [value] ++ restoredValues value ++ [value / 2, value % 2]) inside [] :=
  final_tape value older inside
example (value : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration value older inside).tape.left = [] := final_frontier value older inside
example (value : Nat) (older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [value])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ outputValues value)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps value ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds value older bound inputLength hSpan

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderRegisterHalveRegression
