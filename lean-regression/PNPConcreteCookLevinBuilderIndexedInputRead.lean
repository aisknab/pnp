/-
Copyright (c) 2026 PNP Labs.
Indexed source reads must use one fixed machine, preserve source/output and
retained registers, return absence past the source, and charge every scan.
-/
import PNP.Concrete.CookLevinBuilderIndexedInputRead

namespace PNP.Concrete.CookLevin.BuilderIndexedInputRead.Regression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape inside)

example : machine.rules.length = 162 := rules_length
example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState
example : machine.startState = 0 := rfl
example : machine.acceptState = 18 := rfl
example : machine.rejectState = 19 := rfl

example : resultCode none = 0 := rfl
example : resultCode (some false) = 1 := rfl
example : resultCode (some true) = 2 := rfl
example (value : Option Bool) : resultCode value ≤ 2 := resultCode_le value
example : resultCode none ≠ resultCode (some false) := by decide
example : resultCode (some false) ≠ resultCode (some true) := by decide

example (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) :
    workRunExact? machine (workSteps older index input)
      (initialConfiguration older index input output tail) =
      some (finalConfiguration older index input output tail) :=
  workRunExact older index input output tail

example (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps older index input)
      (encodeWorkConfiguration (initialConfiguration older index input output tail)) =
      encodeWorkConfiguration (finalConfiguration older index input output tail) :=
  run_compile_exact older index input output tail

example (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) :
    (finalConfiguration older index input output tail).tape =
      endTape (older ++ [index, resultCode input[index]?]) (inside input output)
        (tail.drop (resultCode input[index]? + 1)) := final_tape older index input output tail

example (older : List Nat) (index : Nat) (input : BitString)
    (output : List CNFToken) (tail : List WorkSymbol) :
    (finalConfiguration older index input output tail).state = machine.acceptState :=
  final_accept older index input output tail

example (older : List Nat) (index : Nat) (output : List CNFToken) (tail : List WorkSymbol) :
    workRunExact? machine (workSteps older index [])
      (initialConfiguration older index [] output tail) =
      some
        { state := machine.acceptState
          tape := endTape (older ++ [index, 0]) (inside [] output) (tail.drop 1) } :=
  workRunExact older index [] output tail

example (older : List Nat) (output : List CNFToken) (tail : List WorkSymbol) :
    workRunExact? machine (workSteps older 1 [true, false])
      (initialConfiguration older 1 [true, false] output tail) =
      some
        { state := machine.acceptState
          tape := endTape (older ++ [1, 1]) (inside [true, false] output) (tail.drop 2) } :=
  workRunExact older 1 [true, false] output tail

example (older : List Nat) (output : List CNFToken) (tail : List WorkSymbol) :
    workRunExact? machine (workSteps older 1 [false, true])
      (initialConfiguration older 1 [false, true] output tail) =
      some
        { state := machine.acceptState
          tape := endTape (older ++ [1, 2]) (inside [false, true] output) (tail.drop 3) } :=
  workRunExact older 1 [false, true] output tail

example (older : List Nat) (output : List CNFToken) (tail : List WorkSymbol) :
    workRunExact? machine (workSteps older 2 [false, true])
      (initialConfiguration older 2 [false, true] output tail) =
      some
        { state := machine.acceptState
          tape := endTape (older ++ [2, 0]) (inside [false, true] output) (tail.drop 1) } :=
  workRunExact older 2 [false, true] output tail

example : workSteps [] 0 [] = 8 := rfl
example : workSteps [] 0 [false] = 9 := rfl
example : workSteps [] 0 [true] = 10 := rfl
example : workSteps [] 1 [] = 10 := rfl
example : workSteps [] 2 [] = 12 := rfl
example : workSteps [] 1 [true, false] = 22 := rfl
example : workSteps [] 1 [false, true] = 23 := rfl
example : workSteps [] 2 [false, true] = 40 := rfl
example : workSteps [] 3 [false, true] = 46 := rfl
example : workSteps [2, 1] 0 [true] = 20 := rfl

-- Independent literal executions check the fixed table, not just cost formulas.
example : workRunExact? machine 8 (initialConfiguration [] 0 [] [] []) =
    some (finalConfiguration [] 0 [] [] []) := by rfl
example : workRunExact? machine 9 (initialConfiguration [] 0 [false] [] []) =
    some (finalConfiguration [] 0 [false] [] []) := by rfl
example : workRunExact? machine 10 (initialConfiguration [] 0 [true] [] []) =
    some (finalConfiguration [] 0 [true] [] []) := by rfl
example : workRunExact? machine 23 (initialConfiguration [] 1 [false, true] [] []) =
    some (finalConfiguration [] 1 [false, true] [] []) := by rfl
example : workRunExact? machine 40 (initialConfiguration [] 2 [false, true] [] []) =
    some (finalConfiguration [] 2 [false, true] [] []) := by rfl

example (output : List CNFToken) (tail : List WorkSymbol) :
    workRunExact? machine 8 (initialConfiguration [] 0 [] output tail) =
      some (finalConfiguration [] 0 [] output tail) := workRunExact [] 0 [] output tail

example : workRunExact? machine 8
    (initialConfiguration [] 0 [] [.t, .finish, .f, .sep] [.oneZero, .zeroBlank, .oneOne]) =
      some (finalConfiguration [] 0 [] [.t, .finish, .f, .sep] [.oneZero, .zeroBlank, .oneOne]) := by rfl

example (olderLength seen remaining : Nat) (input : BitString) :
    loopSteps olderLength seen remaining input ≤
      (remaining + 1) * (2 * olderLength + 6 * (seen + remaining) + 12) :=
  loopSteps_le olderLength seen remaining input

example (older : List Nat) (index : Nat) (input : BitString) :
    workSteps older index input ≤
      (index + 1) * (2 * (registerWord older).length + 6 * index + 12) :=
  workSteps_le older index input

example (bound : NatPolynomial) (inputLength : Nat) :
    (rawTimePolynomial bound).eval inputLength =
      6 * ((bound.eval inputLength + 1) * (8 * bound.eval inputLength + 12)) :=
  rawTimePolynomial_eval bound inputLength

example (bound : NatPolynomial) (older : List Nat) (index : Nat) (input : BitString)
    (hOlder : (registerWord older).length ≤ bound.eval input.length)
    (hIndex : index ≤ bound.eval input.length) :
    6 * workSteps older index input ≤ (rawTimePolynomial bound).eval input.length :=
  rawTimeBound_le bound older index input hOlder hIndex

example (older : List Nat) (index : Nat) (input : BitString) :
    (registerWord (older ++ [index, resultCode input[index]?])).length =
      (registerWord (older ++ [index])).length + resultCode input[index]? + 1 :=
  register_span_added older index input

example (older : List Nat) (index : Nat) (input : BitString) :
    (registerWord (older ++ [index, resultCode input[index]?])).length ≤
      (registerWord (older ++ [index])).length + 3 := register_span_increase_le older index input

example (tape : WorkTape) (hHead : tape.head ≠ scratchEndSymbol) :
    workRunExact? machine 1 (workStartConfiguration machine tape) =
      some { state := 20, tape := tape } := invalid_entry tape hHead

end PNP.Concrete.CookLevin.BuilderIndexedInputRead.Regression
