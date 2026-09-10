import PNP.Concrete.CookLevinBuilderInitialRowLoop

namespace PNP.Concrete.CookLevin.BuilderInitialRowLoopRegression

open BuilderInitialRowLoop
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)

example : graph.nodes.length = 5 := rfl
example : graph.WellFormed := graph_wellFormed
example : Advance.copyMachine Advance.lengthIndex 0 = RegisterCopy.machine 8 := rfl
example : Advance.copyMachine Advance.widthIndex 1 = RegisterCopy.machine 2 := rfl
example : Advance.copyMachine Advance.coordinateIndex 2 = RegisterCopy.machine 2 := rfl
example : Advance.copyMachine Advance.remainingIndex 3 = RegisterCopy.machine 8 := rfl
example : endpoint 0 3 0 = .reject := rfl
example : endpoint 1 3 2 = .accept := by decide
example : endpoint 1 3 3 = .reject := by decide
example : endpoint 2 2 2 = .accept := by decide
example : endpoint 2 2 4 = .accept := by decide
example : endpoint 2 2 5 = .reject := by decide
example : endpoint 2 0 0 = .accept := by decide
example : endpoint 1 0 0 = .reject := by decide
example : endpoint 3 0 2 = .accept := by decide
example : endpoint 3 0 3 = .reject := by decide
example : finishValues 0 7 4 9 = [7, 4, 9, 0] := rfl
example : finishValues 1 0 3 2 = [0, 3, 2, 0, 2, 0, 3, 3, 2] := by decide
example : finishValues 2 0 2 2 =
    [0, 2, 2, 1, 2, 0, 2, 2, 0, 1, 3, 0, 0, 0, 0, 3, 3, 0] := by decide
example : finishValues 2 0 0 0 =
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0] := by decide
example : Advance.values (attemptEnvironment 0 3 4 2) = [1, 4, 1, 2] := by decide
example : Advance.values (attemptEnvironment 0 3 4 2) ≠ [1, 4, 0, 2] := by decide
example : finishOutside 1 0 3 2 (List.replicate 30 .oneOne ++ [.zeroOne, .oneBlank]) =
    List.replicate 16 .oneOne ++ [.zeroOne, .oneBlank] := by decide
example : finishOutside 2 0 2 2 (List.replicate 40 .oneOne ++ [.zeroOne, .oneBlank]) =
    List.replicate 11 .oneOne ++ [.zeroOne, .oneBlank] := by decide
example : finishOutside 2 0 0 0 (List.replicate 30 .oneOne ++ [.zeroOne, .oneBlank]) =
    List.replicate 13 .oneOne ++ [.zeroOne, .oneBlank] := by decide
example (remaining length width coordinate : Nat) : (attemptValues length width coordinate remaining).length = 9 :=
  attemptValues_length length width coordinate remaining

example (older : List Nat) (environment : Fin 9 → Nat) (inside outside : List WorkSymbol) :
    workRunExact? Advance.machine (Advance.workSteps environment)
      (workStartConfiguration Advance.machine (endTape (older ++ List.ofFn environment) inside outside)) =
      some {
        state := Advance.machine.acceptState
        tape := endTape (older ++ List.ofFn environment ++ Advance.values environment)
          inside (outside.drop (registerWord (Advance.values environment)).length) } :=
  Advance.workRunExact older environment inside outside

example (remaining length width coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps remaining length width coordinate)
      (initialConfiguration remaining length width coordinate older inside outside) =
      some (finalConfiguration remaining length width coordinate older inside outside) :=
  workRunExact remaining length width coordinate older inside outside

example (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps 2 0 0 0) (initialConfiguration 2 0 0 0 older inside outside) =
      some (finalConfiguration 2 0 0 0 older inside outside) := workRunExact 2 0 0 0 older inside outside

example (remaining length width coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps remaining length width coordinate)
      (encodeWorkConfiguration (initialConfiguration remaining length width coordinate older inside outside)) =
      encodeWorkConfiguration (finalConfiguration remaining length width coordinate older inside outside) :=
  run_compile_exact remaining length width coordinate older inside outside

example (remaining length width coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration remaining length width coordinate older inside outside).state = machine.acceptState ↔
      (BuilderInitialLengthSelection.locate remaining width coordinate).isSome = true :=
  final_accept_iff remaining length width coordinate older inside outside

example (remaining length width coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration remaining length width coordinate older inside outside).state = machine.rejectState ↔
      BuilderInitialLengthSelection.locate remaining width coordinate = none :=
  final_reject_iff remaining length width coordinate older inside outside

example (remaining length width coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration remaining length width coordinate older inside outside).tape =
      endTape (older ++ finishValues remaining length width coordinate) inside
        (finishOutside remaining length width coordinate outside) :=
  final_tape remaining length width coordinate older inside outside

example (remaining length width coordinate : Nat) (position : Fin remaining) (offset : Nat)
    (hFound : BuilderInitialLengthSelection.locate remaining width coordinate = some (position, offset)) :
    ∃ history middle : List Nat, middle.length = 7 ∧
      finishValues remaining length width coordinate = history ++ [length + position.val] ++ middle ++ [offset] :=
  found_suffix remaining length width coordinate position offset hFound

example (remaining length width coordinate bound : Nat)
    (hLength : length + remaining ≤ bound) (hWidth : width + remaining ≤ bound) (hCoordinate : coordinate ≤ bound) :
    (registerWord (finishValues remaining length width coordinate)).length ≤ (remaining + 1) * (9 * bound + 13) :=
  finish_span_le remaining length width coordinate bound hLength hWidth hCoordinate

example (remaining length width coordinate : Nat) (older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ frame length width coordinate remaining)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ finishValues remaining length width coordinate)).length ≤
        (spanPolynomial bound).eval inputLength ∧
      6 * workSteps remaining length width coordinate ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds remaining length width coordinate older bound inputLength hSpan

example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration (problem.certificateLimit + 1) 0
      (problem.dimensions.tapeWidth problem.tableauInputMode) coordinate older inside outside).state =
        machine.acceptState ↔ (BuilderInitialLengthSelection.selectedLength problem coordinate).isSome = true :=
  source_final_accept_iff problem coordinate older inside outside

example {language : Language} (problem : VerifierTableauProblem language) (hMode : problem.tableauInputMode = .paired)
    (coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration (problem.certificateLimit + 1) 0
      (problem.dimensions.tapeWidth problem.tableauInputMode) coordinate older inside outside).state =
        machine.rejectState ↔ problem.pairedCellsWidthDirect ≤ coordinate :=
  source_final_reject_iff problem hMode coordinate older inside outside

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderInitialRowLoopRegression
