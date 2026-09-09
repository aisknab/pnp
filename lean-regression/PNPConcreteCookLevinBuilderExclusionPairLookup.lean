import PNP.Concrete.CookLevinBuilderExclusionPairLookup

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderExclusionPairSelection (reverseCoordinate selectedPair observePair)
open LocalConstraint (pairCount)
open BuilderExclusionPairLookup

example (count coordinate : Nat) :
    List.ofFn (outputEnvironment count coordinate) = BuilderExclusionPairPreparation.history count coordinate :=
  BuilderExclusionPairLookup.outputEnvironment_ofFn count coordinate

example (count coordinate : Nat) (hValid : coordinate < pairCount count) :
    BuilderRegisterPack.values rowFields (outputEnvironment count coordinate) =
      [0, 1, reverseCoordinate count coordinate, count] :=
  BuilderExclusionPairLookup.row_values count coordinate hValid

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol)
    (hValid : coordinate < pairCount count) :
    workRunExact? packMachine (packSteps count coordinate)
      (workStartConfiguration packMachine
        (endTape (older ++ BuilderExclusionPairPreparation.history count coordinate) inside [])) =
      some {
        state := packMachine.acceptState
        tape := endTape (older ++ BuilderExclusionPairPreparation.history count coordinate ++
          BuilderInitialRowLoop.frame 0 1 (reverseCoordinate count coordinate) (count - 1)) inside [WorkSymbol.blank] } :=
  BuilderExclusionPairLookup.pack_workRunExact count coordinate older inside hValid

example (remaining length coordinate : Nat) :
    BuilderInitialRowLoop.finishOutside (remaining + 1) length 1 coordinate [WorkSymbol.blank] = [] :=
  positive_row_frontier remaining length coordinate

example : graph.nodes.length = 3 :=
  BuilderExclusionPairLookup.graph_nodes_length

example : graph.WellFormed :=
  BuilderExclusionPairLookup.graph_wellFormed

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps count coordinate) (initialConfiguration count coordinate older inside) =
      some (finalConfiguration count coordinate older inside) :=
  BuilderExclusionPairLookup.workRunExact count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count coordinate)
      (encodeWorkConfiguration (initialConfiguration count coordinate older inside)) =
      encodeWorkConfiguration (finalConfiguration count coordinate older inside) :=
  BuilderExclusionPairLookup.run_compile_exact count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).state = machine.acceptState ↔ coordinate < pairCount count :=
  BuilderExclusionPairLookup.final_accept_iff count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).state = machine.rejectState ↔ pairCount count ≤ coordinate :=
  BuilderExclusionPairLookup.final_reject_iff count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside).tape =
      endTape (resultValues count coordinate older) inside [] :=
  BuilderExclusionPairLookup.final_tape count coordinate older inside

example (count coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    observedPair count coordinate older inside = selectedPair count coordinate :=
  BuilderExclusionPairLookup.observedPair_eq_selectedPair count coordinate older inside

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps variables.length coordinate)
      (initialConfiguration variables.length coordinate older inside) =
      some (finalConfiguration variables.length coordinate older inside) ∧
      observePair variables (observedPair variables.length coordinate older inside) =
        (atMostOneBoundedClauses variables)[coordinate]? :=
  BuilderExclusionPairLookup.workRun_observes_canonical variables coordinate older inside

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderExclusionPairLookup.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  BuilderExclusionPairLookup.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderExclusionPairLookup.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  BuilderExclusionPairLookup.acceptState_ne_rejectState

example (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ BuilderExclusionPairPreparation.history count coordinate)).length ≤
      bound.eval inputLength) (hValid : coordinate < pairCount count) :
    (registerWord (older ++ BuilderExclusionPairPreparation.history count coordinate ++
      BuilderInitialRowLoop.frame 0 1 (reverseCoordinate count coordinate) (count - 1))).length ≤
        (BuilderRegisterPack.spanPolynomial rowFields bound).eval inputLength ∧
      6 * packSteps count coordinate ≤
        (BuilderRegisterPack.rawTimePolynomial rowFields bound).eval inputLength + 18 :=
  BuilderExclusionPairLookup.pack_polynomial_bounds count coordinate older bound inputLength hSpan hValid

example (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [count, coordinate])).length ≤ bound.eval inputLength) :
    (registerWord (resultValues count coordinate older)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count coordinate ≤ (rawTimePolynomial bound).eval inputLength :=
  BuilderExclusionPairLookup.source_polynomial_bounds count coordinate older bound inputLength hSpan

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [variables.length, coordinate])).length ≤ bound.eval inputLength) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval inputLength ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration variables.length coordinate older inside)) =
        encodeWorkConfiguration (finalConfiguration variables.length coordinate older inside) ∧
      observePair variables (observedPair variables.length coordinate older inside) =
        (atMostOneBoundedClauses variables)[coordinate]? :=
  BuilderExclusionPairLookup.uniform_polynomial_lookup variables coordinate older inside bound inputLength hSpan

example : observedPair 0 0 [] [] = none := by decide
example : observedPair 0 8 [9] [] = none := by decide
example : observedPair 1 0 [7, 8] [] = none := by decide
example : observedPair 1 10 [] [] = none := by decide
example : observedPair 2 0 [] [] = some (0, 1) := by decide
example : observedPair 2 1 [7, 8] [] = none := by decide
example : observedPair 4 0 [] [] = some (0, 1) := by decide
example : observedPair 4 1 [] [] = some (0, 2) := by decide
example : observedPair 4 2 [] [] = some (0, 3) := by decide
example : observedPair 4 3 [7, 8] [] = some (1, 2) := by decide
example : observedPair 4 4 [7, 8] [] = some (1, 3) := by decide
example : observedPair 4 5 [7, 8] [] = some (2, 3) := by decide
example : observedPair 4 6 [7, 8] [] = none := by decide
example : observedPair 4 100 [7, 8] [] = none := by decide
example : BuilderRegisterPack.values rowFields (outputEnvironment 4 0) = [0, 1, 5, 4] := by decide
example : BuilderRegisterPack.values rowFields (outputEnvironment 4 5) = [0, 1, 0, 4] := by decide
example : observePair ([2, 2, 1] : List (Fin 5)) (observedPair 3 1 [8, 9] []) =
    some (excludeBoundedPairClause (2 : Fin 5) 1) := by decide
