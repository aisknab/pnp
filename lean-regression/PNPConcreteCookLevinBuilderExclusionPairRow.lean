import PNP.Concrete.CookLevinBuilderExclusionPairRow

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderUnaryPolynomial BuilderExclusionPairSelection
open BuilderInitialRowLoop (attemptValues attemptEnvironment finishValues)
open BuilderDividerOperands (endTape)
open BuilderExclusionPairRow

example (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps count coordinate)
      (initialConfiguration count coordinate older inside outside) =
      some (finalConfiguration count coordinate older inside outside) :=
  BuilderExclusionPairRow.workRunExact count coordinate older inside outside

example (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count coordinate)
      (encodeWorkConfiguration (initialConfiguration count coordinate older inside outside)) =
      encodeWorkConfiguration (finalConfiguration count coordinate older inside outside) :=
  BuilderExclusionPairRow.run_compile_exact count coordinate older inside outside

example (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside outside).state = machine.rejectState ↔
      LocalConstraint.pairCount count ≤ coordinate :=
  BuilderExclusionPairRow.final_reject_iff count coordinate older inside outside

example (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside outside).state = machine.acceptState ↔
      coordinate < LocalConstraint.pairCount count :=
  BuilderExclusionPairRow.final_accept_iff count coordinate older inside outside

example (count coordinate : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration count coordinate older inside outside).tape =
      endTape (resultValues count coordinate older) inside
        (BuilderInitialRowLoop.finishOutside (count - 1) 0 1
          (reverseCoordinate count coordinate) outside) :=
  BuilderExclusionPairRow.final_tape count coordinate older inside outside

example (remaining length width coordinate : Nat)
    (position : Fin remaining) (offset : Nat)
    (hFound : BuilderInitialLengthSelection.locate remaining width coordinate = some (position, offset)) :
    ∃ history : List Nat, history.length = 9 * position.val ∧
      finishValues remaining length width coordinate =
        history ++ attemptValues (length + position.val) (width + position.val)
          offset (remaining - (position.val + 1)) :=
  BuilderExclusionPairRow.found_attempt remaining length width coordinate position offset hFound

example (history : List Nat) (environment : Fin 9 → Nat) :
    decodeValues (history ++ List.ofFn environment) =
      some (environment ⟨3, by decide⟩,
        environment ⟨3, by decide⟩ + environment ⟨7, by decide⟩ - environment ⟨8, by decide⟩) :=
  BuilderExclusionPairRow.decodeValues_suffix history environment

example (count coordinate : Nat) (older : List Nat)
    (position : Fin (count - 1)) (offset : Nat)
    (hFound : rowSelection count coordinate = some (position, offset)) :
    decodeValues (resultValues count coordinate older) = some (reversePair count (position, offset)) :=
  BuilderExclusionPairRow.found_pair_values count coordinate older position offset hFound

example (count coordinate : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    observedPair count coordinate older inside outside = selectedPair count coordinate :=
  BuilderExclusionPairRow.observedPair_eq_selectedPair count coordinate older inside outside

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps variables.length coordinate)
      (initialConfiguration variables.length coordinate older inside outside) =
      some (finalConfiguration variables.length coordinate older inside outside) ∧
    observePair variables (observedPair variables.length coordinate older inside outside) =
      (atMostOneBoundedClauses variables)[coordinate]? :=
  BuilderExclusionPairRow.workRun_observes_canonical variables coordinate older inside outside

example (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [count, coordinate])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ BuilderInitialRowLoop.frame 0 1
      (reverseCoordinate count coordinate) (count - 1))).length ≤
        (preparedSpanPolynomial bound).eval inputLength :=
  BuilderExclusionPairRow.prepared_span_bound count coordinate older bound inputLength hSpan

example (count coordinate : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [count, coordinate])).length ≤ bound.eval inputLength) :
    (registerWord (resultValues count coordinate older)).length ≤ (spanPolynomial bound).eval inputLength ∧
      6 * workSteps count coordinate ≤ (rawTimePolynomial bound).eval inputLength :=
  BuilderExclusionPairRow.row_polynomial_bounds count coordinate older bound inputLength hSpan

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [variables.length, coordinate])).length ≤ bound.eval inputLength) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval inputLength ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (initialConfiguration variables.length coordinate older inside outside)) =
        encodeWorkConfiguration (finalConfiguration variables.length coordinate older inside outside) ∧
      observePair variables (observedPair variables.length coordinate older inside outside) =
        (atMostOneBoundedClauses variables)[coordinate]? :=
  BuilderExclusionPairRow.uniform_polynomial_row_phase variables coordinate older inside outside bound inputLength hSpan

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderExclusionPairRow.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  BuilderExclusionPairRow.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderExclusionPairRow.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  BuilderExclusionPairRow.acceptState_ne_rejectState

example : decodeValues [20, 0, 0, 0, 2, 0, 0, 0, 1, 0] = some (2, 3) := rfl
example : decodeValues [90, 80, 2, 3, 2, 0, 0, 0, 0, 3, 2] = some (0, 1) := rfl
example : decodeValues ([] : List Nat) = none := rfl
example : decodeValues [0, 1, 2, 3] = none := rfl
example : observedPair 0 0 [] [] [] = none := by decide
example : observedPair 1 10 [2, 3] [] [] = none := by decide
example : observedPair 4 0 [] [] [] = some (0, 1) := by decide
example : observedPair 4 2 [] [] [] = some (0, 3) := by decide
example : observedPair 4 3 [17, 8] [] [] = some (1, 2) := by decide
example : observedPair 4 5 [17, 8] [] [] = some (2, 3) := by decide
example : observedPair 4 6 [17, 8] [] [] = none := by decide
example : observedPair 4 100 [17, 8] [] [] = none := by decide
example : workSteps 0 0 = 4 := rfl
example : workSteps 1 100 = 4 := rfl
