import PNP.Concrete.CookLevinBuilderExclusionPairSecondVariable

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open BuilderExclusionPairFirstVariable (firstIndex secondIndex rowWidth rowOffset)
open BuilderExclusionPairSecondVariable

example (environment : Fin 9 → Nat) (firstValue : Nat) :
    (firstHistory environment firstValue).length = 8 :=
  BuilderExclusionPairSecondVariable.firstHistory_length environment firstValue

example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values upperExpression environment = upperScratch environment :=
  BuilderExclusionPairSecondVariable.upper_values environment

example : BuilderRegisterExpression.nodeCount upperExpression = 7 :=
  BuilderExclusionPairSecondVariable.upper_nodeCount

example (environment : Fin 9 → Nat) : (upperScratch environment).length = 7 :=
  BuilderExclusionPairSecondVariable.upperScratch_length environment

example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values offsetExpression environment = [rowOffset environment] :=
  BuilderExclusionPairSecondVariable.offset_values environment

example (environment : Fin 9 → Nat) : (scratchPrefix environment).length = 10 :=
  BuilderExclusionPairSecondVariable.scratchPrefix_length environment

example (environment : Fin 9 → Nat) : (scratch environment).length = 11 :=
  BuilderExclusionPairSecondVariable.scratch_length environment

example (environment : Fin 9 → Nat) (hOffset : rowOffset environment < rowWidth environment) :
    rowOffset environment ≤ upper environment :=
  BuilderExclusionPairSecondVariable.upper_not_less environment hOffset

example (environment : Fin 9 → Nat) (hOffset : rowOffset environment < rowWidth environment) :
    BuilderRegisterCompareResidual.resultCoordinate (comparisonResult environment) = address environment :=
  BuilderExclusionPairSecondVariable.residual_eq_address environment hOffset

example (environment : Fin 9 → Nat) (hOffset : rowOffset environment < rowWidth environment) :
    BuilderRegisterCompareResidual.outputValues (comparisonResult environment) =
      comparisonPrefix environment ++ [address environment] :=
  BuilderExclusionPairSecondVariable.comparison_values environment hOffset

example (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) :
    initialValues payload older history environment firstValue =
      BuilderExclusionPairFirstVariable.finalValues payload older history environment firstValue :=
  BuilderExclusionPairSecondVariable.after_first_values payload older history environment firstValue

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (inside : List WorkSymbol) :
    workRunExact? prepareMachine (prepareSteps environment firstValue)
      (workStartConfiguration prepareMachine (endTape (initialValues payload older history environment firstValue) inside [])) =
      some {
        state := prepareMachine.acceptState
        tape := endTape (preparedValues payload older history environment firstValue) inside [] } :=
  BuilderExclusionPairSecondVariable.prepare_workRunExact payload older history environment firstValue inside

example (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : secondIndex environment < payload.length) :
    address environment < (reader payload history environment firstValue).length :=
  BuilderExclusionPairSecondVariable.reader_address_lt payload history environment firstValue hHistory hField

example (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : secondIndex environment < payload.length) :
    (reader payload history environment firstValue)[address environment]'
      (reader_address_lt payload history environment firstValue hHistory hField) = payload[secondIndex environment] :=
  BuilderExclusionPairSecondVariable.reader_address_value payload history environment firstValue hHistory hField

example (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) :
    older ++ (reader payload history environment firstValue).reverse ++ [address environment] =
      initialValues payload older history environment firstValue ++ scratch environment :=
  BuilderExclusionPairSecondVariable.reader_layout payload older history environment firstValue

example : graph.nodes.length = 3 :=
  BuilderExclusionPairSecondVariable.graph_nodes_length

example : graph.WellFormed :=
  BuilderExclusionPairSecondVariable.graph_wellFormed

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (inside : List WorkSymbol)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment) (hField : secondIndex environment < payload.length) :
    workRunExact? machine (workSteps payload history environment firstValue payload[secondIndex environment])
      (initialConfiguration payload older history environment firstValue inside) =
      some (finalConfiguration payload older history environment firstValue payload[secondIndex environment] inside) :=
  BuilderExclusionPairSecondVariable.workRunExact payload older history environment firstValue inside hHistory hOffset hField

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (inside : List WorkSymbol)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment) (hField : secondIndex environment < payload.length) :
    run (compileWorkMachine machine) (6 * workSteps payload history environment firstValue payload[secondIndex environment])
      (encodeWorkConfiguration (initialConfiguration payload older history environment firstValue inside)) =
      encodeWorkConfiguration (finalConfiguration payload older history environment firstValue payload[secondIndex environment] inside) :=
  BuilderExclusionPairSecondVariable.run_compile_exact payload older history environment firstValue inside hHistory hOffset hField

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderExclusionPairSecondVariable.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  BuilderExclusionPairSecondVariable.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderExclusionPairSecondVariable.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  BuilderExclusionPairSecondVariable.acceptState_ne_rejectState

example (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues payload older history environment firstValue)).length ≤ bound.eval input) :
    (registerWord (preparedValues payload older history environment firstValue)).length ≤
      (preparedSpanPolynomial bound).eval input ∧
    6 * prepareSteps environment firstValue ≤ (preparedRawTimePolynomial bound).eval input :=
  BuilderExclusionPairSecondVariable.prepare_polynomial_bounds payload older history environment firstValue bound input hSpan

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment) (hField : secondIndex environment < payload.length)
    (hSpan : (registerWord (initialValues payload older history environment firstValue)).length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment firstValue payload[secondIndex environment])).length ≤
      (spanPolynomial bound).eval input ∧
    6 * workSteps payload history environment firstValue payload[secondIndex environment] ≤ (rawTimePolynomial bound).eval input :=
  BuilderExclusionPairSecondVariable.source_polynomial_bounds payload older history environment firstValue bound input hHistory hOffset hField hSpan

example (payload older history : List Nat) (environment : Fin 9 → Nat) (inside : List WorkSymbol)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment)
    (hFirst : firstIndex environment < payload.length) (hSecond : secondIndex environment < payload.length) :
    workRunExact? pairMachine (pairSteps payload history environment payload[firstIndex environment] payload[secondIndex environment])
      (workStartConfiguration pairMachine
        (endTape (BuilderExclusionPairFirstVariable.initialValues payload older history environment) inside [])) =
      some {
        state := pairMachine.acceptState
        tape := endTape (finalValues payload older history environment payload[firstIndex environment] payload[secondIndex environment]) inside [] } :=
  BuilderExclusionPairSecondVariable.pair_workRunExact payload older history environment inside hHistory hOffset hFirst hSecond

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment)
    (hFirst : firstIndex environment < payload.length) (hSecond : secondIndex environment < payload.length)
    (hSpan : (registerWord (BuilderExclusionPairFirstVariable.initialValues payload older history environment)).length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment payload[firstIndex environment] payload[secondIndex environment])).length ≤
      (pairSpanPolynomial bound).eval input ∧
    6 * pairSteps payload history environment payload[firstIndex environment] payload[secondIndex environment] ≤
      (pairRawTimePolynomial bound).eval input :=
  BuilderExclusionPairSecondVariable.pair_polynomial_bounds payload older history environment bound input hHistory hOffset hFirst hSecond hSpan

example : lookupGraph.nodes.length = 2 :=
  BuilderExclusionPairSecondVariable.lookupGraph_nodes_length

example : lookupGraph.WellFormed :=
  BuilderExclusionPairSecondVariable.lookupGraph_wellFormed

example : lookupMachine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderExclusionPairSecondVariable.lookup_rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt lookupMachine lookupMachine.acceptState :=
  BuilderExclusionPairSecondVariable.lookup_noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt lookupMachine lookupMachine.rejectState :=
  BuilderExclusionPairSecondVariable.lookup_noRuleAtReject

example : lookupMachine.acceptState ≠ lookupMachine.rejectState :=
  BuilderExclusionPairSecondVariable.lookup_acceptState_ne_rejectState

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hValid : coordinate < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++
      [variables.length, coordinate])).length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (steps : Nat),
      BuilderExclusionPairSelection.selectedPair variables.length coordinate = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      run (compileWorkMachine lookupMachine) (6 * steps)
        (encodeWorkConfiguration (workStartConfiguration lookupMachine
          (endTape (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++
            [variables.length, coordinate]) inside []))) =
        encodeWorkConfiguration {
          state := lookupMachine.acceptState
          tape := endTape (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older ++
            firstWritten ++ [variables[first.val].val] ++ secondWritten ++ [variables[second.val].val]) inside [] } ∧
      (registerWord (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older ++
        firstWritten ++ [variables[first.val].val] ++ secondWritten ++ [variables[second.val].val])).length ≤
          (completeSpanPolynomial bound).eval input ∧
      6 * steps ≤ (completeRawTimePolynomial bound).eval input :=
  BuilderExclusionPairSecondVariable.uniform_source_lookup variables coordinate older inside bound input hValid hSpan

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ coordinate) :
    run (compileWorkMachine lookupMachine) (6 * (BuilderExclusionPairLookup.workSteps variables.length coordinate + 1))
      (encodeWorkConfiguration (workStartConfiguration lookupMachine
        (endTape (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++ [variables.length, coordinate]) inside []))) =
      encodeWorkConfiguration {
        state := lookupMachine.rejectState
        tape := endTape (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older) inside [] } :=
  BuilderExclusionPairSecondVariable.invalid_source_lookup variables coordinate older inside hInvalid

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ coordinate)
    (hSpan : (registerWord (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++
      [variables.length, coordinate])).length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (NatPolynomial.add (BuilderExclusionPairLookup.rawTimePolynomial bound) (.constant 6)).eval input ∧
      run (compileWorkMachine lookupMachine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration lookupMachine
          (endTape (older ++ BuilderExclusionPairFirstVariable.payloadValues variables ++ [variables.length, coordinate]) inside []))) =
        encodeWorkConfiguration {
          state := lookupMachine.rejectState
          tape := endTape (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older) inside [] } ∧
      (registerWord (BuilderExclusionPairFirstVariable.lookupValues variables coordinate older)).length ≤
        (BuilderExclusionPairLookup.spanPolynomial bound).eval input :=
  BuilderExclusionPairSecondVariable.uniform_invalid_source_lookup variables coordinate older inside bound input hInvalid hSpan

example : BuilderRegisterExpression.nodeCount upperExpression = 7 := rfl
example : BuilderRegisterExpression.nodeCount offsetExpression = 1 := rfl
example : upper (BuilderInitialRowLoop.attemptEnvironment 0 1 0 4) = 59 := by decide
example : address (BuilderInitialRowLoop.attemptEnvironment 0 1 0 4) = 59 := by decide
example : upper (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0) = 85 := by decide
example : address (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0) = 83 := by decide
example : address (BuilderInitialRowLoop.attemptEnvironment 3 4 0 0) = 85 := by decide
example : address (BuilderInitialRowLoop.attemptEnvironment 3 4 3 0) = 82 := by decide
example : (firstHistory (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0) 7).length = 8 := by decide
example : (scratchPrefix (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0)).length = 10 := by decide
example : (scratch (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0)).length = 11 := by decide
example : BuilderExclusionPairSelection.selectedPair 3 0 = some (0, 1) := by decide
example : BuilderExclusionPairSelection.selectedPair 3 2 = some (1, 2) := by decide
example : BuilderExclusionPairSelection.selectedPair 3 3 = none := by decide
example : BuilderExclusionPairSelection.selectedPair 0 0 = none := rfl
example : BuilderExclusionPairSelection.selectedPair 1 0 = none := rfl
example : BuilderLocalConstraintPayload.variableValues ([⟨7, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩] : List (Fin 8)) =
    [7, 2, 6] := rfl
example : BuilderExclusionPairFirstVariable.payloadValues ([⟨7, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩] : List (Fin 8)) =
    [6, 2, 7, 3, 4] := rfl
example : BuilderExclusionPairFirstVariable.payloadValues ([⟨5, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩] : List (Fin 6)) =
    [5, 1, 5, 3, 4] := rfl
example : BuilderExclusionPairSelection.selectedPair 3 1 = some (0, 2) := by decide
