import PNP.Concrete.CookLevinBuilderExclusionPairFirstVariable

open PNP.Concrete PNP.Concrete.CookLevin
open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderExclusionPairSelection (rowSelection reverseCoordinate reversePair selectedPair)
open BuilderExclusionPairFirstVariable

example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.eval expression environment = address environment :=
  BuilderExclusionPairFirstVariable.expression_eval environment

example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values expression environment = scratch environment :=
  BuilderExclusionPairFirstVariable.expression_values environment

example : BuilderRegisterExpression.nodeCount expression = 7 :=
  BuilderExclusionPairFirstVariable.expression_nodeCount

example (environment : Fin 9 → Nat) : (scratch environment).length = 7 :=
  BuilderExclusionPairFirstVariable.scratch_length environment

example (payload history : List Nat) (environment : Fin 9 → Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    address environment < (reader payload history environment).length :=
  BuilderExclusionPairFirstVariable.reader_address_lt payload history environment hHistory hField

example (payload history : List Nat) (environment : Fin 9 → Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    (reader payload history environment)[address environment]'
      (reader_address_lt payload history environment hHistory hField) = payload[firstIndex environment] :=
  BuilderExclusionPairFirstVariable.reader_address_value payload history environment hHistory hField

example (payload older history : List Nat) (environment : Fin 9 → Nat) :
    older ++ (reader payload history environment).reverse ++ [address environment] =
      initialValues payload older history environment ++ scratch environment :=
  BuilderExclusionPairFirstVariable.reader_layout payload older history environment

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (inside outside : List WorkSymbol) (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    workRunExact? machine (workSteps payload history environment payload[firstIndex environment])
      (initialConfiguration payload older history environment inside outside) =
      some (finalConfiguration payload older history environment payload[firstIndex environment] inside outside) :=
  BuilderExclusionPairFirstVariable.workRunExact payload older history environment inside outside hHistory hField

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (inside outside : List WorkSymbol) (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    run (compileWorkMachine machine) (6 * workSteps payload history environment payload[firstIndex environment])
      (encodeWorkConfiguration (initialConfiguration payload older history environment inside outside)) =
      encodeWorkConfiguration
        (finalConfiguration payload older history environment payload[firstIndex environment] inside outside) :=
  BuilderExclusionPairFirstVariable.run_compile_exact payload older history environment inside outside hHistory hField

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderExclusionPairFirstVariable.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine :=
  BuilderExclusionPairFirstVariable.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  BuilderExclusionPairFirstVariable.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState :=
  BuilderExclusionPairFirstVariable.acceptState_ne_rejectState

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = 18 + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length)
    (hSpan : (registerWord (initialValues payload older history environment)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment payload[firstIndex environment])).length +
        (outside.drop (allocation environment payload[firstIndex environment])).length ≤
          (spanPolynomial bound).eval input ∧
      6 * workSteps payload history environment payload[firstIndex environment] ≤ (rawTimePolynomial bound).eval input :=
  BuilderExclusionPairFirstVariable.source_polynomial_bounds payload older history environment outside bound input hHistory hField hSpan

example {width : Nat} (variables : List (Fin width)) :
    payloadValues variables = (BuilderLocalConstraintPayload.variableValues variables).reverse ++ [variables.length, 4] :=
  BuilderExclusionPairFirstVariable.payload_values variables

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat) (older : List Nat)
    (hValid : coordinate < LocalConstraint.pairCount variables.length) :
    ∃ (first second : Fin variables.length) (environment : Fin 9 → Nat) (history : List Nat),
      selectedPair variables.length coordinate = some (first.val, second.val) ∧
      firstIndex environment = first.val ∧
      secondIndex environment = second.val ∧
      rowOffset environment < rowWidth environment ∧
      history.length = 18 + 9 * rowWidth environment ∧
      lookupValues variables coordinate older =
        initialValues (BuilderLocalConstraintPayload.variableValues variables) older history environment :=
  BuilderExclusionPairFirstVariable.source_layout variables coordinate older hValid

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat) (older : List Nat)
    (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hValid : coordinate < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (lookupValues variables coordinate older)).length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (written : List Nat) (steps : Nat),
      selectedPair variables.length coordinate = some (first.val, second.val) ∧
      written.length = 7 ∧
      workRunExact? machine steps
        (workStartConfiguration machine
          (BuilderExclusionPairLookup.finalConfiguration variables.length coordinate
            (older ++ payloadValues variables) inside).tape) =
        some {
          state := machine.acceptState
          tape := endTape (lookupValues variables coordinate older ++ written ++ [variables[first.val].val]) inside [] } ∧
      (registerWord (lookupValues variables coordinate older ++ written ++ [variables[first.val].val])).length ≤
        (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input :=
  BuilderExclusionPairFirstVariable.source_read variables coordinate older inside bound input hValid hSpan

example {width : Nat} (variables : List (Fin width)) (coordinate : Nat)
    (older : List Nat) (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hValid : coordinate < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (older ++ payloadValues variables ++ [variables.length, coordinate])).length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (written : List Nat) (steps : Nat),
      selectedPair variables.length coordinate = some (first.val, second.val) ∧
      written.length = 7 ∧
      run (compileWorkMachine lookupMachine) (6 * steps)
        (encodeWorkConfiguration (workStartConfiguration lookupMachine
          (endTape (older ++ payloadValues variables ++ [variables.length, coordinate]) inside []))) =
        encodeWorkConfiguration {
          state := lookupMachine.acceptState
          tape := endTape (lookupValues variables coordinate older ++ written ++ [variables[first.val].val]) inside [] } ∧
      (registerWord (lookupValues variables coordinate older ++ written ++ [variables[first.val].val])).length ≤
        (completeSpanPolynomial bound).eval input ∧
      6 * steps ≤ (completeRawTimePolynomial bound).eval input :=
  BuilderExclusionPairFirstVariable.uniform_source_lookup variables coordinate older inside bound input hValid hSpan

example : BuilderRegisterExpression.nodeCount expression = 7 := rfl
example : address (BuilderInitialRowLoop.attemptEnvironment 0 1 0 4) = 46 := by decide
example : address (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0) = 69 := by decide
example : firstIndex (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0) = 0 := rfl
example : rowWidth (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0) = 4 := by decide
example : (scratch (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0)).length = 7 := rfl
example : BuilderExclusionPairSelection.selectedPair 4 0 = some (0, 1) := by decide
example : BuilderExclusionPairSelection.selectedPair 4 5 = some (2, 3) := by decide
example : BuilderExclusionPairSelection.selectedPair 4 6 = none := by decide
example : BuilderExclusionPairSelection.selectedPair 0 0 = none := rfl
example : BuilderExclusionPairSelection.selectedPair 1 0 = none := rfl
example : payloadValues ([⟨5, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩] : List (Fin 6)) =
    [5, 1, 5, 3, 4] := rfl
example (width coordinate : Nat) (variables : List (Fin width)) :
    BuilderExclusionPairSelection.selectedPair variables.length coordinate = none ↔
      LocalConstraint.pairCount variables.length ≤ coordinate :=
  BuilderExclusionPairSelection.selectedPair_none_iff variables.length coordinate
example : secondIndex (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0) = 2 := by decide
example : rowOffset (BuilderInitialRowLoop.attemptEnvironment 3 4 2 0) = 2 := by decide
