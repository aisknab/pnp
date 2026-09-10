import PNP.Concrete.CookLevinBuilderRequestedPairVariables

namespace PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderExclusionPairSelection (rowSelection reverseCoordinate reversePair selectedPair)
open BuilderRegisterExpression (Expr)

example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.eval expression environment = address environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.expression_eval environment

example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values expression environment = scratch environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.expression_values environment

example : BuilderRegisterExpression.nodeCount expression = 7 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.expression_nodeCount

example (environment : Fin 9 → Nat) : (scratch environment).length = 7 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.scratch_length environment

example (payload history : List Nat) (environment : Fin 9 → Nat)
    (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    address environment < (reader payload history environment).length := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.reader_address_lt payload history environment hHistory hField

example (payload history : List Nat) (environment : Fin 9 → Nat)
    (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    (reader payload history environment)[address environment]'
      (reader_address_lt payload history environment hHistory hField) = payload[firstIndex environment] := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.reader_address_value payload history environment hHistory hField

example (payload older history : List Nat) (environment : Fin 9 → Nat) :
    older ++ (reader payload history environment).reverse ++ [address environment] =
      initialValues payload older history environment ++ scratch environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.reader_layout payload older history environment

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (inside outside : List WorkSymbol) (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    workRunExact? machine (workSteps payload history environment payload[firstIndex environment])
      (initialConfiguration payload older history environment inside outside) =
      some (finalConfiguration payload older history environment payload[firstIndex environment] inside outside) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.workRunExact payload older history environment inside outside hHistory hField

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (inside outside : List WorkSymbol) (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length) :
    run (compileWorkMachine machine) (6 * workSteps payload history environment payload[firstIndex environment])
      (encodeWorkConfiguration (initialConfiguration payload older history environment inside outside)) =
      encodeWorkConfiguration
        (finalConfiguration payload older history environment payload[firstIndex environment] inside outside) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.run_compile_exact payload older history environment inside outside hHistory hField

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.rules_pairwise_query_distinct

example : WorkMachineChain.NoRuleAtAccept machine := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.acceptState_ne_rejectState

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = (18 + requestLength) + 9 * rowWidth environment)
    (hField : firstIndex environment < payload.length)
    (hSpan : (registerWord (initialValues payload older history environment)).length + outside.length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment payload[firstIndex environment])).length +
        (outside.drop (allocation environment payload[firstIndex environment])).length ≤
          (spanPolynomial bound).eval input ∧
      6 * workSteps payload history environment payload[firstIndex environment] ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First.source_polynomial_bounds payload older history environment outside bound input hHistory hField hSpan

end PNP.Concrete.CookLevin.BuilderRequestedPairVariables.First

namespace PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open BuilderRequestedPairVariables.First (firstIndex secondIndex rowWidth rowOffset)
open BuilderRegisterExpression (Expr)
open WorkMachineProgramGraph (Node Graph Endpoint)
open WorkMachineProgramPath (AcceptPath)

example (environment : Fin 9 → Nat) (firstValue : Nat) :
    (firstHistory environment firstValue).length = 8 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.firstHistory_length environment firstValue

example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values upperExpression environment = upperScratch environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.upper_values environment

example : BuilderRegisterExpression.nodeCount upperExpression = 7 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.upper_nodeCount

example (environment : Fin 9 → Nat) : (upperScratch environment).length = 7 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.upperScratch_length environment

example (environment : Fin 9 → Nat) :
    BuilderRegisterExpression.values offsetExpression environment = [rowOffset environment] := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.offset_values environment

example (environment : Fin 9 → Nat) : (scratchPrefix environment).length = 10 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.scratchPrefix_length environment

example (environment : Fin 9 → Nat) : (scratch environment).length = 11 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.scratch_length environment

example (environment : Fin 9 → Nat) (hOffset : rowOffset environment < rowWidth environment) :
    rowOffset environment ≤ upper environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.upper_not_less environment hOffset

example (environment : Fin 9 → Nat) (hOffset : rowOffset environment < rowWidth environment) :
    BuilderRegisterCompareResidual.resultCoordinate (comparisonResult environment) = address environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.residual_eq_address environment hOffset

example (environment : Fin 9 → Nat) (hOffset : rowOffset environment < rowWidth environment) :
    BuilderRegisterCompareResidual.outputValues (comparisonResult environment) =
      comparisonPrefix environment ++ [address environment] := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.comparison_values environment hOffset

example (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) :
    initialValues payload older history environment firstValue =
      BuilderRequestedPairVariables.First.finalValues payload older history environment firstValue := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.after_first_values payload older history environment firstValue

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (inside : List WorkSymbol) :
    workRunExact? prepareMachine (prepareSteps environment firstValue)
      (workStartConfiguration prepareMachine (endTape (initialValues payload older history environment firstValue) inside [])) =
      some {
        state := prepareMachine.acceptState
        tape := endTape (preparedValues payload older history environment firstValue) inside [] } := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.prepare_workRunExact payload older history environment firstValue inside

example (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hField : secondIndex environment < payload.length) :
    address environment < (reader payload history environment firstValue).length := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.reader_address_lt payload history environment firstValue hHistory hField

example (payload history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hField : secondIndex environment < payload.length) :
    (reader payload history environment firstValue)[address environment]'
      (reader_address_lt payload history environment firstValue hHistory hField) = payload[secondIndex environment] := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.reader_address_value payload history environment firstValue hHistory hField

example (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat) :
    older ++ (reader payload history environment firstValue).reverse ++ [address environment] =
      initialValues payload older history environment firstValue ++ scratch environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.reader_layout payload older history environment firstValue

example : graph.nodes.length = 3 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.graph_nodes_length

example : graph.WellFormed := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.graph_wellFormed

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (inside : List WorkSymbol)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment) (hField : secondIndex environment < payload.length) :
    workRunExact? machine (workSteps payload history environment firstValue payload[secondIndex environment])
      (initialConfiguration payload older history environment firstValue inside) =
      some (finalConfiguration payload older history environment firstValue payload[secondIndex environment] inside) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.workRunExact payload older history environment firstValue inside hHistory hOffset hField

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (inside : List WorkSymbol)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment) (hField : secondIndex environment < payload.length) :
    run (compileWorkMachine machine) (6 * workSteps payload history environment firstValue payload[secondIndex environment])
      (encodeWorkConfiguration (initialConfiguration payload older history environment firstValue inside)) =
      encodeWorkConfiguration (finalConfiguration payload older history environment firstValue payload[secondIndex environment] inside) := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.run_compile_exact payload older history environment firstValue inside hHistory hOffset hField

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.acceptState_ne_rejectState

example (payload older history : List Nat) (environment : Fin 9 → Nat) (firstValue : Nat)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues payload older history environment firstValue)).length ≤ bound.eval input) :
    (registerWord (preparedValues payload older history environment firstValue)).length ≤
      (preparedSpanPolynomial bound).eval input ∧
    6 * prepareSteps environment firstValue ≤ (preparedRawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.prepare_polynomial_bounds payload older history environment firstValue bound input hSpan

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (firstValue : Nat) (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment) (hField : secondIndex environment < payload.length)
    (hSpan : (registerWord (initialValues payload older history environment firstValue)).length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment firstValue payload[secondIndex environment])).length ≤
      (spanPolynomial bound).eval input ∧
    6 * workSteps payload history environment firstValue payload[secondIndex environment] ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.source_polynomial_bounds payload older history environment firstValue bound input hHistory hOffset hField hSpan

example (payload older history : List Nat) (environment : Fin 9 → Nat) (inside : List WorkSymbol)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment)
    (hFirst : firstIndex environment < payload.length) (hSecond : secondIndex environment < payload.length) :
    workRunExact? pairMachine (pairSteps payload history environment payload[firstIndex environment] payload[secondIndex environment])
      (workStartConfiguration pairMachine
        (endTape (BuilderRequestedPairVariables.First.initialValues payload older history environment) inside [])) =
      some {
        state := pairMachine.acceptState
        tape := endTape (finalValues payload older history environment payload[firstIndex environment] payload[secondIndex environment]) inside [] } := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.pair_workRunExact payload older history environment inside hHistory hOffset hFirst hSecond

example (payload older history : List Nat) (environment : Fin 9 → Nat)
    (bound : NatPolynomial) (input : Nat)
    (hHistory : history.length = (18 + BuilderRequestedPairVariables.First.requestLength) + 9 * rowWidth environment)
    (hOffset : rowOffset environment < rowWidth environment)
    (hFirst : firstIndex environment < payload.length) (hSecond : secondIndex environment < payload.length)
    (hSpan : (registerWord (BuilderRequestedPairVariables.First.initialValues payload older history environment)).length ≤ bound.eval input) :
    (registerWord (finalValues payload older history environment payload[firstIndex environment] payload[secondIndex environment])).length ≤
      (pairSpanPolynomial bound).eval input ∧
    6 * pairSteps payload history environment payload[firstIndex environment] payload[secondIndex environment] ≤
      (pairRawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.pair_polynomial_bounds payload older history environment bound input hHistory hOffset hFirst hSecond hSpan

example : pairMachine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.pair_rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt pairMachine pairMachine.acceptState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.pair_noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt pairMachine pairMachine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.pair_noRuleAtReject

example : pairMachine.acceptState ≠ pairMachine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second.pair_acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderRequestedPairVariables.Second

namespace PNP.Concrete.CookLevin.BuilderRequestedPairVariables

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Request requestValues)
open BuilderLocalConstraintPayload (variableValues)
open BuilderExclusionPairSelection (rowSelection reverseCoordinate reversePair selectedPair)
open First (firstIndex secondIndex rowWidth rowOffset)
open WorkMachineProgramGraph (Node Graph)
open WorkMachineProgramPath (AcceptPath)

example (request : Request) :
    (request.gap ++ [request.clauseIndex, request.originalPosition]).length = First.requestLength := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.request_length request

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat) :
    BuilderRequestedPairLookup.initialValues variables request older =
      older ++ (variableValues variables).reverse ++ [variables.length, 4] ++ request.gap ++
        [request.clauseIndex, request.originalPosition] := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.input_layout variables request older

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside : List WorkSymbol) :
    (BuilderRequestedPairLookup.canonicalFinal variables request older inside).tape =
      endTape (lookupValues variables request older) inside [] := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.canonical_tape variables request older inside

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length) :
    ∃ (first second : Fin variables.length) (environment : Fin 9 → Nat) (history : List Nat),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstIndex environment = first.val ∧ secondIndex environment = second.val ∧
      rowOffset environment < rowWidth environment ∧
      history.length = (18 + First.requestLength) + 9 * rowWidth environment ∧
      lookupValues variables request older = First.initialValues (variableValues variables) older history environment := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.source_layout variables request older hValid

example {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (lookupValues variables request older)).length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (steps : Nat),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      workRunExact? Second.pairMachine steps
        (workStartConfiguration Second.pairMachine (endTape (lookupValues variables request older) inside [])) =
        some {
          state := Second.pairMachine.acceptState
          tape := endTape (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
            secondWritten ++ [variables[second.val].val]) inside []
        } ∧
      (registerWord (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
        secondWritten ++ [variables[second.val].val])).length ≤ (Second.pairSpanPolynomial bound).eval input ∧
      6 * steps ≤ (Second.pairRawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.canonical_source_read variables request older inside bound input hValid hSpan

example : graph.nodes.length = 2 := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.graph_nodes_length

example : graph.WellFormed := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.graph_wellFormed

example : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.rules_pairwise_query_distinct

example : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.noRuleAtAccept

example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.noRuleAtReject

example : machine.acceptState ≠ machine.rejectState := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.acceptState_ne_rejectState

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (steps : Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      workRunExact? machine steps
        (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) = some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.acceptState
        tape := endTape (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
          secondWritten ++ [variables[second.val].val]) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.workRun_source_lookup variables request older inside outside bound input hPositive hBlank hValid hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (rawSteps : Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration machine
          (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside))) =
        encodeWorkConfiguration final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.acceptState
        tape := endTape (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
          secondWritten ++ [variables[second.val].val]) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.uniform_source_lookup variables request older inside outside bound input hPositive hBlank hValid hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps
        (encodeWorkConfiguration (workStartConfiguration machine
          (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside))) =
        encodeWorkConfiguration final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.rejectState
        tape := endTape (lookupValues variables request older) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderRequestedPairVariables.uniform_invalid_source_lookup variables request older inside outside bound input hPositive hBlank hInvalid hSpan


example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hValid : request.clauseIndex - 1 < LocalConstraint.pairCount variables.length)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ (first second : Fin variables.length) (firstWritten secondWritten : List Nat) (steps : Nat) (final : WorkConfiguration),
      selectedPair variables.length (request.clauseIndex - 1) = some (first.val, second.val) ∧
      firstWritten.length = 7 ∧ secondWritten.length = 11 ∧
      workRunExact? machine steps
        (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) = some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.acceptState
        tape := endTape (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
          secondWritten ++ [variables[second.val].val]) inside []
      } ∧
      (registerWord (lookupValues variables request older ++ firstWritten ++ [variables[first.val].val] ++
        secondWritten ++ [variables[second.val].val])).length ≤
          (Second.pairSpanPolynomial (canonicalSpanPolynomial bound)).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact workRun_source_lookup_with_canonical_span variables request older inside outside bound input hPositive hBlank hValid hSpan

example {width : Nat} (variables : List (Fin width)) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex) (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hInvalid : LocalConstraint.pairCount variables.length ≤ request.clauseIndex - 1)
    (hSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length + outside.length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps
        (workStartConfiguration machine (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside outside)) =
        some final ∧
      WorkConfiguration.BlankEquivalent final {
        state := machine.rejectState
        tape := endTape (lookupValues variables request older) inside []
      } ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact workRun_invalid_source_lookup variables request older inside outside bound input hPositive hBlank hInvalid hSpan


end PNP.Concrete.CookLevin.BuilderRequestedPairVariables

open PNP PNP.Concrete PNP.Concrete.CookLevin
open BuilderRequestedPairVariables
open BuilderUnaryPolynomial (registerWord)
open BuilderPayloadSearchSource (Request)

-- Independent address, scratch, retained-prefix and fail-closed routing contracts.
example (environment : Fin 9 → Nat) :
    First.address environment = 9 * First.rowWidth environment + First.firstIndex environment + 44 := rfl
example (environment : Fin 9 → Nat) :
    Second.address environment = 9 * First.rowWidth environment + First.secondIndex environment + 56 := rfl
example (environment : Fin 9 → Nat) : (First.scratch environment).length = 7 := rfl
example (environment : Fin 9 → Nat) : (Second.scratch environment).length = 11 := by
  exact Second.scratch_length environment
example : lookupNode.onReject = .reject := rfl
example : pairNode.program = Second.pairMachine := rfl
example : lookupNode.program = BuilderRequestedPairLookup.machine := rfl
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      (BuilderRequestedPairLookup.rawTimePolynomial bound).eval input + 12 +
      (Second.pairRawTimePolynomial (canonicalSpanPolynomial bound)).eval input := rfl
example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input = bound.eval input + (rawTimePolynomial bound).eval input := rfl
