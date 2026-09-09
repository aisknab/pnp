/-
Copyright (c) 2026 PNP Labs.

Complete actual-source body-clause execution and encoded-input polynomial
contracts. These public contracts do not accept an externally supplied run,
selected literal, width verdict or correctness certificate.
-/
import PNP.Concrete.CookLevinBuilderPayloadClauseTokenSelector

namespace PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelectorRegression

open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family Request family body requestValues)
open WorkMachineProgramGraph (endpointConfiguration)
open BuilderPayloadClauseTokenSelector

example (route : Family) : (graph route).nodes.length = 6 :=
  BuilderPayloadClauseTokenSelector.graph_nodes_length route

example :
    ([trueState,1,2,separatorState,finishState] : List Nat).Pairwise (fun left right => left ≠ right) :=
  BuilderPayloadClauseTokenSelector.terminal_states_distinct

example (route : Family) : (graph route).WellFormed :=
  BuilderPayloadClauseTokenSelector.graph_wellFormed route

example (route : Family) : WorkMachineChain.NoRuleAtAccept (machine route) :=
  BuilderPayloadClauseTokenSelector.noRuleAtAccept route

example (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) (machine route).rejectState :=
  BuilderPayloadClauseTokenSelector.noRuleAtReject route

example (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) 2 :=
  BuilderPayloadClauseTokenSelector.noRuleAtPadding route

example (route : Family) : (machine route).rules.Pairwise WorkMachineChain.QueryDistinct :=
  BuilderPayloadClauseTokenSelector.rules_pairwise_query_distinct route

example (route : Family) : (machine route).acceptState ≠ (machine route).rejectState :=
  BuilderPayloadClauseTokenSelector.acceptState_ne_rejectState route

example (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) separatorState :=
  BuilderPayloadClauseTokenSelector.noRuleAtSeparator route

example (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) finishState :=
  BuilderPayloadClauseTokenSelector.noRuleAtFinish route

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) :
    initialValues constraint request position older = entryOlder constraint request older ++ [position] :=
  BuilderPayloadClauseTokenSelector.initial_values_suffix constraint request position older

example {width : Nat} (constraint : LocalConstraint width)
    (position : Nat) (tape : WorkTape) :
    observe (endpointConfiguration (endpoint constraint position) tape) =
      (encodeClauseTokens (BoundedClause.emit (body constraint)))[position]? :=
  BuilderPayloadClauseTokenSelector.endpoint_observes_encoding constraint position tape

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (hPositive : 0 < position) :
    (registerWord (initialValues constraint request (position - 1) older)).length +
        (bodyOutside outside).length =
      (registerWord (initialValues constraint request position older)).length + outside.length :=
  BuilderPayloadClauseTokenSelector.body_input_span constraint request position older outside hPositive

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request position older)).length + outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol),
      workRunExact? (machine (family constraint)) steps
        (workStartConfiguration (machine (family constraint))
          (endTape (initialValues constraint request position older) inside outside)) =
        some (endpointConfiguration (endpoint constraint position) (endTape values inside resultOutside)) ∧
      observe (endpointConfiguration (endpoint constraint position) (endTape values inside resultOutside)) =
        (encodeClauseTokens (BoundedClause.emit (body constraint)))[position]? ∧
      (∃ scratch, values = requestValues constraint request older ++ scratch) ∧
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input :=
  BuilderPayloadClauseTokenSelector.workRun_polynomial_lookup constraint request position older inside outside bound input hSpan

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request position older)).length + outside.length ≤ bound.eval input) :
    ∃ (rawSteps : Nat) (values : List Nat) (resultOutside : List WorkSymbol),
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine (machine (family constraint))) rawSteps
        (encodeWorkConfiguration (workStartConfiguration (machine (family constraint))
          (endTape (initialValues constraint request position older) inside outside))) =
        encodeWorkConfiguration (endpointConfiguration (endpoint constraint position) (endTape values inside resultOutside)) ∧
      observe (endpointConfiguration (endpoint constraint position) (endTape values inside resultOutside)) =
        (encodeClauseTokens (BoundedClause.emit (body constraint)))[position]? ∧
      (∃ scratch, values = requestValues constraint request older ++ scratch) ∧
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input :=
  BuilderPayloadClauseTokenSelector.uniform_polynomial_lookup constraint request position older inside outside bound input hSpan

-- Empty positive bodies still have a complete clause, including its finish.
example (tape : WorkTape) :
    observe (endpointConfiguration (endpoint (.exactlyOne ([] : List (Fin 0))) 0) tape) = some .sep := rfl
example (tape : WorkTape) :
    observe (endpointConfiguration (endpoint (.exactlyOne ([] : List (Fin 0))) 1) tape) = some .finish := rfl
example (tape : WorkTape) :
    observe (endpointConfiguration (endpoint (.exactlyOne ([] : List (Fin 0))) 2) tape) = none := rfl

-- The wrapper adds constant time overhead, not another iteration of the search polynomial.
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      72 + (BuilderPayloadSourceSearchEnvelope.rawTimePolynomial bound).eval input := rfl
example (bound : NatPolynomial) (input : Nat) :
    (spanPolynomial bound).eval input =
      bound.eval input + (BuilderPayloadSourceSearchEnvelope.spanPolynomial bound).eval input := rfl

end PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelectorRegression
