import PNP.Concrete.CookLevinBuilderPayloadBodyTokenLookup

open PNP PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family Request family body requestValues)
open WorkMachineProgramGraph (endpointConfiguration)
open PipelineStateNamespace (renameConfiguration)
open BuilderPayloadBodyTokenLookup

example :
    ([trueState,falseState,paddingState,separatorState,finishState] : List Nat).Pairwise
      (fun left right => left ≠ right) := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.terminal_states_distinct

example (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderPayloadClauseTokenSelector.observe configuration := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.observe_rename configuration

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (values : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration constraint request values inside outside) =
      (encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]? := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.final_observation constraint request values inside outside

example (route : Family) :
    (machine route).rules.Pairwise WorkMachineChain.QueryDistinct := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.rules_pairwise_query_distinct route

example (route : Family) : WorkMachineChain.NoRuleAtAccept (machine route) := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtAccept route

example (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) (machine route).rejectState := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtReject route

example (route : Family) :
    (machine route).acceptState ≠ (machine route).rejectState := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.acceptState_ne_rejectState route

example (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) paddingState := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtPadding route

example (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) separatorState := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtSeparator route

example (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) finishState := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtFinish route

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (requestValues constraint request older)).length + outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol),
      workRunExact? (machine (family constraint)) steps
        (initialConfiguration constraint request older inside outside) =
        some (finalConfiguration constraint request values inside resultOutside) ∧
      observe (finalConfiguration constraint request values inside resultOutside) =
        (encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]? ∧
      (∃ scratch, values = requestValues constraint request older ++ scratch) ∧
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.workRun_polynomial_lookup constraint request older inside outside bound input hSpan

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (requestValues constraint request older)).length + outside.length ≤ bound.eval input) :
    ∃ (rawSteps : Nat) (values : List Nat) (resultOutside : List WorkSymbol),
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine (machine (family constraint))) rawSteps
        (encodeWorkConfiguration (initialConfiguration constraint request older inside outside)) =
        encodeWorkConfiguration (finalConfiguration constraint request values inside resultOutside) ∧
      observe (finalConfiguration constraint request values inside resultOutside) =
        (encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]? ∧
      (∃ scratch, values = requestValues constraint request older ++ scratch) ∧
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input := by
  exact PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.uniform_polynomial_lookup constraint request older inside outside bound input hSpan

-- Independent checks for all five stable observations and fixed composition.
example (tape : WorkTape) : observe {state := trueState, tape := tape} = some .t := rfl
example (tape : WorkTape) : observe {state := falseState, tape := tape} = some .f := rfl
example (tape : WorkTape) : observe {state := paddingState, tape := tape} = none := rfl
example (tape : WorkTape) : observe {state := separatorState, tape := tape} = some .sep := rfl
example (tape : WorkTape) : observe {state := finishState, tape := tape} = some .finish := rfl
example (route : Family) : machine route =
    WorkMachineChain.machine (BuilderPayloadBodyPreparation.machine route)
      (BuilderPayloadClauseTokenSelector.machine route) := rfl
example (bound : NatPolynomial) : spanPolynomial bound =
    BuilderPayloadClauseTokenSelector.spanPolynomial (BuilderPayloadBodyPreparation.spanPolynomial bound) := rfl
example (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input =
      (BuilderPayloadBodyPreparation.rawTimePolynomial bound).eval input + 6 +
        (BuilderPayloadClauseTokenSelector.rawTimePolynomial (BuilderPayloadBodyPreparation.spanPolynomial bound)).eval input := rfl
