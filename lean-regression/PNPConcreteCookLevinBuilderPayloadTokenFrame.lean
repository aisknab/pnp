/- Regression contracts for blank-preserving actual-source body-token lookup. -/
import PNP.Concrete.CookLevinBuilderCursorTokenLookup

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlankFrameRegression

open PipelineTape
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource
open BuilderPayloadLiteralTokenSelector (Source Context)
open BuilderPayloadSourceSearch (CostTrace costVisit)
open BuilderPayloadSourceSearchControl (graph graph_wellFormed)
open BuilderPayloadSourceSearchEnvelope
open WorkMachineProgramGraph (endpointConfiguration)
open PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank

example : BlankOutside ([] : List WorkSymbol) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.blank_nil

example (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (WorkSymbol.blank :: outside) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.blank_cons outside hBlank

example (outside : List WorkSymbol) (amount : Nat) (hBlank : BlankOutside outside) :
    BlankOutside (outside.drop amount) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.blank_drop outside amount hBlank

example (amount : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (List.replicate amount WorkSymbol.blank ++ outside) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.blank_replicate_append amount outside hBlank

example (count : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralSearchGuard.finalOutside count outside) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.guard_blank count outside hBlank

example (positive : Bool) (value position : Nat) (outside : List WorkSymbol)
    (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralTokenSelector.finalOutside positive value position outside) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.literal_blank positive value position outside hBlank

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderPayloadLiteralTokenSelector.prepareOutside source context outside) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.payload_prepare_blank source context outside hBlank

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderPayloadSearchComparison.finalOutside source context outside) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.comparison_blank source context outside hBlank

example {width : Nat} (source : Source width) (context : Context source.ordinal)
    (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderPayloadSearchHit.finalOutside source context outside) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.hit_blank source context outside hBlank

example (ordinal remaining residual : Nat) (outside : List WorkSymbol)
    (hBlank : BlankOutside outside) :
    BlankOutside (BuilderPayloadSearchAdvance.finalOutside ordinal remaining residual outside) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.advance_blank ordinal remaining residual outside hBlank

example {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (ordinal remaining : Nat) (prior : List Nat)
    (hIndex : ordinal < (body constraint).length) (hPrior : prior.length = 17 * ordinal)
    (position : Nat) (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).hitOutside ∧
      BlankOutside (costVisit constraint request older ordinal remaining prior hIndex hPrior position outside).nextOutside :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.visit_blank constraint request older ordinal remaining prior hIndex hPrior position outside hBlank

example {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (ordinal count : Nat) (prior : List Nat) (position : Nat) (outside : List WorkSymbol)
    (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol)
    (hTrace : CostTrace constraint request older ordinal count prior position outside steps values resultOutside) :
    BlankOutside outside → BlankOutside resultOutside :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.trace_blank constraint request older ordinal count prior position outside steps values resultOutside hTrace

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (initialValues constraint request older [] 0 (body constraint).length position)).length +
      outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (resultValues : List Nat) (resultOutside : List WorkSymbol),
      workRunExact? (BuilderPayloadSourceSearchControl.machine (family constraint)) steps
        (workStartConfiguration (BuilderPayloadSourceSearchControl.machine (family constraint))
          (endTape (initialValues constraint request older [] 0 (body constraint).length position) inside outside)) =
        some (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
          (endTape resultValues inside resultOutside)) ∧
      BuilderLiteralTokenSelector.observe
        (endpointConfiguration (BuilderLiteralListSearch.endpoint (body constraint) position)
          (endTape resultValues inside resultOutside)) =
        DirectToken.boundedLiteralListSlot (body constraint) position ∧
      (∃ scratch, resultValues = requestValues constraint request older ++ scratch) ∧
      (BuilderLiteralListSearch.endpoint (body constraint) position = .dead →
        ∃ finalPrior, finalPrior.length = 17 * (body constraint).length ∧
          resultValues = initialValues constraint request older finalPrior (body constraint).length 0
            (position - DirectToken.boundedLiteralListWidth (body constraint))) ∧
      (registerWord resultValues).length + resultOutside.length ≤ (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input ∧
      (BlankOutside outside → BlankOutside resultOutside) :=
  PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlank.source_polynomial_bounds constraint request position older inside outside bound input hSpan

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearchBlankFrameRegression

namespace PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelectorFrameRegression

open PipelineTape
open BuilderPayloadSourceSearchBlank (BlankOutside)
open BuilderUnaryPolynomial (registerWord registerWord_length registerWord_append)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family Request family body requestValues)
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration endpointState)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)
open PipelineStateNamespace (renameConfiguration)
open PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector

example (route : Family) : (graph route).nodes.length = 6 :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.graph_nodes_length route

example :
    ([trueState,1,2,separatorState,finishState] : List Nat).Pairwise (fun left right => left ≠ right) :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.terminal_states_distinct

example (route : Family) : (graph route).WellFormed :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.graph_wellFormed route

example (route : Family) : WorkMachineChain.NoRuleAtAccept (machine route) :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.noRuleAtAccept route

example (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) (machine route).rejectState :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.noRuleAtReject route

example (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) 2 :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.noRuleAtPadding route

example (route : Family) : (machine route).rules.Pairwise WorkMachineChain.QueryDistinct :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.rules_pairwise_query_distinct route

example (route : Family) : (machine route).acceptState ≠ (machine route).rejectState :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.acceptState_ne_rejectState route

example (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) separatorState :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.noRuleAtSeparator route

example (route : Family) : WorkMachineProgramGraph.NoRuleAt (machine route) finishState :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.noRuleAtFinish route

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) :
    initialValues constraint request position older = entryOlder constraint request older ++ [position] :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.initial_values_suffix constraint request position older

example {width : Nat} (constraint : LocalConstraint width)
    (position : Nat) (tape : WorkTape) :
    observe (endpointConfiguration (endpoint constraint position) tape) =
      (encodeClauseTokens (BoundedClause.emit (body constraint)))[position]? :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.endpoint_observes_encoding constraint position tape

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (hPositive : 0 < position) :
    (registerWord (initialValues constraint request (position - 1) older)).length +
        (bodyOutside outside).length =
      (registerWord (initialValues constraint request position older)).length + outside.length :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.body_input_span constraint request position older outside hPositive

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
      6 * steps ≤ (rawTimePolynomial bound).eval input ∧
      (BlankOutside outside → BlankOutside resultOutside) :=
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.workRun_polynomial_lookup_with_blank constraint request position older inside outside bound input hSpan

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
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.workRun_polynomial_lookup constraint request position older inside outside bound input hSpan

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
  PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelector.uniform_polynomial_lookup constraint request position older inside outside bound input hSpan

end PNP.Concrete.CookLevin.BuilderPayloadClauseTokenSelectorFrameRegression

namespace PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookupFrameRegression

open PipelineTape
open BuilderPayloadSourceSearchBlank (BlankOutside)
open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family Request family body requestValues)
open WorkMachineProgramGraph (endpointConfiguration)
open PipelineStateNamespace (renameConfiguration)
open PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup

example :
    ([trueState,falseState,paddingState,separatorState,finishState] : List Nat).Pairwise
      (fun left right => left ≠ right) :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.terminal_states_distinct

example (configuration : WorkConfiguration) :
    observe (renameConfiguration WorkMachineChain.secondState configuration) =
      BuilderPayloadClauseTokenSelector.observe configuration :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.observe_rename configuration

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (values : List Nat) (inside outside : List WorkSymbol) :
    observe (finalConfiguration constraint request values inside outside) =
      (encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]? :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.final_observation constraint request values inside outside

example (route : Family) :
    (machine route).rules.Pairwise WorkMachineChain.QueryDistinct :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.rules_pairwise_query_distinct route

example (route : Family) : WorkMachineChain.NoRuleAtAccept (machine route) :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtAccept route

example (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) (machine route).rejectState :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtReject route

example (route : Family) :
    (machine route).acceptState ≠ (machine route).rejectState :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.acceptState_ne_rejectState route

example (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) paddingState :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtPadding route

example (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) separatorState :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtSeparator route

example (route : Family) :
    WorkMachineProgramGraph.NoRuleAt (machine route) finishState :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.noRuleAtFinish route

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
      6 * steps ≤ (rawTimePolynomial bound).eval input ∧
      (BlankOutside outside → BlankOutside resultOutside) :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.workRun_polynomial_lookup_with_blank constraint request older inside outside bound input hSpan

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
      6 * steps ≤ (rawTimePolynomial bound).eval input :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.workRun_polynomial_lookup constraint request older inside outside bound input hSpan

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
      (registerWord values).length + resultOutside.length ≤ (spanPolynomial bound).eval input :=
  PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookup.uniform_polynomial_lookup constraint request older inside outside bound input hSpan

end PNP.Concrete.CookLevin.BuilderPayloadBodyTokenLookupFrameRegression

namespace PNP.Concrete.CookLevin.PayloadTokenFrameBoundaryRegression

open BuilderPayloadSourceSearchBlank

example : BlankOutside ([] : List WorkSymbol) := blank_nil

example (amount : Nat) : BlankOutside (List.replicate amount WorkSymbol.blank) := by
  simpa only [List.append_nil] using blank_replicate_append amount [] blank_nil

example : ¬ BlankOutside [WorkSymbol.oneBlank] := by
  intro h
  have hZero : WorkSymbol.oneBlank = WorkSymbol.blank := h 0
  cases hZero

example (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralSearchGuard.finalOutside 0 outside) := guard_blank 0 outside hBlank

example (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralTokenSelector.finalOutside true 0 0 outside) := literal_blank true 0 0 outside hBlank

example (outside : List WorkSymbol) (hBlank : BlankOutside outside) :
    BlankOutside (BuilderLiteralTokenSelector.finalOutside false 0 7 outside) := literal_blank false 0 7 outside hBlank

example : BuilderPayloadBodyTokenLookup.trueState ≠ BuilderPayloadBodyTokenLookup.falseState := by decide

example : BuilderPayloadBodyTokenLookup.falseState ≠ BuilderPayloadBodyTokenLookup.paddingState := by decide

end PNP.Concrete.CookLevin.PayloadTokenFrameBoundaryRegression
