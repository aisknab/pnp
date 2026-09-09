/-
Copyright (c) 2026 PNP Labs.

Control well-formedness, actual guard/hit path composition, fixed back edges and
stable outcomes for every source family. No runtime input builds a new graph.
-/
import PNP.Concrete.CookLevinBuilderPayloadSourceSearchControl

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearchControlRegression

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family bodyKind lastKind)
open WorkMachineProgramGraph (Node NodeRef Graph Endpoint endpointConfiguration)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)
open BuilderPayloadSourceSearchControl

example (family : Family) : (graph family).nodes.length = 7 :=
  BuilderPayloadSourceSearchControl.graph_nodes_length family

example (family : Family) : (guardNode family).reference = guardReference :=
  BuilderPayloadSourceSearchControl.guard_reference family

example (family : Family) : guardNode family ∈ (graph family).nodes :=
  BuilderPayloadSourceSearchControl.guard_mem family

example (family : Family) : lastNode family ∈ (graph family).nodes :=
  BuilderPayloadSourceSearchControl.last_mem family

example (family : Family) : bodyCompareNode family ∈ (graph family).nodes :=
  BuilderPayloadSourceSearchControl.bodyCompare_mem family

example (family : Family) : lastCompareNode family ∈ (graph family).nodes :=
  BuilderPayloadSourceSearchControl.lastCompare_mem family

example (family : Family) : bodyHitNode family ∈ (graph family).nodes :=
  BuilderPayloadSourceSearchControl.bodyHit_mem family

example (family : Family) : lastHitNode family ∈ (graph family).nodes :=
  BuilderPayloadSourceSearchControl.lastHit_mem family

example (family : Family) : advanceNode ∈ (graph family).nodes :=
  BuilderPayloadSourceSearchControl.advance_mem family

example (family : Family) (last : Bool) : compareNode family last ∈ (graph family).nodes :=
  BuilderPayloadSourceSearchControl.compare_mem family last

example (family : Family) (last : Bool) : hitNode family last ∈ (graph family).nodes :=
  BuilderPayloadSourceSearchControl.hit_mem family last

example (family : Family) (last : Bool) :
    (compareNode family last).program = BuilderPayloadSearchComparison.machine (visitKind family last) :=
  BuilderPayloadSourceSearchControl.compare_program family last

example (family : Family) (last : Bool) :
    (hitNode family last).program = BuilderPayloadSearchHit.machine (visitKind family last) :=
  BuilderPayloadSourceSearchControl.hit_program family last

example (family : Family) (last : Bool) :
    (compareNode family last).onAccept = .node (hitNode family last).reference :=
  BuilderPayloadSourceSearchControl.compare_accept family last

example (family : Family) (last : Bool) :
    (compareNode family last).onReject = .node advanceNode.reference :=
  BuilderPayloadSourceSearchControl.compare_reject family last

example (family : Family) (last : Bool) : (hitNode family last).onAccept = .accept :=
  BuilderPayloadSourceSearchControl.hit_accept family last

example (family : Family) (last : Bool) : (hitNode family last).onReject = .reject :=
  BuilderPayloadSourceSearchControl.hit_reject family last

example (family : Family) (count : Nat) :
    visitKind family (lastFlag count) = BuilderPayloadSearchSource.kindAt family count :=
  BuilderPayloadSourceSearchControl.visitKind_lastFlag family count

example (family : Family) : (graph family).WellFormed :=
  BuilderPayloadSourceSearchControl.graph_wellFormed family

example (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} :=
  BuilderPayloadSourceSearchControl.configuration_eq_of_fields config state tape hState hTape

example (family : Family) (base : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) (target : Endpoint) (tailSteps : Nat) (final : WorkTape)
    (hPositive : 0 < count)
    (hTail : AcceptPath (graph family) (.node (compareNode family (lastFlag count)).reference) target tailSteps
      (endTape (base ++ [ordinal,count,position]) inside (guardedOutside count outside)) final) :
    AcceptPath (graph family) (.node (guardNode family).reference) target (guardSteps count position + tailSteps)
      (endTape (base ++ [ordinal,count,position]) inside outside) final :=
  BuilderPayloadSourceSearchControl.guards_path family base ordinal count position inside outside target tailSteps final hPositive hTail

example (positive : Bool) (value position : Nat) (hHit : position < value + 2) :
    BuilderLiteralTokenSelector.endpoint positive value position = .accept ∨
      BuilderLiteralTokenSelector.endpoint positive value position = .reject :=
  BuilderPayloadSourceSearchControl.literal_endpoint_terminal positive value position hHit

example {width : Nat} (family : Family) (last : Bool)
    (source : BuilderPayloadLiteralTokenSelector.Source width)
    (context : BuilderPayloadLiteralTokenSelector.Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol)
    (hKind : source.kind = visitKind family last)
    (hHit : context.position < source.originalLiteral.index.val + 2) :
    AcceptPath (graph family) (.node (hitNode family last).reference)
      (BuilderLiteralTokenSelector.endpoint source.selectedLiteral.positive source.originalLiteral.index.val context.position)
      (BuilderPayloadSearchHit.workSteps source context + 1)
      (endTape (BuilderPayloadSearchHit.initialValues source context older) inside outside)
      (BuilderPayloadSearchHit.finalConfiguration source context older inside outside).tape :=
  BuilderPayloadSourceSearchControl.hit_path family last source context older inside outside hKind hHit

example (family : Family) (target : Endpoint) (steps tailSteps : Nat)
    (initial middle final : WorkTape)
    (hRun : LocalAcceptRun advanceNode steps initial middle)
    (hTail : AcceptPath (graph family) (.node (guardNode family).reference) target tailSteps middle final) :
    AcceptPath (graph family) (.node advanceNode.reference) target (steps + 1 + tailSteps) initial final :=
  BuilderPayloadSourceSearchControl.advance_path family target steps tailSteps initial middle final hRun hTail

example (family : Family) :
    (BuilderPayloadSourceSearchControl.machine family).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  BuilderPayloadSourceSearchControl.rules_pairwise_query_distinct family

example (family : Family) : WorkMachineProgramGraph.NoRuleAt (BuilderPayloadSourceSearchControl.machine family) (BuilderPayloadSourceSearchControl.machine family).acceptState :=
  BuilderPayloadSourceSearchControl.noRuleAtAccept family

example (family : Family) : WorkMachineProgramGraph.NoRuleAt (BuilderPayloadSourceSearchControl.machine family) (BuilderPayloadSourceSearchControl.machine family).rejectState :=
  BuilderPayloadSourceSearchControl.noRuleAtReject family

example (family : Family) : WorkMachineProgramGraph.NoRuleAt (BuilderPayloadSourceSearchControl.machine family) 2 :=
  BuilderPayloadSourceSearchControl.noRuleAtPadding family

example (family : Family) : (BuilderPayloadSourceSearchControl.machine family).acceptState ≠ (BuilderPayloadSourceSearchControl.machine family).rejectState :=
  BuilderPayloadSourceSearchControl.acceptState_ne_rejectState family

-- Independent fixed routing contracts, not generated node-count expectations.
example (family : Family) :
    (graph family).nodes.map Node.name = [0,1,2,3,4,5,6] := rfl
example (family : Family) : (guardNode family).onAccept = .dead := rfl
example (family : Family) :
    (lastNode family).onAccept = .node (lastCompareNode family).reference ∧
    (lastNode family).onReject = .node (bodyCompareNode family).reference := ⟨rfl,rfl⟩
example (family : Family) :
    (bodyCompareNode family).onReject = .node advanceNode.reference ∧
    (lastCompareNode family).onReject = .node advanceNode.reference := ⟨rfl,rfl⟩
example : advanceNode.onAccept = .node guardReference := rfl
example : visitKind .implication false = .premise := rfl
example : visitKind .implication true = .conclusion := rfl
example : lastFlag 0 = false := rfl
example : lastFlag 1 = true := rfl
example : lastFlag 2 = false := rfl

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearchControlRegression
