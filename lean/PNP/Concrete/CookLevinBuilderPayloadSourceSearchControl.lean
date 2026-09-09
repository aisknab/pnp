/-
Copyright (c) 2026 PNP Labs.

Seven-node source-body search control. The zero and count-one tests select the
actual body/final schema; both miss paths share the same cursor and return to
the zero guard. Only the fixed three-way source family selects this graph.

The complete loop theorem must construct its path from the actual payload.
The path-composition interfaces below are not caller-supplied proof authority.
-/
import PNP.Concrete.CookLevinBuilderPayloadSearchSource
import PNP.Concrete.CookLevinBuilderPayloadSearchAdvance
import PNP.Concrete.CookLevinBuilderLiteralListSearch

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearchControl

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPayloadSearchSource (Family bodyKind lastKind)
open WorkMachineProgramGraph (Node NodeRef Graph Endpoint endpointConfiguration)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

def guardReference : NodeRef := {name := 0, startState := BuilderLiteralSearchGuard.machine.startState}
def advanceNode : Node :=
  {name := 6, program := BuilderPayloadSearchAdvance.machine, onAccept := .node guardReference, onReject := .dead}
def bodyHitNode (family : Family) : Node :=
  {name := 4, program := BuilderPayloadSearchHit.machine (bodyKind family), onAccept := .accept, onReject := .reject}
def lastHitNode (family : Family) : Node :=
  {name := 5, program := BuilderPayloadSearchHit.machine (lastKind family), onAccept := .accept, onReject := .reject}
def bodyCompareNode (family : Family) : Node :=
  {name := 2, program := BuilderPayloadSearchComparison.machine (bodyKind family),
   onAccept := .node (bodyHitNode family).reference, onReject := .node advanceNode.reference}
def lastCompareNode (family : Family) : Node :=
  {name := 3, program := BuilderPayloadSearchComparison.machine (lastKind family),
   onAccept := .node (lastHitNode family).reference, onReject := .node advanceNode.reference}
def lastNode (family : Family) : Node :=
  {name := 1, program := BuilderPayloadConclusionGuard.machine,
   onAccept := .node (lastCompareNode family).reference, onReject := .node (bodyCompareNode family).reference}
def guardNode (family : Family) : Node :=
  {name := 0, program := BuilderLiteralSearchGuard.machine,
   onAccept := .dead, onReject := .node (lastNode family).reference}
def graph (family : Family) : Graph :=
  {nodes := [guardNode family,lastNode family,bodyCompareNode family,lastCompareNode family,
    bodyHitNode family,lastHitNode family,advanceNode], entry := guardReference}
def machine (family : Family) : WorkMachine := WorkMachineProgramGraph.machine (graph family)

def visitKind (family : Family) (last : Bool) : BuilderPayloadLiteralTokenSelector.Kind :=
  if last then lastKind family else bodyKind family
def lastFlag (count : Nat) : Bool := if count = 1 then true else false
def compareNode (family : Family) (last : Bool) : Node :=
  if last then lastCompareNode family else bodyCompareNode family
def hitNode (family : Family) (last : Bool) : Node :=
  if last then lastHitNode family else bodyHitNode family

theorem graph_nodes_length (family : Family) : (graph family).nodes.length = 7 := rfl
theorem guard_reference (family : Family) : (guardNode family).reference = guardReference := rfl

theorem guard_mem (family : Family) : guardNode family ∈ (graph family).nodes := List.Mem.head _

theorem last_mem (family : Family) : lastNode family ∈ (graph family).nodes := List.Mem.tail _ (List.Mem.head _)

theorem bodyCompare_mem (family : Family) : bodyCompareNode family ∈ (graph family).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem lastCompare_mem (family : Family) : lastCompareNode family ∈ (graph family).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem bodyHit_mem (family : Family) : bodyHitNode family ∈ (graph family).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem lastHit_mem (family : Family) : lastHitNode family ∈ (graph family).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem advance_mem (family : Family) : advanceNode ∈ (graph family).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

theorem compare_mem (family : Family) (last : Bool) : compareNode family last ∈ (graph family).nodes := by
  cases last
  · exact bodyCompare_mem family
  · exact lastCompare_mem family
theorem hit_mem (family : Family) (last : Bool) : hitNode family last ∈ (graph family).nodes := by
  cases last
  · exact bodyHit_mem family
  · exact lastHit_mem family

theorem compare_program (family : Family) (last : Bool) :
    (compareNode family last).program = BuilderPayloadSearchComparison.machine (visitKind family last) := by
  cases last <;> rfl
theorem hit_program (family : Family) (last : Bool) :
    (hitNode family last).program = BuilderPayloadSearchHit.machine (visitKind family last) := by
  cases last <;> rfl
theorem compare_accept (family : Family) (last : Bool) :
    (compareNode family last).onAccept = .node (hitNode family last).reference := by
  cases last <;> rfl
theorem compare_reject (family : Family) (last : Bool) :
    (compareNode family last).onReject = .node advanceNode.reference := by
  cases last <;> rfl
theorem hit_accept (family : Family) (last : Bool) : (hitNode family last).onAccept = .accept := by
  cases last <;> rfl
theorem hit_reject (family : Family) (last : Bool) : (hitNode family last).onReject = .reject := by
  cases last <;> rfl

theorem visitKind_lastFlag (family : Family) (count : Nat) :
    visitKind family (lastFlag count) = BuilderPayloadSearchSource.kindAt family count := by
  by_cases h : count = 1
  · rw [lastFlag, if_pos h, BuilderPayloadSearchSource.kindAt, if_pos h]
    rfl
  · rw [lastFlag, if_neg h, BuilderPayloadSearchSource.kindAt, if_neg h]
    rfl

theorem graph_wellFormed (family : Family) : (graph family).WellFormed := by
  have hNames : ((graph family).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2,3,4,5,6] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨BuilderLiteralSearchGuard.rules_pairwise_query_distinct, BuilderLiteralSearchGuard.noRuleAtAccept,
        BuilderLiteralSearchGuard.noRuleAtReject, BuilderLiteralSearchGuard.acceptState_ne_rejectState⟩
    · exact ⟨BuilderPayloadConclusionGuard.rules_pairwise_query_distinct, BuilderPayloadConclusionGuard.noRuleAtAccept,
        BuilderPayloadConclusionGuard.noRuleAtReject, BuilderPayloadConclusionGuard.acceptState_ne_rejectState⟩
    · exact ⟨BuilderPayloadSearchComparison.rules_pairwise_query_distinct _, BuilderPayloadSearchComparison.noRuleAtAccept _,
        BuilderPayloadSearchComparison.noRuleAtReject _, BuilderPayloadSearchComparison.acceptState_ne_rejectState _⟩
    · exact ⟨BuilderPayloadSearchComparison.rules_pairwise_query_distinct _, BuilderPayloadSearchComparison.noRuleAtAccept _,
        BuilderPayloadSearchComparison.noRuleAtReject _, BuilderPayloadSearchComparison.acceptState_ne_rejectState _⟩
    · exact ⟨BuilderPayloadSearchHit.rules_pairwise_query_distinct _, BuilderPayloadSearchHit.noRuleAtAccept _,
        BuilderPayloadSearchHit.noRuleAtReject _, BuilderPayloadSearchHit.acceptState_ne_rejectState _⟩
    · exact ⟨BuilderPayloadSearchHit.rules_pairwise_query_distinct _, BuilderPayloadSearchHit.noRuleAtAccept _,
        BuilderPayloadSearchHit.noRuleAtReject _, BuilderPayloadSearchHit.acceptState_ne_rejectState _⟩
    · exact ⟨BuilderPayloadSearchAdvance.rules_pairwise_query_distinct, BuilderPayloadSearchAdvance.noRuleAtAccept,
        BuilderPayloadSearchAdvance.noRuleAtReject, BuilderPayloadSearchAdvance.acceptState_ne_rejectState⟩
  · exact ⟨guardNode family, guard_mem family, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨True.intro, ⟨lastNode family, last_mem family, rfl, rfl⟩⟩
    · exact ⟨⟨lastCompareNode family, lastCompare_mem family, rfl, rfl⟩,
        ⟨bodyCompareNode family, bodyCompare_mem family, rfl, rfl⟩⟩
    · exact ⟨⟨bodyHitNode family, bodyHit_mem family, rfl, rfl⟩,
        ⟨advanceNode, advance_mem family, rfl, rfl⟩⟩
    · exact ⟨⟨lastHitNode family, lastHit_mem family, rfl, rfl⟩,
        ⟨advanceNode, advance_mem family, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨guardNode family, guard_mem family, rfl, rfl⟩, True.intro⟩

theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      subst currentState
      subst currentTape
      rfl

def guardedOutside (count : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  BuilderPayloadConclusionGuard.finalOutside count (BuilderLiteralSearchGuard.finalOutside count outside)
def guardSteps (count position : Nat) : Nat :=
  BuilderLiteralSearchGuard.workSteps count position + 1 +
    (BuilderPayloadConclusionGuard.workSteps count position + 1)

/-- Both branch choices are derived from the runtime count and restore its frame. -/
theorem guards_path (family : Family) (base : List Nat) (ordinal count position : Nat)
    (inside outside : List WorkSymbol) (target : Endpoint) (tailSteps : Nat) (final : WorkTape)
    (hPositive : 0 < count)
    (hTail : AcceptPath (graph family) (.node (compareNode family (lastFlag count)).reference) target tailSteps
      (endTape (base ++ [ordinal,count,position]) inside (guardedOutside count outside)) final) :
    AcceptPath (graph family) (.node (guardNode family).reference) target (guardSteps count position + tailSteps)
      (endTape (base ++ [ordinal,count,position]) inside outside) final := by
  let guarded := BuilderLiteralSearchGuard.finalOutside count outside
  have hZero := BuilderLiteralSearchGuard.workRunExact base ordinal count position inside outside
  have hZeroState := (BuilderLiteralSearchGuard.final_reject_iff base ordinal count position inside outside).2 hPositive
  have hZeroTape := BuilderLiteralSearchGuard.final_tape base ordinal count position inside outside
  rw [configuration_eq_of_fields _ _ _ hZeroState hZeroTape] at hZero
  have hOne := BuilderPayloadConclusionGuard.workRunExact base ordinal count position inside guarded
  have hOneTape := BuilderPayloadConclusionGuard.final_tape base ordinal count position inside guarded
  have hLast : AcceptPath (graph family) (.node (lastNode family).reference) target
      (BuilderPayloadConclusionGuard.workSteps count position + 1 + tailSteps)
      (endTape (base ++ [ordinal,count,position]) inside guarded) final := by
    by_cases hCount : count = 1
    · have hState := (BuilderPayloadConclusionGuard.final_accept_iff base ordinal count position inside guarded).2 hCount
      rw [configuration_eq_of_fields _ _ _ hState hOneTape] at hOne
      have h := AcceptPath.step (lastNode family) target _ tailSteps _ _ final (last_mem family) hOne
      apply h
      simpa only [lastNode, compareNode, lastFlag, if_pos hCount, ite_true, guardedOutside, guarded, BuilderPayloadConclusionGuard.frame] using hTail
    · have hState := (BuilderPayloadConclusionGuard.final_reject_iff base ordinal count position inside guarded).2 hCount
      rw [configuration_eq_of_fields _ _ _ hState hOneTape] at hOne
      have h := AcceptPath.stepReject (lastNode family) target _ tailSteps _ _ final (last_mem family) hOne
      apply h
      simpa only [lastNode, compareNode, lastFlag, if_neg hCount, Bool.false_eq_true, ite_false, guardedOutside, guarded, BuilderPayloadConclusionGuard.frame] using hTail
  have h := AcceptPath.stepReject (guardNode family) target _ _ _ _ final (guard_mem family) hZero hLast
  simpa only [guardSteps, BuilderLiteralSearchGuard.frame, Nat.add_assoc] using h

theorem literal_endpoint_terminal (positive : Bool) (value position : Nat) (hHit : position < value + 2) :
    BuilderLiteralTokenSelector.endpoint positive value position = .accept ∨
      BuilderLiteralTokenSelector.endpoint positive value position = .reject := by
  unfold BuilderLiteralTokenSelector.endpoint BuilderLiteralTokenSelector.unaryEndpoint
  by_cases hZero : position = 0
  · rw [if_pos hZero]
    cases positive
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [if_neg hZero]
    by_cases hLess : position - 1 < value
    · rw [if_pos hLess]
      exact Or.inl rfl
    · have hEqual : position - 1 = value := by omega
      rw [if_neg hLess, if_pos hEqual]
      exact Or.inr rfl

/-- The source-bound hit continuation returns a stable bit through the graph. -/
theorem hit_path {width : Nat} (family : Family) (last : Bool)
    (source : BuilderPayloadLiteralTokenSelector.Source width)
    (context : BuilderPayloadLiteralTokenSelector.Context source.ordinal)
    (older : List Nat) (inside outside : List WorkSymbol)
    (hKind : source.kind = visitKind family last)
    (hHit : context.position < source.originalLiteral.index.val + 2) :
    AcceptPath (graph family) (.node (hitNode family last).reference)
      (BuilderLiteralTokenSelector.endpoint source.selectedLiteral.positive source.originalLiteral.index.val context.position)
      (BuilderPayloadSearchHit.workSteps source context + 1)
      (endTape (BuilderPayloadSearchHit.initialValues source context older) inside outside)
      (BuilderPayloadSearchHit.finalConfiguration source context older inside outside).tape := by
  have hRun := BuilderPayloadSearchHit.workRunExact source context older inside outside
  rcases literal_endpoint_terminal source.selectedLiteral.positive source.originalLiteral.index.val context.position hHit with hAccept | hReject
  · have hState : (BuilderPayloadSearchHit.finalConfiguration source context older inside outside).state =
        (BuilderPayloadSearchHit.machine source.kind).acceptState := by
      change WorkMachineChain.secondState (WorkMachineChain.secondState
        (endpointConfiguration (BuilderLiteralTokenSelector.endpoint source.selectedLiteral.positive
          source.originalLiteral.index.val context.position) _).state) =
        WorkMachineChain.secondState (WorkMachineChain.secondState 0)
      rw [hAccept]
      rfl
    rw [configuration_eq_of_fields _ _ _ hState rfl] at hRun
    have hLocal : LocalAcceptRun (hitNode family last) (BuilderPayloadSearchHit.workSteps source context)
        (endTape (BuilderPayloadSearchHit.initialValues source context older) inside outside)
        (BuilderPayloadSearchHit.finalConfiguration source context older inside outside).tape := by
      unfold LocalAcceptRun
      rw [hit_program, ← hKind]
      exact hRun
    rw [hAccept]
    apply AcceptPath.step (hitNode family last) .accept _ 0 _ _ _ (hit_mem family last) hLocal
    rw [hit_accept]
    exact .terminal .accept _
  · have hState : (BuilderPayloadSearchHit.finalConfiguration source context older inside outside).state =
        (BuilderPayloadSearchHit.machine source.kind).rejectState := by
      change WorkMachineChain.secondState (WorkMachineChain.secondState
        (endpointConfiguration (BuilderLiteralTokenSelector.endpoint source.selectedLiteral.positive
          source.originalLiteral.index.val context.position) _).state) =
        WorkMachineChain.secondState (WorkMachineChain.secondState 1)
      rw [hReject]
      rfl
    rw [configuration_eq_of_fields _ _ _ hState rfl] at hRun
    have hLocal : LocalRejectRun (hitNode family last) (BuilderPayloadSearchHit.workSteps source context)
        (endTape (BuilderPayloadSearchHit.initialValues source context older) inside outside)
        (BuilderPayloadSearchHit.finalConfiguration source context older inside outside).tape := by
      unfold LocalRejectRun
      rw [hit_program, ← hKind]
      exact hRun
    rw [hReject]
    apply AcceptPath.stepReject (hitNode family last) .reject _ 0 _ _ _ (hit_mem family last) hLocal
    rw [hit_reject]
    exact .terminal .reject _

theorem advance_path (family : Family) (target : Endpoint) (steps tailSteps : Nat)
    (initial middle final : WorkTape)
    (hRun : LocalAcceptRun advanceNode steps initial middle)
    (hTail : AcceptPath (graph family) (.node (guardNode family).reference) target tailSteps middle final) :
    AcceptPath (graph family) (.node advanceNode.reference) target (steps + 1 + tailSteps) initial final := by
  apply AcceptPath.step advanceNode target steps tailSteps initial middle final (advance_mem family) hRun
  simpa only [advanceNode, guard_reference] using hTail

theorem rules_pairwise_query_distinct (family : Family) :
    (machine family).rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise (graph family) (graph_wellFormed family)
theorem noRuleAtAccept (family : Family) : WorkMachineProgramGraph.NoRuleAt (machine family) (machine family).acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept (graph family)
theorem noRuleAtReject (family : Family) : WorkMachineProgramGraph.NoRuleAt (machine family) (machine family).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject (graph family)
theorem noRuleAtPadding (family : Family) : WorkMachineProgramGraph.NoRuleAt (machine family) 2 :=
  WorkMachineProgramGraph.noRuleAt_globalDead (graph family)
theorem acceptState_ne_rejectState (family : Family) : (machine family).acceptState ≠ (machine family).rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearchControl
