/-
Copyright (c) 2026 PNP Labs.

Actual tag/index dispatch from every canonical source/request frame. One fixed
finite graph contains the three body-token machines and the negative-clause
machine. Physical guards derive their entry; no caller supplies a family,
positive-index premise, selected branch or successful dispatch certificate.
The original request survives in a blank-equivalent workspace. Missing sources
have a separate entry from padding. Every guard and bridge is charged.

This module proves arrival at the selected real token program. Complete token
execution, outcome recovery and the enclosing source-cursor loop remain separate
composition obligations; this is not the complete Cook-Levin builder.
-/
import PNP.Concrete.CookLevinBuilderRequestRegisterMatch
import PNP.Concrete.CookLevinBuilderPayloadBodyTokenLookup
import PNP.Concrete.CookLevinBuilderRequestedExclusionTokenLookup
import PNP.Concrete.CookLevinBuilderPayloadClauseOccupancy

namespace PNP.Concrete.CookLevin.BuilderRequestDispatch

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (Slot values)
open BuilderPayloadClauseOccupancy (tag beforeTag)
open BuilderPayloadSearchSource (Family Request family)
open WorkMachineProgramGraph (Node NodeRef Graph Endpoint endpointConfiguration endpointState)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

inductive Route where
  | missing | padding | required | implication | positive | exclusion
  deriving DecidableEq, Repr

def bodyNode (kind : Family) : Node :=
  {name := match kind with | .required => 8 | .implication => 9 | .positive => 10,
   program := BuilderPayloadBodyTokenLookup.machine kind, onAccept := .accept, onReject := .reject}
def exclusionNode : Node :=
  {name := 11, program := BuilderRequestedExclusionTokenLookup.machine, onAccept := .accept, onReject := .reject}
def absentProgram : WorkMachine := {rules := [], startState := 2, acceptState := 0, rejectState := 1}
def absentNode : Node :=
  {name := 12, program := absentProgram, onAccept := .dead, onReject := .dead}
def indexNode (kind : Family) : Node :=
  {name := match kind with | .required => 5 | .implication => 6 | .positive => 7,
   program := BuilderRequestRegisterMatch.machine 1 0, onAccept := .node (bodyNode kind).reference,
   onReject := if kind = .positive then .node exclusionNode.reference else .dead}
def tagRef (code : Nat) : NodeRef :=
  {name := code, startState := (BuilderRequestRegisterMatch.machine 11 code).startState}
def tagTarget : Nat → Endpoint
  | 0 => .node absentNode.reference
  | 1 => .dead
  | 2 => .node (indexNode .required).reference
  | 3 => .node (indexNode .implication).reference
  | _ => .node (indexNode .positive).reference
def tagNode (code : Nat) : Node :=
  {name := code, program := BuilderRequestRegisterMatch.machine 11 code,
   onAccept := tagTarget code, onReject := if code < 4 then .node (tagRef (code + 1)) else .dead}
def graph : Graph :=
  {nodes := [tagNode 0, tagNode 1, tagNode 2, tagNode 3, tagNode 4,
    indexNode .required, indexNode .implication, indexNode .positive,
    bodyNode .required, bodyNode .implication, bodyNode .positive, exclusionNode, absentNode],
   entry := tagRef 0}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

def route {width : Nat} : Slot width → Nat → Route
  | none, _ => .missing
  | some none, _ => .padding
  | some (some (.require _)), index => if index = 0 then .required else .padding
  | some (some (.implication _ _)), index => if index = 0 then .implication else .padding
  | some (some (.exactlyOne _)), index => if index = 0 then .positive else .exclusion
def entry : Route → Endpoint
  | .missing => .node absentNode.reference
  | .padding => .dead
  | .required => .node (bodyNode .required).reference
  | .implication => .node (bodyNode .implication).reference
  | .positive => .node (bodyNode .positive).reference
  | .exclusion => .node exclusionNode.reference

def requestValues {width : Nat} (slot : Slot width) (request : Request) (older : List Nat) : List Nat :=
  older ++ values slot ++ request.gap ++ [request.clauseIndex, request.originalPosition]
def tagPrefix {width : Nat} (slot : Slot width) (older : List Nat) : List Nat := older ++ beforeTag slot
def tagSuffix (request : Request) : List Nat := request.gap ++ [request.clauseIndex, request.originalPosition]
def indexPrefix {width : Nat} (slot : Slot width) (request : Request) (older : List Nat) : List Nat :=
  older ++ values slot ++ request.gap

theorem request_values_present {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat) :
    requestValues (some (some constraint)) request older =
      BuilderPayloadSearchSource.requestValues constraint request older := rfl

theorem tag_operand_layout {width : Nat} (slot : Slot width) (request : Request) (older : List Nat) :
    requestValues slot request older =
      BuilderRequestRegisterMatch.inputValues (tagPrefix slot older) (tag slot) (tagSuffix request) := by
  rw [requestValues, BuilderPayloadClauseOccupancy.values_suffix]
  simp only [BuilderRequestRegisterMatch.inputValues, tagPrefix, tagSuffix, List.append_assoc]

theorem tag_offset (request : Request) : (tagSuffix request).length = 11 := by
  simp only [tagSuffix, List.length_append, request.gap_length, List.length_cons, List.length_nil]

theorem index_operand_layout {width : Nat} (slot : Slot width) (request : Request) (older : List Nat) :
    requestValues slot request older =
      BuilderRequestRegisterMatch.inputValues (indexPrefix slot request older) request.clauseIndex [request.originalPosition] := by
  simp only [requestValues, indexPrefix, BuilderRequestRegisterMatch.inputValues,
    List.append_assoc, List.cons_append, List.nil_append]

theorem exclusion_invariant {width : Nat} (slot : Slot width) (index : Nat)
    (hRoute : route slot index = .exclusion) :
    ∃ variables : List (Fin width), slot = some (some (.exactlyOne variables)) ∧ 0 < index := by
  cases slot with
  | none => cases hRoute
  | some item =>
      cases item with
      | none => cases hRoute
      | some constraint =>
          cases constraint with
          | require literal =>
              by_cases hZero : index = 0 <;>
                simp only [route, hZero, ite_true, ite_false, reduceCtorEq] at hRoute
          | implication premises conclusion =>
              by_cases hZero : index = 0 <;>
                simp only [route, hZero, ite_true, ite_false, reduceCtorEq] at hRoute
          | exactlyOne variables =>
              refine ⟨variables, rfl, ?_⟩
              by_cases hZero : index = 0
              · simp only [route, hZero, ite_true, reduceCtorEq] at hRoute
              · omega

theorem missing_padding_states_distinct :
    endpointState (entry .missing) ≠ endpointState (entry .padding) := by
  have h := WorkMachineProgramGraph.nodeState_ge_three absentNode.name absentNode.program.startState
  change WorkMachineProgramGraph.nodeState absentNode.name absentNode.program.startState ≠ 2
  omega

private theorem tag_mem (code : Nat) (hCode : code ≤ 4) : tagNode code ∈ graph.nodes := by
  have h : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 ∨ code = 4 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact List.Mem.head _
  · exact List.Mem.tail _ (List.Mem.head _)
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem index_mem (kind : Family) : indexNode kind ∈ graph.nodes := by
  cases kind with
  | required => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  | implication => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
  | positive => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
private theorem body_mem (kind : Family) : bodyNode kind ∈ graph.nodes := by
  cases kind with
  | required => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  | implication => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  | positive => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
private theorem exclusion_mem : exclusionNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
private theorem absent_mem : absentNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))

private theorem guard_good (node : Node) (offset expected : Nat)
    (hProgram : node.program = BuilderRequestRegisterMatch.machine offset expected) : node.WellFormed := by
  unfold Node.WellFormed
  rw [hProgram]
  exact ⟨BuilderRequestRegisterMatch.rules_pairwise_query_distinct offset expected,
    BuilderRequestRegisterMatch.noRuleAtAccept offset expected,
    BuilderRequestRegisterMatch.noRuleAtReject offset expected,
    BuilderRequestRegisterMatch.acceptState_ne_rejectState offset expected⟩
private theorem body_good (kind : Family) : (bodyNode kind).WellFormed :=
  ⟨BuilderPayloadBodyTokenLookup.rules_pairwise_query_distinct kind,
    BuilderPayloadBodyTokenLookup.noRuleAtAccept kind,
    BuilderPayloadBodyTokenLookup.noRuleAtReject kind,
    BuilderPayloadBodyTokenLookup.acceptState_ne_rejectState kind⟩
private theorem exclusion_good : exclusionNode.WellFormed :=
  ⟨BuilderRequestedExclusionTokenLookup.rules_pairwise_query_distinct,
    BuilderRequestedExclusionTokenLookup.noRuleAtAccept,
    BuilderRequestedExclusionTokenLookup.noRuleAtReject,
    BuilderRequestedExclusionTokenLookup.acceptState_ne_rejectState⟩
private theorem absent_good : absentNode.WellFormed := by
  refine ⟨List.Pairwise.nil, ?_, ?_, ?_⟩
  · intro rule hMem; cases hMem
  · intro rule hMem; cases hMem
  · change (0 : Nat) ≠ 1; decide

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2,3,4,5,6,7,8,9,10,11,12] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact guard_good _ 11 0 rfl
    · exact guard_good _ 11 1 rfl
    · exact guard_good _ 11 2 rfl
    · exact guard_good _ 11 3 rfl
    · exact guard_good _ 11 4 rfl
    · exact guard_good _ 1 0 rfl
    · exact guard_good _ 1 0 rfl
    · exact guard_good _ 1 0 rfl
    · exact body_good .required
    · exact body_good .implication
    · exact body_good .positive
    · exact exclusion_good
    · exact absent_good
  · exact ⟨tagNode 0, tag_mem 0 (by decide), rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨absentNode, absent_mem, rfl, rfl⟩, ⟨tagNode 1, tag_mem 1 (by decide), rfl, rfl⟩⟩
    · exact ⟨True.intro, ⟨tagNode 2, tag_mem 2 (by decide), rfl, rfl⟩⟩
    · exact ⟨⟨indexNode .required, index_mem .required, rfl, rfl⟩, ⟨tagNode 3, tag_mem 3 (by decide), rfl, rfl⟩⟩
    · exact ⟨⟨indexNode .implication, index_mem .implication, rfl, rfl⟩, ⟨tagNode 4, tag_mem 4 (by decide), rfl, rfl⟩⟩
    · exact ⟨⟨indexNode .positive, index_mem .positive, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨bodyNode .required, body_mem .required, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨bodyNode .implication, body_mem .implication, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨bodyNode .positive, body_mem .positive, rfl, rfl⟩, ⟨exclusionNode, exclusion_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise _ graph_wellFormed
theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := WorkMachineProgramGraph.noRuleAt_globalAccept _
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := WorkMachineProgramGraph.noRuleAt_globalReject _
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

private def Through (word : List Nat) (inside : List WorkSymbol) (start finish : Endpoint) (cost : Nat) : Prop :=
  ∀ tape : WorkTape, WorkTape.BlankEquivalent tape (endTape word inside []) →
    ∃ (steps : Nat) (next : WorkTape), AcceptPath graph start finish steps tape next ∧
      WorkTape.BlankEquivalent next (endTape word inside []) ∧ 6 * steps ≤ cost

private theorem through_mono {word : List Nat} {inside : List WorkSymbol} {start finish : Endpoint} {small large : Nat}
    (h : Through word inside start finish small) (hBound : small ≤ large) : Through word inside start finish large := by
  intro tape hTape
  obtain ⟨steps, next, hPath, hNext, hTime⟩ := h tape hTape
  exact ⟨steps, next, hPath, hNext, Nat.le_trans hTime hBound⟩

private theorem through_trans {word : List Nat} {inside : List WorkSymbol} {start middle finish : Endpoint} {left right : Nat}
    (first : Through word inside start middle left) (second : Through word inside middle finish right) :
    Through word inside start finish (left + right) := by
  intro tape hTape
  obtain ⟨firstSteps, middleTape, hFirst, hMiddle, hFirstTime⟩ := first tape hTape
  obtain ⟨secondSteps, finalTape, hSecond, hFinal, hSecondTime⟩ := second middleTape hMiddle
  refine ⟨firstSteps + secondSteps, finalTape, AcceptPath.trans graph _ _ _ _ _ _ _ _ hFirst hSecond, hFinal, ?_⟩
  omega

private theorem configuration_state (configuration : WorkConfiguration) (state : Nat) (hState : configuration.state = state) :
    configuration = {state := state, tape := configuration.tape} := by
  cases configuration
  cases hState
  rfl

private theorem guard_accept_projection (offset expected : Nat) :
    (BuilderRequestRegisterMatch.machine offset expected).acceptState = endpointState .accept := rfl

private theorem guard_reject_projection (offset expected : Nat) :
    (BuilderRequestRegisterMatch.machine offset expected).rejectState = endpointState .reject := rfl

private theorem guard_through (node : Node) (offset expected actual : Nat) (olderPrefix suffix word : List Nat)
    (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hMember : node ∈ graph.nodes) (hProgram : node.program = BuilderRequestRegisterMatch.machine offset expected)
    (hWord : word = BuilderRequestRegisterMatch.inputValues olderPrefix actual suffix)
    (hLength : suffix.length = offset) (hSpan : (registerWord word).length ≤ bound.eval input) :
    Through word inside (.node node.reference) (if actual = expected then node.onAccept else node.onReject)
      ((BuilderRequestRegisterMatch.rawTimePolynomial expected bound).eval input + 6) := by
  intro tape hTape
  have hSpan' : (registerWord (BuilderRequestRegisterMatch.inputValues olderPrefix actual suffix)).length ≤ bound.eval input := by
    simpa only [hWord] using hSpan
  have hTape' : WorkTape.BlankEquivalent tape (endTape (BuilderRequestRegisterMatch.inputValues olderPrefix actual suffix) inside []) := by
    simpa only [hWord] using hTape
  obtain ⟨final, hRun, hState, hNext, hTime⟩ :=
    BuilderRequestRegisterMatch.workRun_preserving_match offset expected actual olderPrefix suffix inside tape bound input hLength hSpan' hTape'
  refine ⟨BuilderRequestRegisterMatch.workSteps expected actual suffix + 1, final.tape, ?_, ?_, ?_⟩
  · by_cases hEqual : actual = expected
    · have hAccept : final.state = (BuilderRequestRegisterMatch.machine offset expected).acceptState := by
        simpa only [BuilderRequestRegisterMatch.endpoint, if_pos hEqual, guard_accept_projection] using hState
      have hLocal : LocalAcceptRun node (BuilderRequestRegisterMatch.workSteps expected actual suffix) tape final.tape := by
        unfold LocalAcceptRun
        rw [hProgram]
        rw [configuration_state final _ hAccept] at hRun
        exact hRun
      have hPath := AcceptPath.step node node.onAccept _ 0 _ _ _ hMember hLocal (.terminal node.onAccept _)
      simpa only [if_pos hEqual, Nat.add_zero] using hPath
    · have hReject : final.state = (BuilderRequestRegisterMatch.machine offset expected).rejectState := by
        simpa only [BuilderRequestRegisterMatch.endpoint, if_neg hEqual, guard_reject_projection] using hState
      have hLocal : LocalRejectRun node (BuilderRequestRegisterMatch.workSteps expected actual suffix) tape final.tape := by
        unfold LocalRejectRun
        rw [hProgram]
        rw [configuration_state final _ hReject] at hRun
        exact hRun
      have hPath := AcceptPath.stepReject node node.onReject _ 0 _ _ _ hMember hLocal (.terminal node.onReject _)
      simpa only [if_neg hEqual, Nat.add_zero] using hPath
  · simpa only [hWord] using hNext
  · omega

def tagRawPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRequestRegisterMatch.rawTimePolynomial 4 bound) (.constant 6)
def indexRawPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRequestRegisterMatch.rawTimePolynomial 0 bound) (.constant 6)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 5) (tagRawPolynomial bound)) (indexRawPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add bound (rawTimePolynomial bound)

private theorem tag_raw_mono (code : Nat) (hCode : code ≤ 4) (bound : NatPolynomial) (input : Nat) :
    (BuilderRequestRegisterMatch.rawTimePolynomial code bound).eval input + 6 ≤ (tagRawPolynomial bound).eval input := by
  simp only [tagRawPolynomial, BuilderRequestRegisterMatch.rawTimePolynomial,
    NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  omega

private theorem tag_through {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (bound : NatPolynomial) (input code : Nat) (hCode : code ≤ 4)
    (hSpan : (registerWord (requestValues slot request older)).length ≤ bound.eval input) :
    Through (requestValues slot request older) inside (.node (tagRef code))
      (if tag slot = code then tagTarget code else if code < 4 then .node (tagRef (code + 1)) else .dead)
      ((tagRawPolynomial bound).eval input) := by
  have h := guard_through (tagNode code) 11 code (tag slot) (tagPrefix slot older) (tagSuffix request)
    (requestValues slot request older) inside bound input (tag_mem code hCode) rfl
    (tag_operand_layout slot request older) (tag_offset request) hSpan
  have h' := through_mono h (tag_raw_mono code hCode bound input)
  exact h'

private theorem index_through {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat) (kind : Family)
    (hSpan : (registerWord (requestValues slot request older)).length ≤ bound.eval input) :
    Through (requestValues slot request older) inside (.node (indexNode kind).reference)
      (if request.clauseIndex = 0 then .node (bodyNode kind).reference
        else if kind = .positive then .node exclusionNode.reference else .dead)
      ((indexRawPolynomial bound).eval input) := by
  exact guard_through (indexNode kind) 1 0 request.clauseIndex (indexPrefix slot request older) [request.originalPosition]
    (requestValues slot request older) inside bound input (index_mem kind) rfl
    (index_operand_layout slot request older) rfl hSpan

private theorem graph_entry : graph.entry = tagRef 0 := rfl

private theorem dispatch_through {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (requestValues slot request older)).length ≤ bound.eval input) :
    Through (requestValues slot request older) inside (.node graph.entry) (entry (route slot request.clauseIndex))
      ((rawTimePolynomial bound).eval input) := by
  rw [graph_entry]
  have h0 := tag_through slot request older inside bound input 0 (by decide) hSpan
  have h1 := tag_through slot request older inside bound input 1 (by decide) hSpan
  have h2 := tag_through slot request older inside bound input 2 (by decide) hSpan
  have h3 := tag_through slot request older inside bound input 3 (by decide) hSpan
  have h4 := tag_through slot request older inside bound input 4 (by decide) hSpan
  have hiRequired := index_through slot request older inside bound input .required hSpan
  have hiImplication := index_through slot request older inside bound input .implication hSpan
  have hiPositive := index_through slot request older inside bound input .positive hSpan
  cases slot with
  | none =>
      simp only [tag, Nat.reduceLT, ite_true, ite_false, tagTarget] at h0
      apply through_mono h0
      simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
      omega
  | some item =>
      cases item with
      | none =>
          simp only [tag, Nat.reduceLT, ite_true, ite_false, tagTarget] at h0 h1
          apply through_mono (through_trans h0 h1)
          simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
          omega
      | some constraint =>
          cases constraint with
          | require literal =>
              simp only [tag, Nat.reduceLT, ite_true, ite_false, tagTarget] at h0 h1 h2
              have h := through_trans (through_trans (through_trans h0 h1) h2) hiRequired
              have hBound : (tagRawPolynomial bound).eval input + (tagRawPolynomial bound).eval input +
                  (tagRawPolynomial bound).eval input + (indexRawPolynomial bound).eval input ≤
                  (rawTimePolynomial bound).eval input := by
                simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
                omega
              have h' := through_mono h hBound
              by_cases hZero : request.clauseIndex = 0 <;>
                simpa only [route, hZero, ite_true, ite_false, reduceCtorEq, entry] using h'
          | implication premises conclusion =>
              simp only [tag, Nat.reduceLT, ite_true, ite_false, tagTarget] at h0 h1 h2 h3
              have h := through_trans (through_trans (through_trans (through_trans h0 h1) h2) h3) hiImplication
              have hBound : (tagRawPolynomial bound).eval input + (tagRawPolynomial bound).eval input +
                  (tagRawPolynomial bound).eval input + (tagRawPolynomial bound).eval input +
                  (indexRawPolynomial bound).eval input ≤ (rawTimePolynomial bound).eval input := by
                simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
                omega
              have h' := through_mono h hBound
              by_cases hZero : request.clauseIndex = 0 <;>
                simpa only [route, hZero, ite_true, ite_false, reduceCtorEq, entry] using h'
          | exactlyOne variables =>
              simp only [tag, Nat.reduceLT, ite_true, ite_false, tagTarget] at h0 h1 h2 h3 h4
              have h := through_trans (through_trans (through_trans (through_trans (through_trans h0 h1) h2) h3) h4) hiPositive
              have hBound : (tagRawPolynomial bound).eval input + (tagRawPolynomial bound).eval input +
                  (tagRawPolynomial bound).eval input + (tagRawPolynomial bound).eval input +
                  (tagRawPolynomial bound).eval input + (indexRawPolynomial bound).eval input ≤
                  (rawTimePolynomial bound).eval input := by
                simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
                omega
              have h' := through_mono h hBound
              by_cases hZero : request.clauseIndex = 0 <;>
                simpa only [route, hZero, ite_true, ite_false, entry] using h'

def initialConfiguration {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (requestValues slot request older) inside outside)

private theorem initial_projection (tape : WorkTape) :
    endpointConfiguration (.node graph.entry) tape = workStartConfiguration machine tape := rfl

/-- Every canonical original source/request reaches the actual program selected
by its physical tag and clause index. No branch or dispatch witness is supplied. -/
theorem workRun_request_dispatch {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (final : WorkTape),
      workRunExact? machine steps (initialConfiguration slot request older inside outside) =
        some (endpointConfiguration (entry (route slot request.clauseIndex)) final) ∧
      WorkTape.BlankEquivalent final (endTape (requestValues slot request older) inside []) ∧
      BuilderRequestedPairLookup.storedCells final ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  have hThrough := dispatch_through slot request older inside bound input (by omega)
  obtain ⟨steps, final, hPath, hFinal, hTime⟩ := hThrough
    (endTape (requestValues slot request older) inside outside)
    (BuilderRequestedPairLookup.endTape_blankEquivalent _ inside outside hBlank)
  have hRun := WorkMachineProgramPath.runExact graph _ _ steps _ _ graph_wellFormed hPath
  rw [initial_projection] at hRun
  have hStored := BuilderRequestedPairLookup.workRun_storedCells machine steps _ _ hRun
  refine ⟨steps, final, hRun, hFinal, ?_, hTime⟩
  simp only [endpointConfiguration, BuilderRequestedPairLookup.storedCells, workStartConfiguration,
    endTape, List.length_append, List.length_reverse] at hStored
  simp only [spanPolynomial, NatPolynomial.eval_add, BuilderRequestedPairLookup.storedCells]
  omega

theorem uniform_polynomial_dispatch {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ (rawSteps : Nat) (final : WorkTape),
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps (encodeWorkConfiguration (initialConfiguration slot request older inside outside)) =
        encodeWorkConfiguration (endpointConfiguration (entry (route slot request.clauseIndex)) final) ∧
      WorkTape.BlankEquivalent final (endTape (requestValues slot request older) inside []) ∧
      BuilderRequestedPairLookup.storedCells final ≤ inside.length + (spanPolynomial bound).eval input := by
  obtain ⟨steps, final, hRun, hFinal, hSpace, hTime⟩ :=
    workRun_request_dispatch slot request older inside outside bound input hBlank hSpan
  exact ⟨6 * steps, final, hTime, run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun, hFinal, hSpace⟩

end PNP.Concrete.CookLevin.BuilderRequestDispatch
