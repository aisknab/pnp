/-
Copyright (c) 2026 PNP Labs.

Complete token execution through the actual source/request dispatch graph.
The selected program, execution and stable result are derived from the original
request. Missing sources, padding and a valid false token are not conflated.
The original request and a polynomially bounded blank canonical frame survive
every outcome. Raw execution time and actual finite tape storage remain bounded
from the original frame. Cursor-root propagation, physical recovery and the
complete formula-builder loop remain downstream obligations.
-/
import PNP.Concrete.CookLevinBuilderRequestDispatch
import PNP.Concrete.CookLevinBuilderExclusionTokenRecoveryFrame
import PNP.Concrete.CNFWorkFrameCorrectness

namespace PNP.Concrete.CookLevin.BuilderRequestTokenLookup

open BuilderUnaryPolynomial (registerWord)
open BuilderPayloadSourceSearchBlank (BlankOutside blank_nil)
open BuilderDividerOperands (endTape)
open BuilderLocalConstraintPayload (Slot)
open BuilderPayloadSearchSource (Family Request family body)
open BuilderRequestDispatch (graph machine bodyNode exclusionNode absentNode requestValues initialConfiguration)
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration endpointState nodeState)
open PipelineStateNamespace (renameConfiguration)

def missingState : Nat := absentNode.encode absentNode.program.startState
def separatorState (state : Nat) : Prop :=
  state = (bodyNode .required).encode BuilderPayloadBodyTokenLookup.separatorState ∨
  state = (bodyNode .implication).encode BuilderPayloadBodyTokenLookup.separatorState ∨
  state = (bodyNode .positive).encode BuilderPayloadBodyTokenLookup.separatorState ∨
  state = exclusionNode.encode BuilderRequestedExclusionTokenLookup.separatorState
def finishState (state : Nat) : Prop :=
  state = (bodyNode .required).encode BuilderPayloadBodyTokenLookup.finishState ∨
  state = (bodyNode .implication).encode BuilderPayloadBodyTokenLookup.finishState ∨
  state = (bodyNode .positive).encode BuilderPayloadBodyTokenLookup.finishState ∨
  state = exclusionNode.encode BuilderRequestedExclusionTokenLookup.finishState
instance (state : Nat) : Decidable (separatorState state) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
instance (state : Nat) : Decidable (finishState state) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- Outer absence means no source; inner absence means no token at this request. -/
def observe (configuration : WorkConfiguration) : Option (Option CNFToken) :=
  if configuration.state = 0 then some (some .t)
  else if configuration.state = 1 then some (some .f)
  else if configuration.state = missingState then none
  else if separatorState configuration.state then some (some .sep)
  else if finishState configuration.state then some (some .finish) else some none

def canonicalResult {width : Nat} (slot : Slot width) (request : Request) : Option (Option CNFToken) :=
  slot.map (fun source => source.bind (fun constraint =>
    (constraint.emit[request.clauseIndex]?).bind
      (fun clause => (encodeClauseTokens (BoundedClause.emit clause))[request.originalPosition]?)))

def finishConfiguration (node : Node) (configuration : WorkConfiguration) : WorkConfiguration :=
  if configuration.state = node.program.acceptState then endpointConfiguration node.onAccept configuration.tape
  else if configuration.state = node.program.rejectState then endpointConfiguration node.onReject configuration.tape
  else renameConfiguration node.encode configuration
def finishSteps (node : Node) (configuration : WorkConfiguration) : Nat :=
  if configuration.state = node.program.acceptState then 1
  else if configuration.state = node.program.rejectState then 1 else 0

theorem finish_tape (node : Node) (configuration : WorkConfiguration) :
    (finishConfiguration node configuration).tape = configuration.tape := by
  unfold finishConfiguration
  split
  · rfl
  · split <;> rfl

private theorem node_state_eq_iff (a b s t : Nat) :
    nodeState a s = nodeState b t ↔ a = b ∧ s = t :=
  ⟨WorkMachineProgramGraph.nodeState_injective, fun ⟨hName,hState⟩ => by rw [hName,hState]⟩

private theorem node_not_global (name state : Nat) :
    nodeState name state ≠ 0 ∧ nodeState name state ≠ 1 ∧ nodeState name state ≠ 2 := by
  have h := WorkMachineProgramGraph.nodeState_ge_three name state
  refine ⟨?_,?_,?_⟩
  · intro hZero; omega
  · intro hOne; omega
  · intro hTwo; omega

theorem observe_true (tape : WorkTape) : observe {state := 0, tape := tape} = some (some .t) := rfl
theorem observe_false (tape : WorkTape) : observe {state := 1, tape := tape} = some (some .f) := rfl
theorem observe_missing (tape : WorkTape) : observe {state := missingState, tape := tape} = none := by
  have h := node_not_global absentNode.name absentNode.program.startState
  simp only [observe, missingState, Node.encode, if_neg h.1, if_neg h.2.1, ite_true]
theorem observe_padding (tape : WorkTape) : observe {state := 2, tape := tape} = some none := by
  have hMissing := (node_not_global absentNode.name absentNode.program.startState).2.2
  have hBody (kind : Family) (state : Nat) := (node_not_global (bodyNode kind).name state).2.2
  have hExclusion (state : Nat) := (node_not_global exclusionNode.name state).2.2
  simp [observe, missingState, separatorState, finishState, Node.encode,
    Ne.symm hMissing, fun kind state => Ne.symm (hBody kind state), fun state => Ne.symm (hExclusion state)]

private theorem body_name (kind : Family) :
    (bodyNode kind).name = (match kind with | .required => 8 | .implication => 9 | .positive => 10) := rfl
private theorem absent_name : absentNode.name = 12 := rfl
private theorem exclusion_name : exclusionNode.name = 11 := rfl
private theorem graph_machine : WorkMachineProgramGraph.machine graph = machine := rfl

private theorem observe_body_local (kind : Family) (configuration : WorkConfiguration) :
    observe (renameConfiguration (bodyNode kind).encode configuration) =
      some (if configuration.state = BuilderPayloadBodyTokenLookup.separatorState then some .sep
        else if configuration.state = BuilderPayloadBodyTokenLookup.finishState then some .finish else none) := by
  have h := node_not_global (bodyNode kind).name configuration.state
  have hName : (bodyNode kind).name ≠ absentNode.name := by
    rw [body_name,absent_name]
    cases kind <;> decide
  have hMissing := WorkMachineProgramGraph.nodeState_ne_of_name_ne hName configuration.state absentNode.program.startState
  have hSeparator : separatorState (nodeState (bodyNode kind).name configuration.state) ↔
      configuration.state = BuilderPayloadBodyTokenLookup.separatorState := by
    simp only [separatorState,Node.encode,node_state_eq_iff,body_name,exclusion_name]
    cases kind <;> simp
  have hFinish : finishState (nodeState (bodyNode kind).name configuration.state) ↔
      configuration.state = BuilderPayloadBodyTokenLookup.finishState := by
    simp only [finishState,Node.encode,node_state_eq_iff,body_name,exclusion_name]
    cases kind <;> simp
  simp only [observe,renameConfiguration,Node.encode,if_neg h.1,if_neg h.2.1,
    missingState,if_neg hMissing,hSeparator,hFinish]
  by_cases hS : configuration.state = BuilderPayloadBodyTokenLookup.separatorState
  · simp only [if_pos hS]
  · simp only [if_neg hS]
    by_cases hF : configuration.state = BuilderPayloadBodyTokenLookup.finishState
    · simp only [if_pos hF]
    · simp only [if_neg hF]

private theorem observe_exclusion_local (configuration : WorkConfiguration) :
    observe (renameConfiguration exclusionNode.encode configuration) =
      some (if configuration.state = BuilderRequestedExclusionTokenLookup.separatorState then some .sep
        else if configuration.state = BuilderRequestedExclusionTokenLookup.finishState then some .finish else none) := by
  have h := node_not_global exclusionNode.name configuration.state
  have hName : exclusionNode.name ≠ absentNode.name := by rw [exclusion_name,absent_name]; decide
  have hMissing := WorkMachineProgramGraph.nodeState_ne_of_name_ne hName configuration.state absentNode.program.startState
  have hSeparator : separatorState (nodeState exclusionNode.name configuration.state) ↔
      configuration.state = BuilderRequestedExclusionTokenLookup.separatorState := by
    simp only [separatorState,Node.encode,node_state_eq_iff,body_name,exclusion_name]
    simp
  have hFinish : finishState (nodeState exclusionNode.name configuration.state) ↔
      configuration.state = BuilderRequestedExclusionTokenLookup.finishState := by
    simp only [finishState,Node.encode,node_state_eq_iff,body_name,exclusion_name]
    simp
  simp only [observe,renameConfiguration,Node.encode,if_neg h.1,if_neg h.2.1,
    missingState,if_neg hMissing,hSeparator,hFinish]
  by_cases hS : configuration.state = BuilderRequestedExclusionTokenLookup.separatorState
  · simp only [if_pos hS]
  · simp only [if_neg hS]
    by_cases hF : configuration.state = BuilderRequestedExclusionTokenLookup.finishState
    · simp only [if_pos hF]
    · simp only [if_neg hF]

private theorem body_accept (kind : Family) :
    (bodyNode kind).program.acceptState = BuilderPayloadBodyTokenLookup.trueState := rfl
private theorem body_reject (kind : Family) :
    (bodyNode kind).program.rejectState = BuilderPayloadBodyTokenLookup.falseState := rfl
private theorem exclusion_accept : exclusionNode.program.acceptState = BuilderRequestedExclusionTokenLookup.trueState := rfl
private theorem exclusion_reject : exclusionNode.program.rejectState = BuilderRequestedExclusionTokenLookup.falseState := rfl
private theorem body_onAccept (kind : Family) : (bodyNode kind).onAccept = .accept := rfl
private theorem body_onReject (kind : Family) : (bodyNode kind).onReject = .reject := rfl
private theorem exclusion_onAccept : exclusionNode.onAccept = .accept := rfl
private theorem exclusion_onReject : exclusionNode.onReject = .reject := rfl

theorem observe_body_finished (kind : Family) (configuration : WorkConfiguration) :
    observe (finishConfiguration (bodyNode kind) configuration) = some (BuilderPayloadBodyTokenLookup.observe configuration) := by
  unfold finishConfiguration
  rw [body_accept, body_reject, body_onAccept, body_onReject]
  by_cases hA : configuration.state = BuilderPayloadBodyTokenLookup.trueState
  · simp only [if_pos hA, endpointConfiguration, endpointState, WorkMachineProgramGraph.globalAcceptState,
      observe_true, BuilderPayloadBodyTokenLookup.observe]
  · rw [if_neg hA]
    by_cases hR : configuration.state = BuilderPayloadBodyTokenLookup.falseState
    · simp only [if_pos hR, endpointConfiguration, endpointState, WorkMachineProgramGraph.globalRejectState,
        observe_false, BuilderPayloadBodyTokenLookup.observe, if_neg hA]
    · rw [if_neg hR, observe_body_local]
      simp only [BuilderPayloadBodyTokenLookup.observe, if_neg hA, if_neg hR]

theorem observe_exclusion_finished (configuration : WorkConfiguration) :
    observe (finishConfiguration exclusionNode configuration) = some (BuilderRequestedExclusionTokenLookup.observe configuration) := by
  unfold finishConfiguration
  rw [exclusion_accept, exclusion_reject, exclusion_onAccept, exclusion_onReject]
  by_cases hA : configuration.state = BuilderRequestedExclusionTokenLookup.trueState
  · simp only [if_pos hA, endpointConfiguration, endpointState, WorkMachineProgramGraph.globalAcceptState,
      observe_true, BuilderRequestedExclusionTokenLookup.observe]
  · rw [if_neg hA]
    by_cases hR : configuration.state = BuilderRequestedExclusionTokenLookup.falseState
    · simp only [if_pos hR, endpointConfiguration, endpointState, WorkMachineProgramGraph.globalRejectState,
        observe_false, BuilderRequestedExclusionTokenLookup.observe, if_neg hA]
    · rw [if_neg hR, observe_exclusion_local]
      simp only [BuilderRequestedExclusionTokenLookup.observe, if_neg hA, if_neg hR]

theorem observe_blankEquivalent {actual canonical : WorkConfiguration}
    (hEquivalent : WorkConfiguration.BlankEquivalent actual canonical) :
    observe actual = observe canonical := by
  simp only [observe, hEquivalent.state]

private theorem body_mem (kind : Family) : bodyNode kind ∈ graph.nodes := by
  cases kind with
  | required => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
  | implication => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  | positive => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))
private theorem exclusion_mem : exclusionNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
private theorem absent_mem : absentNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))

private theorem equal_node_of_name {nodes : List Node}
    (hNames : nodes.Pairwise (fun a b => a.name ≠ b.name)) {a b : Node}
    (hA : a ∈ nodes) (hB : b ∈ nodes) (hEq : a.name = b.name) : a = b := by
  induction nodes with
  | nil => cases hA
  | cons head rest ih =>
      obtain ⟨hHead,hTail⟩ := List.pairwise_cons.mp hNames
      rcases List.mem_cons.mp hA with hA | hA
      · subst a
        rcases List.mem_cons.mp hB with hB | hB
        · exact hB.symm
        · exact False.elim (hHead b hB hEq)
      · rcases List.mem_cons.mp hB with hB | hB
        · subst b
          exact False.elim (hHead a hA hEq.symm)
        · exact ih hTail hA hB

private theorem bridge_source {source target : Nat} {rule : WorkRule}
    (hMem : rule ∈ PipelineStageBridges.launchRules source target) : rule.sourceState = source := by
  rcases List.mem_map.mp hMem with ⟨symbol,_,rfl⟩
  rfl
private theorem node_rule_source {node : Node} {rule : WorkRule} (hMem : rule ∈ node.rules) :
    ∃ state, rule.sourceState = node.encode state := by
  simp only [Node.rules, List.mem_append] at hMem
  rcases hMem with hA | hR | hL
  · exact ⟨node.program.acceptState,bridge_source hA⟩
  · exact ⟨node.program.rejectState,bridge_source hR⟩
  · rcases List.mem_map.mp hL with ⟨localRule,_,rfl⟩
    exact ⟨localRule.sourceState,rfl⟩

private theorem custom_no_rule (node : Node) (state : Nat) (hMem : node ∈ graph.nodes)
    (hA : state ≠ node.program.acceptState) (hR : state ≠ node.program.rejectState)
    (hNo : WorkMachineProgramGraph.NoRuleAt node.program state) :
    WorkMachineProgramGraph.NoRuleAt machine (node.encode state) := by
  intro rule hRule hState
  rcases List.mem_flatMap.mp hRule with ⟨other,hOther,hLocal⟩
  obtain ⟨localState,hSource⟩ := node_rule_source hLocal
  have hNames := (WorkMachineProgramGraph.nodeState_injective (hSource.symm.trans hState)).1
  have hSame := equal_node_of_name BuilderRequestDispatch.graph_wellFormed.1 hOther hMem hNames
  subst other
  simp only [Node.rules, List.mem_append] at hLocal
  rcases hLocal with hAccept | hReject | hRule
  · exact hA (node.encode_injective ((bridge_source hAccept).symm.trans hState)).symm
  · exact hR (node.encode_injective ((bridge_source hReject).symm.trans hState)).symm
  · rcases List.mem_map.mp hRule with ⟨localRule,hLocalRule,rfl⟩
    exact hNo localRule hLocalRule (node.encode_injective hState)

theorem missing_no_rule : WorkMachineProgramGraph.NoRuleAt machine missingState := by
  apply custom_no_rule absentNode absentNode.program.startState absent_mem
  · change (2 : Nat) ≠ 0; decide
  · change (2 : Nat) ≠ 1; decide
  · intro rule h; cases h

theorem finish_steps_le_one (node : Node) (configuration : WorkConfiguration) : finishSteps node configuration ≤ 1 := by
  unfold finishSteps
  split <;> (try split) <;> omega

private theorem configuration_state (configuration : WorkConfiguration) (state : Nat)
    (hState : configuration.state = state) : configuration = {state := state,tape := configuration.tape} := by
  cases configuration
  cases hState
  rfl

theorem workRun_finish (node : Node) (configuration : WorkConfiguration) (hMem : node ∈ graph.nodes) :
    workRunExact? machine (finishSteps node configuration) (renameConfiguration node.encode configuration) =
      some (finishConfiguration node configuration) := by
  unfold finishSteps finishConfiguration
  by_cases hA : configuration.state = node.program.acceptState
  · rw [if_pos hA, if_pos hA]
    have hStep : workStep? machine (renameConfiguration node.encode {state := node.program.acceptState,tape := configuration.tape}) =
        some (endpointConfiguration node.onAccept configuration.tape) :=
      WorkMachineProgramGraph.accept_bridge_step graph node configuration.tape BuilderRequestDispatch.graph_wellFormed hMem
    rw [configuration_state configuration _ hA]
    simp only [workRunExact?,hStep]
  · rw [if_neg hA, if_neg hA]
    by_cases hR : configuration.state = node.program.rejectState
    · rw [if_pos hR, if_pos hR]
      have hStep : workStep? machine (renameConfiguration node.encode {state := node.program.rejectState,tape := configuration.tape}) =
          some (endpointConfiguration node.onReject configuration.tape) :=
        WorkMachineProgramGraph.reject_bridge_step graph node configuration.tape BuilderRequestDispatch.graph_wellFormed hMem
      rw [configuration_state configuration _ hR]
      simp only [workRunExact?,hStep]
    · rw [if_neg hR, if_neg hR]
      rfl

private theorem finish_no_rule (node : Node) (configuration : WorkConfiguration) (hMem : node ∈ graph.nodes)
    (hAccept : node.onAccept = .accept) (hReject : node.onReject = .reject)
    (hNo : WorkMachineProgramGraph.NoRuleAt node.program configuration.state) :
    WorkMachineProgramGraph.NoRuleAt machine (finishConfiguration node configuration).state := by
  unfold finishConfiguration
  split
  · rw [hAccept]
    exact WorkMachineProgramGraph.noRuleAt_globalAccept graph
  · split
    · rw [hReject]
      exact WorkMachineProgramGraph.noRuleAt_globalReject graph
    · exact custom_no_rule node configuration.state hMem ‹_› ‹_› hNo

private theorem body_final_no_rule {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (values : List Nat) (inside outside : List WorkSymbol) :
    WorkMachineProgramGraph.NoRuleAt (BuilderPayloadBodyTokenLookup.machine (family constraint))
      (BuilderPayloadBodyTokenLookup.finalConfiguration constraint request values inside outside).state := by
  let literals := body constraint
  let position := request.originalPosition
  have hCases : BuilderLiteralClauseTokenSelector.endpoint literals position =
        .node BuilderLiteralClauseTokenSelector.trueReference ∨
      BuilderLiteralClauseTokenSelector.endpoint literals position = .reject ∨
      BuilderLiteralClauseTokenSelector.endpoint literals position = .dead ∨
      BuilderLiteralClauseTokenSelector.endpoint literals position =
        .node BuilderLiteralClauseTokenSelector.separatorNode.reference ∨
      BuilderLiteralClauseTokenSelector.endpoint literals position =
        .node BuilderLiteralClauseTokenSelector.finishNode.reference := by
    unfold BuilderLiteralClauseTokenSelector.endpoint
    by_cases hZero : position = 0
    · rw [if_pos hZero]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [if_neg hZero]
      unfold BuilderLiteralClauseTokenSelector.afterEndpoint
      by_cases hBody : position - 1 < DirectToken.boundedLiteralListWidth literals
      · rw [if_pos hBody]
        unfold BuilderLiteralClauseTokenSelector.bodyEndpoint
        cases BuilderLiteralListSearch.endpoint literals (position - 1) <;> simp
      · rw [if_neg hBody]
        split <;> simp
  change WorkMachineProgramGraph.NoRuleAt (BuilderPayloadBodyTokenLookup.machine (family constraint))
    (WorkMachineChain.secondState (endpointState (BuilderLiteralClauseTokenSelector.endpoint literals position)))
  rcases hCases with h | h | h | h | h
  · rw [h]; exact BuilderPayloadBodyTokenLookup.noRuleAtAccept (family constraint)
  · rw [h]; exact BuilderPayloadBodyTokenLookup.noRuleAtReject (family constraint)
  · rw [h]; exact BuilderPayloadBodyTokenLookup.noRuleAtPadding (family constraint)
  · rw [h]; exact BuilderPayloadBodyTokenLookup.noRuleAtSeparator (family constraint)
  · rw [h]; exact BuilderPayloadBodyTokenLookup.noRuleAtFinish (family constraint)

private theorem node_entry_projection (node : Node) (tape : WorkTape) :
    renameConfiguration node.encode (workStartConfiguration node.program tape) =
      endpointConfiguration (.node node.reference) tape := rfl

private theorem node_complete (node : Node) (steps : Nat) (word : List Nat) (inside : List WorkSymbol)
    (canonicalFinal : WorkConfiguration) (actualTape : WorkTape) (hMem : node ∈ graph.nodes)
    (hTape : WorkTape.BlankEquivalent actualTape (endTape word inside []))
    (hRun : workRunExact? node.program steps (workStartConfiguration node.program (endTape word inside [])) = some canonicalFinal) :
    ∃ final,
      workRunExact? machine (steps + finishSteps node canonicalFinal) (endpointConfiguration (.node node.reference) actualTape) = some final ∧
      WorkConfiguration.BlankEquivalent final (finishConfiguration node canonicalFinal) := by
  have hLocal := WorkMachineProgramGraph.local_workRunExact graph node steps _ _ BuilderRequestDispatch.graph_wellFormed hMem hRun
  rw [graph_machine,node_entry_projection] at hLocal
  have hFinish := workRun_finish node canonicalFinal hMem
  have hCombined := workRunExact?_add_of_exact machine steps (finishSteps node canonicalFinal) _ _ _ hLocal hFinish
  have hInitial : WorkConfiguration.BlankEquivalent
      (endpointConfiguration (.node node.reference) actualTape)
      (endpointConfiguration (.node node.reference) (endTape word inside [])) := ⟨rfl,hTape⟩
  exact PNP.Concrete.workRunExact?_transport machine _ hInitial hCombined

def selectedRawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderPayloadBodyTokenLookup.rawTimePolynomial bound)
    (BuilderRequestedExclusionTokenLookup.rawTimePolynomial bound)) (.constant 6)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRequestDispatch.rawTimePolynomial bound) (selectedRawTimePolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add bound (rawTimePolynomial bound)

def canonicalSpanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add bound (.add (BuilderPayloadBodyTokenLookup.spanPolynomial bound)
    (BuilderExclusionTokenRecoveryFrame.canonicalSpanPolynomial bound))

private theorem body_run {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (tape : WorkTape) (bound : NatPolynomial) (input : Nat)
    (hTape : WorkTape.BlankEquivalent tape (endTape (requestValues (some (some constraint)) request older) inside []))
    (hSpan : (registerWord (requestValues (some (some constraint)) request older)).length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      workRunExact? machine steps (endpointConfiguration (.node (bodyNode (family constraint)).reference) tape) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = some ((encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]?) ∧
      (∃ scratch, values = requestValues (some (some constraint)) request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      6 * steps ≤ (selectedRawTimePolynomial bound).eval input := by
  rw [BuilderRequestDispatch.request_values_present] at hTape hSpan
  obtain ⟨steps, values, outside, hRun, hObserve, hRetained, hCanonical, hTime, hBlank⟩ :=
    BuilderPayloadBodyTokenLookup.workRun_polynomial_lookup_with_blank constraint request older inside [] bound input (by
      simpa only [List.length_nil, Nat.add_zero] using hSpan)
  let child := BuilderPayloadBodyTokenLookup.finalConfiguration constraint request values inside outside
  obtain ⟨final, hComplete, hEquivalent⟩ :=
    node_complete (bodyNode (family constraint)) steps _ inside child tape (body_mem _) hTape hRun
  have hNo := finish_no_rule (bodyNode (family constraint)) child (body_mem _) rfl rfl
    (body_final_no_rule constraint request values inside outside)
  refine ⟨steps + finishSteps (bodyNode (family constraint)) child, values, outside, final,
    hComplete, ?_, ?_, ?_, ?_, hBlank blank_nil, ?_, ?_⟩
  · rw [hEquivalent.state]
    exact hNo
  · rw [observe_blankEquivalent hEquivalent, observe_body_finished]
    exact congrArg some hObserve
  · rw [BuilderRequestDispatch.request_values_present]
    exact hRetained
  · have hFinalTape := hEquivalent.tape
    rw [finish_tape] at hFinalTape
    exact hFinalTape
  · simp only [canonicalSpanPolynomial, NatPolynomial.eval_add]
    omega
  · have hBridge := finish_steps_le_one (bodyNode (family constraint)) child
    simp only [selectedRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

private theorem exclusion_run {width : Nat} (variables : List (Fin width)) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (tape : WorkTape) (bound : NatPolynomial) (input : Nat)
    (hPositive : 0 < request.clauseIndex)
    (hTape : WorkTape.BlankEquivalent tape (endTape (requestValues (some (some (.exactlyOne variables))) request older) inside []))
    (hSpan : (registerWord (requestValues (some (some (.exactlyOne variables))) request older)).length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      workRunExact? machine steps (endpointConfiguration (.node exclusionNode.reference) tape) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = some (BuilderRequestedExclusionTokenLookup.canonicalToken variables request) ∧
      (∃ scratch, values = requestValues (some (some (.exactlyOne variables))) request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      6 * steps ≤ (selectedRawTimePolynomial bound).eval input := by
  rw [BuilderRequestDispatch.request_values_present] at hTape hSpan
  change WorkTape.BlankEquivalent tape (endTape (BuilderRequestedPairLookup.initialValues variables request older) inside []) at hTape
  change (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length ≤ bound.eval input at hSpan
  have hBlank : BuilderRequestedPairLookup.BlankExterior ([] : List WorkSymbol) :=
    BuilderRequestedPairLookup.blankExterior_replicate 0
  have hInputSpan : (registerWord (BuilderRequestedPairLookup.initialValues variables request older)).length +
      ([] : List WorkSymbol).length ≤ bound.eval input := by
    simpa only [List.length_nil, Nat.add_zero] using hSpan
  obtain ⟨steps, values, outside, child, hRun, hNo, hObserve, hRetained, hFrame, hBlankFinal, hCanonical, _, hTime⟩ :=
    BuilderExclusionTokenRecoveryFrame.workRun_polynomial_lookup_with_frame
      variables request older inside [] bound input hPositive hBlank hInputSpan
  obtain ⟨final, hComplete, hEquivalent⟩ := node_complete exclusionNode steps _ inside child tape exclusion_mem hTape hRun
  have hTerminal := finish_no_rule exclusionNode child exclusion_mem rfl rfl hNo
  refine ⟨steps + finishSteps exclusionNode child, values, outside, final,
    hComplete, ?_, ?_, ?_, ?_, hBlankFinal, ?_, ?_⟩
  · rw [hEquivalent.state]
    exact hTerminal
  · rw [observe_blankEquivalent hEquivalent, observe_exclusion_finished]
    exact congrArg some hObserve
  · rw [BuilderRequestDispatch.request_values_present]
    exact hRetained
  · have hFinalTape := hEquivalent.tape
    rw [finish_tape] at hFinalTape
    exact WorkTape.blankEquivalent_trans hFinalTape hFrame
  · simp only [canonicalSpanPolynomial, NatPolynomial.eval_add]
    omega
  · have hBridge := finish_steps_le_one exclusionNode child
    simp only [selectedRawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem canonical_body {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (hZero : request.clauseIndex = 0) :
    canonicalResult (some (some constraint)) request =
      some ((encodeClauseTokens (BoundedClause.emit (body constraint)))[request.originalPosition]?) := by
  simp only [canonicalResult,Option.map_some,Option.bind_some,hZero,BuilderPayloadSearchSource.body_first_clause]

theorem canonical_exclusion {width : Nat} (variables : List (Fin width)) (request : Request) :
    canonicalResult (some (some (.exactlyOne variables))) request =
      some (BuilderRequestedExclusionTokenLookup.canonicalToken variables request) := by
  rw [BuilderRequestedExclusionTokenLookup.canonicalToken_eq_emit]
  rfl

private theorem padding_run {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (tape : WorkTape) (bound : NatPolynomial) (input : Nat)
    (hTape : WorkTape.BlankEquivalent tape (endTape (requestValues slot request older) inside []))
    (hSpan : (registerWord (requestValues slot request older)).length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      workRunExact? machine steps (endpointConfiguration .dead tape) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧ observe final = some none ∧
      (∃ scratch, values = requestValues slot request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      6 * steps ≤ (selectedRawTimePolynomial bound).eval input := by
  refine ⟨0, requestValues slot request older, [], endpointConfiguration .dead tape, rfl,
    WorkMachineProgramGraph.noRuleAt_globalDead graph, observe_padding tape,
    ⟨[], (List.append_nil _).symm⟩, hTape, blank_nil, ?_, Nat.zero_le _⟩
  simp only [List.length_nil, Nat.add_zero, canonicalSpanPolynomial, NatPolynomial.eval_add]
  omega

/-- Complete dispatch retains the actual request frame for every source kind,
including absence, padding, body clauses and valid or invalid exclusions. -/
theorem workRun_from_dispatch_with_frame {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (tape : WorkTape) (bound : NatPolynomial) (input : Nat)
    (hTape : WorkTape.BlankEquivalent tape (endTape (requestValues slot request older) inside []))
    (hSpan : (registerWord (requestValues slot request older)).length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      workRunExact? machine steps
        (endpointConfiguration (BuilderRequestDispatch.entry (BuilderRequestDispatch.route slot request.clauseIndex)) tape) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      (∃ scratch, values = requestValues slot request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      6 * steps ≤ (selectedRawTimePolynomial bound).eval input := by
  cases slot with
  | none =>
      refine ⟨0, requestValues none request older, [], endpointConfiguration (.node absentNode.reference) tape,
        rfl, missing_no_rule, observe_missing tape, ⟨[], (List.append_nil _).symm⟩,
        hTape, blank_nil, ?_, Nat.zero_le _⟩
      simp only [List.length_nil, Nat.add_zero, canonicalSpanPolynomial, NatPolynomial.eval_add]
      omega
  | some source =>
      cases source with
      | none => exact padding_run (some none) request older inside tape bound input hTape hSpan
      | some constraint =>
          by_cases hZero : request.clauseIndex = 0
          · have hRun := body_run constraint request older inside tape bound input hTape hSpan
            rw [← canonical_body constraint request hZero] at hRun
            cases constraint <;> simpa only [BuilderRequestDispatch.route, hZero, ite_true, BuilderRequestDispatch.entry,
              BuilderPayloadSearchSource.family] using hRun
          · cases constraint with
            | require literal =>
                have hResult : canonicalResult (some (some (.require literal))) request = some none := by
                  cases hIndex : request.clauseIndex with
                  | zero => exact False.elim (hZero hIndex)
                  | succ index => simp [canonicalResult, LocalConstraint.emit, unitClauses, hIndex]
                simpa only [BuilderRequestDispatch.route, if_neg hZero, BuilderRequestDispatch.entry, hResult] using
                  padding_run (some (some (.require literal))) request older inside tape bound input hTape hSpan
            | implication premises conclusion =>
                have hResult : canonicalResult (some (some (.implication premises conclusion))) request = some none := by
                  cases hIndex : request.clauseIndex with
                  | zero => exact False.elim (hZero hIndex)
                  | succ index => simp [canonicalResult, LocalConstraint.emit, implicationClauses, hIndex]
                simpa only [BuilderRequestDispatch.route, if_neg hZero, BuilderRequestDispatch.entry, hResult] using
                  padding_run (some (some (.implication premises conclusion))) request older inside tape bound input hTape hSpan
            | exactlyOne variables =>
                have hRun := exclusion_run variables request older inside tape bound input (by omega) hTape hSpan
                rw [← canonical_exclusion variables request] at hRun
                simpa only [BuilderRequestDispatch.route, if_neg hZero, BuilderRequestDispatch.entry] using hRun

theorem workRun_from_dispatch {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside : List WorkSymbol) (tape : WorkTape) (bound : NatPolynomial) (input : Nat)
    (hTape : WorkTape.BlankEquivalent tape (endTape (requestValues slot request older) inside []))
    (hSpan : (registerWord (requestValues slot request older)).length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps
        (endpointConfiguration (BuilderRequestDispatch.entry (BuilderRequestDispatch.route slot request.clauseIndex)) tape) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      6 * steps ≤ (selectedRawTimePolynomial bound).eval input := by
  obtain ⟨steps, _, _, final, hRun, hNo, hObserve, _, _, _, _, hTime⟩ :=
    workRun_from_dispatch_with_frame slot request older inside tape bound input hTape hSpan
  exact ⟨steps, final, hRun, hNo, hObserve, hTime⟩

/-- Full actual-source execution derives its recoverable frame. No selected
program, retained-frame certificate or output token is a supplied premise. -/
theorem workRun_polynomial_lookup_with_frame {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ (steps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      workRunExact? machine steps (initialConfiguration slot request older inside outside) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      (∃ scratch, values = requestValues slot request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  obtain ⟨dispatchSteps, middle, hDispatch, hMiddle, _, hDispatchTime⟩ :=
    BuilderRequestDispatch.workRun_request_dispatch slot request older inside outside bound input hBlank hSpan
  obtain ⟨lookupSteps, values, resultOutside, final, hLookup, hNo, hObserve,
      hRetained, hFrame, hBlankFinal, hCanonical, hLookupTime⟩ :=
    workRun_from_dispatch_with_frame slot request older inside middle bound input hMiddle (by omega)
  have hRun := workRunExact?_add_of_exact machine dispatchSteps lookupSteps _ _ _ hDispatch hLookup
  have hTime : 6 * (dispatchSteps + lookupSteps) ≤ (rawTimePolynomial bound).eval input := by
    simp only [rawTimePolynomial, NatPolynomial.eval_add]
    omega
  refine ⟨dispatchSteps + lookupSteps, values, resultOutside, final, hRun, hNo, hObserve,
    hRetained, hFrame, hBlankFinal, hCanonical, ?_, hTime⟩
  have hCells := BuilderRequestedPairLookup.workRun_storedCells machine _ _ _ hRun
  simp only [BuilderRequestedPairLookup.storedCells, BuilderRequestDispatch.initialConfiguration, workStartConfiguration,
    endTape, List.length_append, List.length_reverse] at hCells ⊢
  simp only [spanPolynomial, NatPolynomial.eval_add]
  omega

theorem workRun_polynomial_lookup {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ steps final,
      workRunExact? machine steps (initialConfiguration slot request older inside outside) = some final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input ∧
      6 * steps ≤ (rawTimePolynomial bound).eval input := by
  obtain ⟨steps, _, _, final, hRun, hNo, hObserve, _, _, _, _, hSpace, hTime⟩ :=
    workRun_polynomial_lookup_with_frame slot request older inside outside bound input hBlank hSpan
  exact ⟨steps, final, hRun, hNo, hObserve, hSpace, hTime⟩

theorem uniform_polynomial_lookup {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps final,
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps (encodeWorkConfiguration (initialConfiguration slot request older inside outside)) =
        encodeWorkConfiguration final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  obtain ⟨steps,final,hRun,hNo,hObserve,hSpace,hTime⟩ :=
    workRun_polynomial_lookup slot request older inside outside bound input hBlank hSpan
  exact ⟨6 * steps,final,hTime,run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun,hNo,hObserve,hSpace⟩

theorem uniform_polynomial_lookup_with_frame {width : Nat} (slot : Slot width) (request : Request) (older : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hBlank : BuilderRequestedPairLookup.BlankExterior outside)
    (hSpan : (registerWord (requestValues slot request older)).length + outside.length ≤ bound.eval input) :
    ∃ (rawSteps : Nat) (values : List Nat) (resultOutside : List WorkSymbol) (final : WorkConfiguration),
      rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine machine) rawSteps (encodeWorkConfiguration (initialConfiguration slot request older inside outside)) =
        encodeWorkConfiguration final ∧
      WorkMachineProgramGraph.NoRuleAt machine final.state ∧
      observe final = canonicalResult slot request ∧
      (∃ scratch, values = requestValues slot request older ++ scratch) ∧
      WorkTape.BlankEquivalent final.tape (endTape values inside resultOutside) ∧
      BlankOutside resultOutside ∧
      (registerWord values).length + resultOutside.length ≤ (canonicalSpanPolynomial bound).eval input ∧
      BuilderRequestedPairLookup.storedCells final.tape ≤ inside.length + (spanPolynomial bound).eval input := by
  obtain ⟨steps, values, resultOutside, final, hRun, hNo, hObserve,
      hRetained, hFrame, hBlankFinal, hCanonical, hSpace, hTime⟩ :=
    workRun_polynomial_lookup_with_frame slot request older inside outside bound input hBlank hSpan
  exact ⟨6 * steps, values, resultOutside, final, hTime,
    run_compileWorkMachine_mul_of_workRunExact _ _ _ _ hRun,
    hNo, hObserve, hRetained, hFrame, hBlankFinal, hCanonical, hSpace⟩

end PNP.Concrete.CookLevin.BuilderRequestTokenLookup
