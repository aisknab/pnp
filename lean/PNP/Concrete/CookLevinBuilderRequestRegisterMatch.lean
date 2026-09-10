/-
Copyright (c) 2026 PNP Labs.

A fixed-offset request-register test with physical copy, comparison and erasure.
The tested value comes from the original register word, not a supplied branch
certificate. Both outcomes retain every source/request register and the inside
tape. Temporary cells are cleared; blank-equivalent workspaces compose without
pretending their finite exterior is empty. All work has an input-span bound.
-/
import PNP.Concrete.CookLevinBuilderUnaryTagMatch
import PNP.Concrete.CookLevinBuilderRegisterErase
import PNP.Concrete.CookLevinBuilderRequestedPairLookup

namespace PNP.Concrete.CookLevin.BuilderRequestRegisterMatch

open PipelineTape BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open WorkMachineProgramGraph (Node Graph Endpoint endpointConfiguration endpointState)
open WorkMachineProgramPath (AcceptPath LocalAcceptRun LocalRejectRun)

def eraseYesNode : Node :=
  {name := 2, program := BuilderRegisterErase.oneMachine, onAccept := .accept, onReject := .dead}
def eraseNoNode : Node :=
  {name := 3, program := BuilderRegisterErase.oneMachine, onAccept := .reject, onReject := .dead}
def testNode (expected : Nat) : Node :=
  {name := 1, program := BuilderUnaryTagMatch.machine expected,
   onAccept := .node eraseYesNode.reference, onReject := .node eraseNoNode.reference}
def copyNode (offset expected : Nat) : Node :=
  {name := 0, program := RegisterCopy.machine offset,
   onAccept := .node (testNode expected).reference, onReject := .dead}
def graph (offset expected : Nat) : Graph :=
  {nodes := [copyNode offset expected, testNode expected, eraseYesNode, eraseNoNode],
   entry := (copyNode offset expected).reference}
def machine (offset expected : Nat) : WorkMachine := WorkMachineProgramGraph.machine (graph offset expected)

private theorem copy_mem (offset expected : Nat) : copyNode offset expected ∈ (graph offset expected).nodes :=
  List.Mem.head _
private theorem test_mem (offset expected : Nat) : testNode expected ∈ (graph offset expected).nodes :=
  List.Mem.tail _ (List.Mem.head _)
private theorem erase_yes_mem (offset expected : Nat) : eraseYesNode ∈ (graph offset expected).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem erase_no_mem (offset expected : Nat) : eraseNoNode ∈ (graph offset expected).nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private theorem copy_good (offset expected : Nat) : (copyNode offset expected).WellFormed := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct offset, ?_, ?_,
    RegisterCopy.machine_acceptState_ne_rejectState offset⟩
  · intro rule hRule
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState offset rule hRule)
  · intro rule hRule
    have h := RegisterCopy.rule_source_lt_acceptState offset rule hRule
    rw [RegisterCopy.machine_acceptState] at h
    change rule.sourceState ≠ (RegisterCopy.machine offset).rejectState
    rw [RegisterCopy.machine_rejectState]
    omega

private theorem test_good (expected : Nat) : (testNode expected).WellFormed :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct expected,
   BuilderUnaryTagMatch.noRuleAtAccept expected, BuilderUnaryTagMatch.noRuleAtReject expected,
   BuilderUnaryTagMatch.acceptState_ne_rejectState expected⟩

private theorem erase_good : eraseYesNode.WellFormed ∧ eraseNoNode.WellFormed := by
  have h := And.intro BuilderRegisterErase.one_rules_pairwise_query_distinct
    (And.intro BuilderRegisterErase.one_noRuleAtAccept
      (And.intro BuilderRegisterErase.one_noRuleAtReject BuilderRegisterErase.one_acceptState_ne_rejectState))
  exact ⟨h, h⟩

theorem graph_wellFormed (offset expected : Nat) : (graph offset expected).WellFormed := by
  have hNames : ((graph offset expected).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0,1,2,3] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact copy_good offset expected
    · exact test_good expected
    · exact erase_good.1
    · exact erase_good.2
  · exact ⟨copyNode offset expected, copy_mem offset expected, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact ⟨⟨testNode expected, test_mem offset expected, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨eraseYesNode, erase_yes_mem offset expected, rfl, rfl⟩,
        ⟨eraseNoNode, erase_no_mem offset expected, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem rules_pairwise_query_distinct (offset expected : Nat) :
    (machine offset expected).rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise _ (graph_wellFormed offset expected)
theorem noRuleAtAccept (offset expected : Nat) : WorkMachineChain.NoRuleAtAccept (machine offset expected) :=
  WorkMachineProgramGraph.noRuleAt_globalAccept _
theorem noRuleAtReject (offset expected : Nat) :
    WorkMachineProgramGraph.NoRuleAt (machine offset expected) (machine offset expected).rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject _
theorem acceptState_ne_rejectState (offset expected : Nat) :
    (machine offset expected).acceptState ≠ (machine offset expected).rejectState := by
  change (0 : Nat) ≠ 1
  decide

def endpoint (expected actual : Nat) : Endpoint := if actual = expected then .accept else .reject
def inputValues (older : List Nat) (actual : Nat) (newer : List Nat) : List Nat := older ++ [actual] ++ newer
def copiedOutside (actual : Nat) (outside : List WorkSymbol) : List WorkSymbol := outside.drop (actual + 1)
def restoredOutside (actual : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate (actual + 1) WorkSymbol.blank ++ copiedOutside actual outside
def workSteps (expected actual : Nat) (newer : List Nat) : Nat :=
  RegisterCopy.steps newer actual + 1 + (BuilderUnaryTagMatch.workSteps expected actual + 1 + (actual + 2 + 1))
def initialConfiguration (offset expected actual : Nat) (older newer : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration (machine offset expected) (endTape (inputValues older actual newer) inside outside)
def finalConfiguration (expected actual : Nat) (older newer : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  endpointConfiguration (endpoint expected actual)
    (endTape (inputValues older actual newer) inside (restoredOutside actual outside))

private theorem copy_run (offset : Nat) (older : List Nat) (actual : Nat) (newer : List Nat)
    (inside outside : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (RegisterCopy.machine offset) (RegisterCopy.steps newer actual)
      (workStartConfiguration (RegisterCopy.machine offset) (endTape (inputValues older actual newer) inside outside)) =
      some {state := (RegisterCopy.machine offset).acceptState, tape := endTape (inputValues older actual newer ++ [actual]) inside (copiedOutside actual outside)} := by
  subst offset
  have h := RegisterCopy.workRunExact (registerWord older) inside outside actual newer
  have hInitial : RegisterCopy.initialConfiguration (registerWord older) inside outside actual newer =
      workStartConfiguration (RegisterCopy.machine newer.length) (endTape (inputValues older actual newer) inside outside) := by
    simp only [RegisterCopy.initialConfiguration, endTape, workStartConfiguration, inputValues,
      RegisterCopy.machine_startState, registerWord_append, List.append_assoc]
    rfl
  have hFinal : RegisterCopy.finalConfiguration (registerWord older) inside outside actual newer =
      {state := (RegisterCopy.machine newer.length).acceptState,
       tape := endTape (inputValues older actual newer ++ [actual]) inside (copiedOutside actual outside)} := by
    simp only [RegisterCopy.finalConfiguration, endTape, inputValues, copiedOutside,
      RegisterCopy.machine_acceptState, registerWord_append, List.append_assoc]
    rfl
  rw [hInitial, hFinal] at h
  exact h

private theorem graph_entry (offset expected : Nat) :
    (graph offset expected).entry = (copyNode offset expected).reference := rfl

private theorem execution_path (offset expected actual : Nat) (older newer : List Nat)
    (inside outside : List WorkSymbol) (hLength : newer.length = offset) :
    AcceptPath (graph offset expected) (.node (graph offset expected).entry) (endpoint expected actual)
      (workSteps expected actual newer) (endTape (inputValues older actual newer) inside outside)
      (endTape (inputValues older actual newer) inside (restoredOutside actual outside)) := by
  have hCopy : LocalAcceptRun (copyNode offset expected) (RegisterCopy.steps newer actual)
      (endTape (inputValues older actual newer) inside outside)
      (endTape (inputValues older actual newer ++ [actual]) inside (copiedOutside actual outside)) :=
    copy_run offset older actual newer inside outside hLength
  have hErase := BuilderRegisterErase.one_workRunExact (inputValues older actual newer) actual inside (copiedOutside actual outside)
  by_cases hEqual : actual = expected
  · have hLocal : LocalAcceptRun (testNode expected) (BuilderUnaryTagMatch.workSteps expected actual)
        (endTape (inputValues older actual newer ++ [actual]) inside (copiedOutside actual outside))
        (endTape (inputValues older actual newer ++ [actual]) inside (copiedOutside actual outside)) := by
      subst actual
      exact BuilderUnaryTagMatch.accept_workRunExact expected _ inside _
    have hTail := AcceptPath.step eraseYesNode .accept _ 0 _ _ _
      (erase_yes_mem offset expected) hErase (.terminal .accept _)
    have hTest := AcceptPath.step (testNode expected) .accept _ _ _ _ _
      (test_mem offset expected) hLocal hTail
    have h := AcceptPath.step (copyNode offset expected) .accept _ _ _ _ _
      (copy_mem offset expected) hCopy hTest
    simpa only [workSteps, endpoint, if_pos hEqual, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, graph_entry, restoredOutside] using h
  · have hLocal : LocalRejectRun (testNode expected) (BuilderUnaryTagMatch.workSteps expected actual)
        (endTape (inputValues older actual newer ++ [actual]) inside (copiedOutside actual outside))
        (endTape (inputValues older actual newer ++ [actual]) inside (copiedOutside actual outside)) :=
      BuilderUnaryTagMatch.reject_workRunExact expected actual _ inside _ hEqual
    have hTail := AcceptPath.step eraseNoNode .reject _ 0 _ _ _
      (erase_no_mem offset expected) hErase (.terminal .reject _)
    have hTest := AcceptPath.stepReject (testNode expected) .reject _ _ _ _ _
      (test_mem offset expected) hLocal hTail
    have h := AcceptPath.step (copyNode offset expected) .reject _ _ _ _ _
      (copy_mem offset expected) hCopy hTest
    simpa only [workSteps, endpoint, if_neg hEqual, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, graph_entry, restoredOutside] using h

private theorem initial_projection (offset expected : Nat) (tape : WorkTape) :
    endpointConfiguration (.node (graph offset expected).entry) tape =
      workStartConfiguration (machine offset expected) tape := rfl

/-- Both outcomes execute comparison and erasure from the original register word. -/
theorem workRunExact (offset expected actual : Nat) (older newer : List Nat)
    (inside outside : List WorkSymbol) (hLength : newer.length = offset) :
    workRunExact? (machine offset expected) (workSteps expected actual newer)
      (initialConfiguration offset expected actual older newer inside outside) =
      some (finalConfiguration expected actual older newer inside outside) := by
  have h := WorkMachineProgramPath.runExact (graph offset expected) _ _ _ _ _
    (graph_wellFormed offset expected) (execution_path offset expected actual older newer inside outside hLength)
  rw [initial_projection] at h
  exact h

theorem final_state (expected actual : Nat) (older newer : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration expected actual older newer inside outside).state =
      if actual = expected then 0 else 1 := by
  by_cases hEqual : actual = expected <;>
    simp only [finalConfiguration, endpoint, hEqual, ite_true, ite_false, endpointConfiguration,
      endpointState, WorkMachineProgramGraph.globalAcceptState, WorkMachineProgramGraph.globalRejectState]

theorem final_registers (expected actual : Nat) (older newer : List Nat) (inside outside : List WorkSymbol) :
    (finalConfiguration expected actual older newer inside outside).tape =
      endTape (older ++ [actual] ++ newer) inside (restoredOutside actual outside) := rfl

def copyWorkPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (.mul (.mul (.constant 4) (.add bound (.constant 1))) (.add bound (.constant 1)))
    (.mul (.constant 9) (.add bound (.constant 1)))) (.constant 5)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial := .add (.mul (.constant 2) bound) (.constant 1)
def rawTimePolynomial (expected : Nat) (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6) (.add (.add (copyWorkPolynomial bound) bound) (.constant (2 * expected + 8)))

theorem source_polynomial_bounds (expected actual : Nat) (older newer : List Nat)
    (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (inputValues older actual newer)).length + outside.length ≤ bound.eval input) :
    (registerWord (inputValues older actual newer)).length + (restoredOutside actual outside).length ≤
        (spanPolynomial bound).eval input ∧
      6 * workSteps expected actual newer ≤ (rawTimePolynomial expected bound).eval input := by
  have hLengths := hSpan
  simp only [inputValues, registerWord_append, List.length_append, registerWord_length,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hLengths
  have hActual : actual ≤ bound.eval input := by omega
  have hNewer : newer.length + newer.sum ≤ bound.eval input := by omega
  have hCopy := RegisterCopy.steps_le newer actual (bound.eval input) hActual hNewer
  have hTest := BuilderUnaryTagMatch.workSteps_le expected actual
  constructor
  · simp only [restoredOutside, copiedOutside, List.length_append, List.length_replicate,
      List.length_drop, spanPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega
  · simp only [workSteps, rawTimePolynomial, copyWorkPolynomial,
      NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
    omega

theorem canonical_final_blankEquivalent (expected actual : Nat) (older newer : List Nat) (inside : List WorkSymbol) :
    WorkTape.BlankEquivalent (finalConfiguration expected actual older newer inside []).tape
      (endTape (inputValues older actual newer) inside []) := by
  have h := BuilderRequestedPairLookup.endTape_blankEquivalent (inputValues older actual newer) inside
    (List.replicate (actual + 1) WorkSymbol.blank) (BuilderRequestedPairLookup.blankExterior_replicate _)
  simpa only [finalConfiguration, endpointConfiguration, restoredOutside, copiedOutside,
    List.drop_nil, List.append_nil] using h

/-- Transport the fixed test across a real blank-equivalent workspace. No empty
exterior, chosen comparison outcome or successful execution is supplied. -/
theorem workRun_preserving_match (offset expected actual : Nat) (older newer : List Nat)
    (inside : List WorkSymbol) (tape : WorkTape) (bound : NatPolynomial) (input : Nat)
    (hLength : newer.length = offset)
    (hSpan : (registerWord (inputValues older actual newer)).length ≤ bound.eval input)
    (hTape : WorkTape.BlankEquivalent tape (endTape (inputValues older actual newer) inside [])) :
    ∃ final : WorkConfiguration,
      workRunExact? (machine offset expected) (workSteps expected actual newer)
        (workStartConfiguration (machine offset expected) tape) = some final ∧
      final.state = endpointState (endpoint expected actual) ∧
      WorkTape.BlankEquivalent final.tape (endTape (inputValues older actual newer) inside []) ∧
      6 * workSteps expected actual newer ≤ (rawTimePolynomial expected bound).eval input := by
  have hRun := workRunExact offset expected actual older newer inside [] hLength
  have hInitial : WorkConfiguration.BlankEquivalent
      (workStartConfiguration (machine offset expected) tape)
      (initialConfiguration offset expected actual older newer inside []) := ⟨rfl, hTape⟩
  obtain ⟨final, hActual, hEquivalent⟩ := PNP.Concrete.workRunExact?_transport
    (machine offset expected) (workSteps expected actual newer) hInitial hRun
  have hBounds := source_polynomial_bounds expected actual older newer [] bound input (by
    simpa only [List.length_nil, Nat.add_zero] using hSpan)
  exact ⟨final, hActual, hEquivalent.1,
    WorkTape.blankEquivalent_trans hEquivalent.2 (canonical_final_blankEquivalent expected actual older newer inside), hBounds.2⟩

theorem uniform_polynomial_match (offset expected actual : Nat) (older newer : List Nat)
    (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hLength : newer.length = offset)
    (hSpan : (registerWord (inputValues older actual newer)).length + outside.length ≤ bound.eval input) :
    6 * workSteps expected actual newer ≤ (rawTimePolynomial expected bound).eval input ∧
      run (compileWorkMachine (machine offset expected)) (6 * workSteps expected actual newer)
        (encodeWorkConfiguration (initialConfiguration offset expected actual older newer inside outside)) =
        encodeWorkConfiguration (finalConfiguration expected actual older newer inside outside) ∧
      (registerWord (inputValues older actual newer)).length + (restoredOutside actual outside).length ≤
        (spanPolynomial bound).eval input := by
  have hBounds := source_polynomial_bounds expected actual older newer outside bound input hSpan
  exact ⟨hBounds.2, run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact offset expected actual older newer inside outside hLength), hBounds.1⟩

end PNP.Concrete.CookLevin.BuilderRequestRegisterMatch
