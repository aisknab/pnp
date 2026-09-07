/-
Copyright (c) 2026 PNP Labs.

Strict comparison of two disposable ordinary registers with complete recovery.
A fixed reserve step prepares the one restoration cell; the unchanged physical
comparator supplies the verdict; restoration and erasure recover the retained
source frame. Both branches account for every cleared and consumed exterior cell.

This is the comparison boundary needed by the canonical control-head right
clamp. No operand value, verdict, or execution certificate determines the program.
-/

import PNP.Concrete.CookLevinBuilderRegisterPairExterior
import PNP.Concrete.CookLevinBuilderRegisterCountdownControl
import PNP.Concrete.CookLevinBuilderRegisterErase

namespace PNP.Concrete.CookLevin.BuilderRegisterLessThan

open BuilderUnaryPolynomial (registerWord registerWord_append registerWord_length)
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

private theorem chain_run (first second : WorkMachine) (n m : Nat)
    (initial middle final : WorkTape)
    (hFirst : workRunExact? first n (workStartConfiguration first initial) =
      some {state := first.acceptState, tape := middle})
    (hSecond : workRunExact? second m (workStartConfiguration second middle) =
      some {state := second.acceptState, tape := final}) :
    workRunExact? (WorkMachineChain.machine first second) (n + 1 + m)
      (workStartConfiguration (WorkMachineChain.machine first second) initial) =
      some {state := (WorkMachineChain.machine first second).acceptState, tape := final} :=
  WorkMachineChain.workRunExact first second n m _ _ _ hFirst rfl hSecond

/-- Temporarily increment and decrement the newest register, reserving one blank cell. -/
def reserveMachine : WorkMachine :=
  WorkMachineChain.machine BuilderConstraintRegionAssembly.Increment.machine
    BuilderRegisterCountdownControl.decrement

theorem decrement_workRunExact (value : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? BuilderRegisterCountdownControl.decrement 2
      (workStartConfiguration BuilderRegisterCountdownControl.decrement
        (endTape (older ++ [value + 1]) inside outside)) =
      some {
        state := BuilderRegisterCountdownControl.decrement.acceptState
        tape := endTape (older ++ [value]) inside (WorkSymbol.blank :: outside) } := by
  simpa only [endTape, registerWord_append, registerWord, List.append_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate,
    List.nil_append, List.cons_append, List.append_assoc] using
    BuilderRegisterCountdownControl.decrement_workRunExact value (registerWord older) inside outside

theorem reserve_workRunExact (value : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? reserveMachine 5
      (workStartConfiguration reserveMachine (endTape (older ++ [value]) inside outside)) =
      some {
        state := reserveMachine.acceptState
        tape := endTape (older ++ [value]) inside (WorkSymbol.blank :: outside.drop 1) } :=
  chain_run _ _ 2 2 _ _ _
    (BuilderConstraintRegionAssembly.Increment.workRunExact older value inside outside)
    (decrement_workRunExact value older inside (outside.drop 1))

def eraseLessNode : Node :=
  {name := 4, program := BuilderRegisterErase.machine 3, onAccept := .accept, onReject := .dead}
def eraseNotLessNode : Node :=
  {name := 5, program := BuilderRegisterErase.machine 3, onAccept := .reject, onReject := .dead}
def restoreLessNode : Node :=
  {name := 2, program := BuilderRegionResidualRegisters.machine,
   onAccept := .node eraseLessNode.reference, onReject := .dead}
def restoreNotLessNode : Node :=
  {name := 3, program := BuilderRegionResidualRegisters.machine,
   onAccept := .node eraseNotLessNode.reference, onReject := .node eraseNotLessNode.reference}
def compareNode : Node :=
  {name := 1, program := BuilderRegionPairComparison.machine,
   onAccept := .node restoreLessNode.reference, onReject := .node restoreNotLessNode.reference}
def reserveNode : Node :=
  {name := 0, program := reserveMachine, onAccept := .node compareNode.reference, onReject := .dead}

def graph : Graph :=
  {nodes := [reserveNode, compareNode, restoreLessNode, restoreNotLessNode,
    eraseLessNode, eraseNotLessNode], entry := reserveNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

private theorem reserve_mem : reserveNode ∈ graph.nodes := List.Mem.head _
private theorem compare_mem : compareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem restoreLess_mem : restoreLessNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem restoreNotLess_mem : restoreNotLessNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem eraseLess_mem : eraseLessNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem eraseNotLess_mem : eraseNotLessNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem reserve_good : Good reserveMachine := by
  have hDec := BuilderRegisterCountdownControl.decrement_control
  refine ⟨WorkMachineChain.rules_pairwise_query_distinct _ _
      BuilderConstraintRegionAssembly.Increment.rules_pairwise_query_distinct hDec.1
      BuilderConstraintRegionAssembly.Increment.noRuleAtAccept,
    WorkMachineChain.noRuleAtAccept _ _ hDec.2.1, ?_,
    WorkMachineChain.machine_acceptState_ne_rejectState _ _ hDec.2.2.2⟩
  intro selected hMem
  decide +revert

private theorem comparison_good : Good BuilderRegionPairComparison.machine := by
  refine ⟨BuilderRegionPairComparison.rules_pairwise_query_distinct,
    BuilderRegionPairComparison.noRuleAtAccept, ?_,
    BuilderRegionPairComparison.acceptState_ne_rejectState⟩
  intro selected hMem
  decide +revert

private theorem restoration_good : Good BuilderRegionResidualRegisters.machine := by
  refine ⟨BuilderRegionResidualRegisters.rules_pairwise_query_distinct,
    BuilderRegionResidualRegisters.noRuleAtAccept, ?_,
    BuilderRegionResidualRegisters.acceptState_ne_rejectState⟩
  intro selected hMem
  decide +revert

private theorem erasure_good : Good (BuilderRegisterErase.machine 3) :=
  ⟨BuilderRegisterErase.rules_pairwise_query_distinct 3,
    BuilderRegisterErase.noRuleAtAccept 3, BuilderRegisterErase.noRuleAtReject 3,
    BuilderRegisterErase.acceptState_ne_rejectState 3⟩

theorem graph_wellFormed : graph.WellFormed := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact reserve_good
    · exact comparison_good
    · exact restoration_good
    · exact restoration_good
    · exact erasure_good
    · exact erasure_good
  · exact ⟨reserveNode, reserve_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨compareNode, compare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨restoreLessNode, restoreLess_mem, rfl, rfl⟩,
        ⟨restoreNotLessNode, restoreNotLess_mem, rfl, rfl⟩⟩
    · exact ⟨⟨eraseLessNode, eraseLess_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨eraseNotLessNode, eraseNotLess_mem, rfl, rfl⟩,
        ⟨eraseNotLessNode, eraseNotLess_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def resultValues (result : RawRouter.ComparisonResult) : List Nat :=
  BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison result)
def restoreSteps (result : RawRouter.ComparisonResult) : Nat :=
  BuilderRegionResidualRegisters.workSteps (BuilderRegionResidualRegisters.ofComparison result)
def clearedSpan (result : RawRouter.ComparisonResult) : Nat :=
  BuilderRegisterErase.clearedSpan (resultValues result)
def resultEndpoint : RawRouter.ComparisonResult → Endpoint
  | .less _ _ => .accept
  | .equal _ | .greater _ _ => .reject

theorem resultValues_length (result : RawRouter.ComparisonResult) : (resultValues result).length = 3 := rfl

private theorem span_all (processed coordinate boundary : Nat) :
    clearedSpan (RawRouter.compareResult processed coordinate boundary) =
      2 * processed + coordinate + boundary + 3 := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary <;>
        simp only [RawRouter.compareResult, clearedSpan, BuilderRegisterErase.clearedSpan,
          resultValues, BuilderRegionResidualRegisters.ofComparison,
          BuilderRegionResidualRegisters.restoredValues, registerWord_length,
          List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] <;> omega
  | succ coordinate ih =>
      cases boundary with
      | zero =>
          simp only [RawRouter.compareResult, clearedSpan, BuilderRegisterErase.clearedSpan,
            resultValues, BuilderRegionResidualRegisters.ofComparison,
            BuilderRegionResidualRegisters.restoredValues, registerWord_length,
            List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
          omega
      | succ boundary =>
          change clearedSpan (RawRouter.compareResult (processed + 1) coordinate boundary) = _
          rw [ih]
          omega

theorem clearedSpan_eq (coordinate boundary : Nat) :
    clearedSpan (RawRouter.compareResult 0 coordinate boundary) = coordinate + boundary + 3 := by
  simpa only [Nat.mul_zero, Nat.zero_add] using span_all 0 coordinate boundary

def resultTape (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  BuilderRegionResidualRegisters.inputTape (BuilderRegionResidualRegisters.ofComparison result)
    ((registerWord older).reverse ++ inside) (WorkSymbol.blank :: outside.drop 1)

def continuationSteps (result : RawRouter.ComparisonResult) : Nat :=
  restoreSteps result + 1 + BuilderRegisterErase.workSteps (resultValues result) + 1
def continuationEntry : RawRouter.ComparisonResult → Endpoint
  | .less _ _ => .node restoreLessNode.reference
  | .equal _ | .greater _ _ => .node restoreNotLessNode.reference

def workSteps (coordinate boundary : Nat) : Nat :=
  5 + 1 + BuilderRegionPairComparison.workSteps coordinate boundary + 1 +
    continuationSteps (RawRouter.compareResult 0 coordinate boundary)
def initialConfiguration (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [coordinate, boundary]) inside outside)
def finalConfiguration (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration
    (resultEndpoint (RawRouter.compareResult 0 coordinate boundary))
    (endTape older inside (List.replicate (coordinate + boundary + 3) WorkSymbol.blank ++ outside.drop 1))

private theorem restore_run (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? BuilderRegionResidualRegisters.machine (restoreSteps result)
      (workStartConfiguration BuilderRegionResidualRegisters.machine (resultTape result older inside outside)) =
      some {
        state := BuilderRegionResidualRegisters.terminalState (BuilderRegionResidualRegisters.isGreater result)
        tape := endTape (older ++ resultValues result) inside (outside.drop 1) } := by
  have h := BuilderRegionResidualRegisters.workRunExact
    (BuilderRegionResidualRegisters.ofComparison result) ((registerWord older).reverse ++ inside)
    (WorkSymbol.blank :: outside.drop 1) rfl
  simpa only [BuilderRegionResidualRegisters.initialConfiguration,
    BuilderRegionResidualRegisters.finalConfiguration, List.drop_succ_cons, List.drop_zero,
    BuilderRegionResidualRegisters.ofComparison_markedParity, endTape, registerWord_append,
    List.reverse_append, List.append_assoc, resultValues, resultTape, restoreSteps] using h

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat)
    (tape : WorkTape) (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      subst currentState
      subst currentTape
      rfl

private theorem pair_run (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? BuilderRegionPairComparison.machine (BuilderRegionPairComparison.workSteps coordinate boundary)
      (workStartConfiguration BuilderRegionPairComparison.machine
        (endTape (older ++ [coordinate, boundary]) inside (WorkSymbol.blank :: outside.drop 1))) =
      some {
        state := if (RawRouter.compareResult 0 coordinate boundary).isLess then
          BuilderRegionPairComparison.machine.acceptState else BuilderRegionPairComparison.machine.rejectState
        tape := resultTape (RawRouter.compareResult 0 coordinate boundary) older inside outside } := by
  have h := BuilderRegisterPairExterior.workRunExact coordinate boundary older inside
    (WorkSymbol.blank :: outside.drop 1)
  have hState := BuilderRegisterPairExterior.final_state coordinate boundary older inside
    (WorkSymbol.blank :: outside.drop 1)
  have hTape := BuilderRegisterPairExterior.final_tape coordinate boundary older inside
    (WorkSymbol.blank :: outside.drop 1)
  rw [show BuilderRegisterPairExterior.finalConfiguration coordinate boundary older inside
      (WorkSymbol.blank :: outside.drop 1) =
      {state := if (RawRouter.compareResult 0 coordinate boundary).isLess then
        BuilderRegionPairComparison.machine.acceptState else BuilderRegionPairComparison.machine.rejectState,
       tape := resultTape (RawRouter.compareResult 0 coordinate boundary) older inside outside} from
    configuration_eq_of_fields _ _ _ hState hTape] at h
  exact h

private theorem continuation_path (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (continuationEntry result) (resultEndpoint result) (continuationSteps result)
      (resultTape result older inside outside)
      (endTape older inside (List.replicate (clearedSpan result) WorkSymbol.blank ++ outside.drop 1)) := by
  have hRestore := restore_run result older inside outside
  have hErase := BuilderRegisterErase.workRunExact 3 older (resultValues result) inside
    (outside.drop 1) (resultValues_length result)
  simp only [BuilderRegisterErase.initialConfiguration, BuilderRegisterErase.finalConfiguration] at hErase
  cases result with
  | less matched rest =>
      have hE := AcceptPath.step eraseLessNode .accept
        (BuilderRegisterErase.workSteps (resultValues (.less matched rest))) 0 _ _ _
        eraseLess_mem hErase (.terminal .accept _)
      have hR := AcceptPath.step restoreLessNode .accept (restoreSteps (.less matched rest))
        _ _ _ _ restoreLess_mem hRestore hE
      simpa only [continuationEntry, resultEndpoint, continuationSteps, Nat.add_zero,
        Nat.add_assoc, clearedSpan] using hR
  | equal matched =>
      have hE := AcceptPath.step eraseNotLessNode .reject
        (BuilderRegisterErase.workSteps (resultValues (.equal matched))) 0 _ _ _
        eraseNotLess_mem hErase (.terminal .reject _)
      have hR := AcceptPath.step restoreNotLessNode .reject (restoreSteps (.equal matched))
        _ _ _ _ restoreNotLess_mem hRestore hE
      simpa only [continuationEntry, resultEndpoint, continuationSteps, Nat.add_zero,
        Nat.add_assoc, clearedSpan] using hR
  | greater matched rest =>
      have hE := AcceptPath.step eraseNotLessNode .reject
        (BuilderRegisterErase.workSteps (resultValues (.greater matched rest))) 0 _ _ _
        eraseNotLess_mem hErase (.terminal .reject _)
      have hR := AcceptPath.stepReject restoreNotLessNode .reject (restoreSteps (.greater matched rest))
        _ _ _ _ restoreNotLess_mem hRestore hE
      simpa only [continuationEntry, resultEndpoint, continuationSteps, Nat.add_zero,
        Nat.add_assoc, clearedSpan] using hR

/-- One fixed physical graph recovers the same retained frame on both comparison outcomes. -/
theorem workRunExact (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary)
      (initialConfiguration coordinate boundary older inside outside) =
      some (finalConfiguration coordinate boundary older inside outside) := by
  have hReserve := reserve_workRunExact boundary (older ++ [coordinate]) inside outside
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hReserve
  have hCompare := pair_run coordinate boundary older inside outside
  have hTail := continuation_path (RawRouter.compareResult 0 coordinate boundary) older inside outside
  have hPath : AcceptPath graph (.node compareNode.reference)
      (resultEndpoint (RawRouter.compareResult 0 coordinate boundary))
      (BuilderRegionPairComparison.workSteps coordinate boundary + 1 +
        continuationSteps (RawRouter.compareResult 0 coordinate boundary))
      (endTape (older ++ [coordinate, boundary]) inside (WorkSymbol.blank :: outside.drop 1))
      (endTape older inside
        (List.replicate (clearedSpan (RawRouter.compareResult 0 coordinate boundary)) WorkSymbol.blank ++
          outside.drop 1)) := by
    cases hResult : RawRouter.compareResult 0 coordinate boundary with
    | less matched rest =>
        simp only [hResult] at hCompare hTail ⊢
        exact AcceptPath.step compareNode .accept _ _ _ _ _ compare_mem hCompare hTail
    | equal matched =>
        simp only [hResult] at hCompare hTail ⊢
        exact AcceptPath.stepReject compareNode .reject _ _ _ _ _ compare_mem hCompare hTail
    | greater matched rest =>
        simp only [hResult] at hCompare hTail ⊢
        exact AcceptPath.stepReject compareNode .reject _ _ _ _ _ compare_mem hCompare hTail
  have hAll := AcceptPath.step reserveNode _ 5 _ _ _ _ reserve_mem hReserve hPath
  rw [clearedSpan_eq] at hAll
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hAll
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node reserveNode.reference) tape =
        workStartConfiguration machine tape := rfl
  rw [hStart] at h
  simpa only [initialConfiguration, finalConfiguration, workSteps, machine, Nat.add_assoc] using h

theorem run_compile_exact (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration coordinate boundary older inside outside)) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact coordinate boundary older inside outside)

theorem final_accept_iff (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).state = machine.acceptState ↔
      coordinate < boundary := by
  change WorkMachineProgramGraph.endpointState
    (resultEndpoint (RawRouter.compareResult 0 coordinate boundary)) =
    WorkMachineProgramGraph.globalAcceptState ↔ _
  rw [← RawRouter.compareResult_isLess_iff 0 coordinate boundary]
  cases RawRouter.compareResult 0 coordinate boundary with
  | less _ _ =>
      change (0 = 0 ↔ true = true)
      decide
  | equal _ =>
      change (1 = 0 ↔ false = true)
      decide
  | greater _ _ =>
      change (1 = 0 ↔ false = true)
      decide

theorem final_reject_iff (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).state = machine.rejectState ↔
      boundary ≤ coordinate := by
  have hLess := RawRouter.compareResult_isLess_iff 0 coordinate boundary
  change WorkMachineProgramGraph.endpointState
    (resultEndpoint (RawRouter.compareResult 0 coordinate boundary)) =
    WorkMachineProgramGraph.globalRejectState ↔ _
  cases hResult : RawRouter.compareResult 0 coordinate boundary with
  | less matched rest =>
      rw [hResult] at hLess
      have hlt : coordinate < boundary := hLess.mp rfl
      exact iff_of_false (by change ¬ (0 = 1); decide) (by omega)
  | equal matched =>
      rw [hResult] at hLess
      have hNot : ¬ coordinate < boundary := by
        intro h
        have hFalse := hLess.mpr h
        change (false : Bool) = true at hFalse
        cases hFalse
      exact iff_of_true rfl (by omega)
  | greater matched rest =>
      rw [hResult] at hLess
      have hNot : ¬ coordinate < boundary := by
        intro h
        have hFalse := hLess.mpr h
        change (false : Bool) = true at hFalse
        cases hFalse
      exact iff_of_true rfl (by omega)

theorem final_inside_preserved (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).tape.right =
      (registerWord older).reverse ++ inside := rfl

theorem final_outside_accounted (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).tape.left =
      List.replicate (coordinate + boundary + 3) WorkSymbol.blank ++ outside.drop 1 := rfl

private theorem restoreSteps_le (coordinate boundary bound : Nat)
    (hc : coordinate ≤ bound) (hb : boundary ≤ bound) :
    restoreSteps (RawRouter.compareResult 0 coordinate boundary) ≤ 15 * (2 * bound + 3) + 13 := by
  have hSpan := clearedSpan_eq coordinate boundary
  have hFields :
      let view := BuilderRegionResidualRegisters.ofComparison (RawRouter.compareResult 0 coordinate boundary)
      view.boundaryRest ≤ 2 * bound + 3 ∧ view.boundaryMarked ≤ 2 * bound + 3 ∧
        view.coordinateRest ≤ 2 * bound + 3 ∧ view.coordinateMarked ≤ 2 * bound + 3 := by
    cases hResult : RawRouter.compareResult 0 coordinate boundary <;>
      simp only [hResult, clearedSpan, BuilderRegisterErase.clearedSpan, resultValues,
        BuilderRegionResidualRegisters.ofComparison, BuilderRegionResidualRegisters.restoredValues,
        registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hSpan ⊢ <;>
      exact ⟨by omega, by omega, by omega, by omega⟩
  exact BuilderRegionResidualRegisters.workSteps_le _ _ hFields.1 hFields.2.1 hFields.2.2.1 hFields.2.2.2

def workBound (bound : Nat) : Nat :=
  (2 * bound + 4 + 6 * (bound + 1) * (bound + 1)) + 15 * (2 * bound + 3) + 13 + 2 * bound + 18

theorem workSteps_le (coordinate boundary bound : Nat) (hc : coordinate ≤ bound) (hb : boundary ≤ bound) :
    workSteps coordinate boundary ≤ workBound bound := by
  have hPair := BuilderRegionPairComparison.workSteps_le coordinate boundary bound hc hb
  have hRestore := restoreSteps_le coordinate boundary bound hc hb
  have hSpan := clearedSpan_eq coordinate boundary
  have hLength := resultValues_length (RawRouter.compareResult 0 coordinate boundary)
  simp only [clearedSpan] at hSpan
  simp only [workSteps, continuationSteps, BuilderRegisterErase.workSteps, hLength, hSpan, workBound]
  omega

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.constant 6)
    (.add
      (.add (.add (.mul (.constant 2) bound) (.constant 4))
        (.mul (.mul (.constant 6) (.add bound (.constant 1))) (.add bound (.constant 1))))
      (.add (.add (.mul (.constant 15) (.add (.mul (.constant 2) bound) (.constant 3)))
        (.constant 13)) (.add (.mul (.constant 2) bound) (.constant 18))))

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := by
  simp only [rawTimePolynomial, NatPolynomial.eval, workBound]
  omega

theorem raw_time_polynomial (coordinate boundary : Nat) (bound : NatPolynomial) (input : Nat)
    (hc : coordinate ≤ bound.eval input) (hb : boundary ≤ bound.eval input) :
    6 * workSteps coordinate boundary ≤ (rawTimePolynomial bound).eval input := by
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le coordinate boundary (bound.eval input) hc hb)

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderRegisterLessThan
