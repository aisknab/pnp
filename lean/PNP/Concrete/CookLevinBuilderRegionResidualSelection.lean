/-
Copyright (c) 2026 PNP Labs.

One fixed graph compares an ordinary disposable pair, restores the actual marked
fields, and copies or increments the resulting coordinate. Every successor is
literal finite control. No input-dependent verdict or correctness certificate
is supplied to the executable machine.

The all-source preparation, five-region dispatcher and complete formula-builder
loop still require composition; this module alone does not earn that checkpoint.
-/

import PNP.Concrete.CookLevinBuilderRegionResidualRegisters
import PNP.Concrete.WorkMachineProgramPath

namespace PNP.Concrete.CookLevin.BuilderRegionResidualSelection

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node NodeRef Endpoint Graph)
open WorkMachineProgramPath (LocalAcceptRun LocalRejectRun AcceptPath)

def incrementNode : Node :=
  { name := 6
    program := BuilderConstraintRegionAssembly.Increment.machine
    onAccept := .reject
    onReject := .dead }

def copyRemainderNode : Node :=
  { name := 5
    program := RegisterCopy.machine 1
    onAccept := .node incrementNode.reference
    onReject := .dead }

def copyZeroNode : Node :=
  { name := 4
    program := RegisterCopy.machine 1
    onAccept := .reject
    onReject := .dead }

def copySelectedNode : Node :=
  { name := 3
    program := RegisterCopy.machine 2
    onAccept := .accept
    onReject := .dead }

def restoreResidualNode : Node :=
  { name := 2
    program := BuilderRegionResidualRegisters.machine
    onAccept := .node copyZeroNode.reference
    onReject := .node copyRemainderNode.reference }

def restoreSelectedNode : Node :=
  { name := 1
    program := BuilderRegionResidualRegisters.machine
    onAccept := .node copySelectedNode.reference
    onReject := .dead }

def compareNode : Node :=
  { name := 0
    program := BuilderRegionPairComparison.machine
    onAccept := .node restoreSelectedNode.reference
    onReject := .node restoreResidualNode.reference }

def graph : Graph :=
  { nodes := [compareNode, restoreSelectedNode, restoreResidualNode,
      copySelectedNode, copyZeroNode, copyRemainderNode, incrementNode]
    entry := compareNode.reference }

def machine : WorkMachine := WorkMachineProgramGraph.machine graph

private theorem compare_mem : compareNode ∈ graph.nodes :=
  List.Mem.head _
private theorem restoreSelected_mem : restoreSelectedNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.head _)
private theorem restoreResidual_mem : restoreResidualNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem copySelected_mem : copySelectedNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem copyZero_mem : copyZeroNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem copyRemainder_mem : copyRemainderNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
private theorem increment_mem : incrementNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

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

private theorem copy_good (offset : Nat) : Good (RegisterCopy.machine offset) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct offset, ?_, ?_,
    RegisterCopy.machine_acceptState_ne_rejectState offset⟩
  · intro selected hMem
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState offset selected hMem)
  · intro selected hMem
    have hLt := RegisterCopy.rule_source_lt_acceptState offset selected hMem
    rw [RegisterCopy.machine_acceptState] at hLt
    rw [RegisterCopy.machine_rejectState]
    omega

private theorem increment_good : Good BuilderConstraintRegionAssembly.Increment.machine := by
  refine ⟨BuilderConstraintRegionAssembly.Increment.rules_pairwise_query_distinct,
    BuilderConstraintRegionAssembly.Increment.noRuleAtAccept, ?_,
    BuilderConstraintRegionAssembly.Increment.acceptState_ne_rejectState⟩
  intro selected hMem
  decide +revert

theorem graph_wellFormed : graph.WellFormed := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact comparison_good
    · exact restoration_good
    · exact restoration_good
    · exact copy_good 2
    · exact copy_good 1
    · exact copy_good 1
    · exact increment_good
  · exact ⟨compareNode, compare_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨restoreSelectedNode, restoreSelected_mem, rfl, rfl⟩,
        ⟨restoreResidualNode, restoreResidual_mem, rfl, rfl⟩⟩
    · exact ⟨⟨copySelectedNode, copySelected_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨copyZeroNode, copyZero_mem, rfl, rfl⟩,
        ⟨copyRemainderNode, copyRemainder_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨incrementNode, increment_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem rules_length : machine.rules.length = 602 := by
  have hPair : BuilderRegionPairComparison.machine.rules.length = 68 := rfl
  have hRestore : BuilderRegionResidualRegisters.machine.rules.length = 42 := rfl
  change (WorkMachineProgramGraph.rules graph).length = 602
  rw [WorkMachineProgramGraph.rules_length]
  simp only [graph, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    compareNode, restoreSelectedNode, restoreResidualNode, copySelectedNode,
    copyZeroNode, copyRemainderNode, incrementNode, hPair, hRestore,
    RegisterCopy.rules_length, RegisterCopy.stateCount,
    BuilderConstraintRegionAssembly.Increment.rules_length]
  rfl

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph

theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

private def ComparisonFacts (processed coordinate boundary : Nat) : RawRouter.ComparisonResult → Prop
  | .less matched rest => matched = processed + coordinate ∧ boundary = coordinate + rest + 1
  | .equal matched => matched = processed + coordinate ∧ boundary = coordinate
  | .greater matched rest => matched = processed + boundary ∧ coordinate = boundary + rest + 1

private theorem comparison_facts (processed coordinate boundary : Nat) :
    ComparisonFacts processed coordinate boundary (RawRouter.compareResult processed coordinate boundary) := by
  induction coordinate generalizing processed boundary with
  | zero =>
    cases boundary <;>
      simp only [RawRouter.compareResult, ComparisonFacts, Nat.add_zero, Nat.zero_add, and_self]
  | succ coordinate ih =>
    cases boundary with
    | zero =>
      simp only [RawRouter.compareResult, ComparisonFacts, Nat.add_zero, Nat.zero_add, and_self]
    | succ boundary =>
      change ComparisonFacts processed (coordinate + 1) (boundary + 1)
        (RawRouter.compareResult (processed + 1) coordinate boundary)
      have h := ih (processed + 1) boundary
      cases hResult : RawRouter.compareResult (processed + 1) coordinate boundary <;>
        simp only [ComparisonFacts, hResult] at h ⊢ <;> constructor <;> omega

def resultCoordinate : RawRouter.ComparisonResult → Nat
  | .less matched _ => matched
  | .equal _ => 0
  | .greater _ rest => rest + 1

def scratchValues (result : RawRouter.ComparisonResult) : List Nat :=
  BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison result) ++
    [resultCoordinate result]

def resultEndpoint : RawRouter.ComparisonResult → Endpoint
  | .less _ _ => .accept
  | .equal _ | .greater _ _ => .reject

def nextCoordinate (coordinate boundary : Nat) : Nat :=
  resultCoordinate (RawRouter.compareResult 0 coordinate boundary)

theorem nextCoordinate_eq (coordinate boundary : Nat) :
    nextCoordinate coordinate boundary =
      if coordinate < boundary then coordinate else coordinate - boundary := by
  have h := comparison_facts 0 coordinate boundary
  unfold nextCoordinate
  cases hResult : RawRouter.compareResult 0 coordinate boundary with
  | less matched rest =>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at h
    rw [resultCoordinate, if_pos (by omega)]
    omega
  | equal matched =>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at h
    rw [resultCoordinate, if_neg (by omega)]
    omega
  | greater matched rest =>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at h
    rw [resultCoordinate, if_neg (by omega)]
    omega

theorem restoredBoundary_eq (coordinate boundary : Nat) :
    let view := BuilderRegionResidualRegisters.ofComparison (RawRouter.compareResult 0 coordinate boundary)
    view.boundaryRest + view.boundaryMarked = boundary := by
  have h := comparison_facts 0 coordinate boundary
  cases hResult : RawRouter.compareResult 0 coordinate boundary <;>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at h <;>
    simp only [BuilderRegionResidualRegisters.ofComparison, Nat.zero_add] <;> omega

private def resultTape (result : RawRouter.ComparisonResult) (older : List Nat)
    (workspace : List WorkSymbol) : WorkTape :=
  BuilderRegionResidualRegisters.inputTape (BuilderRegionResidualRegisters.ofComparison result)
    ((registerWord older).reverse ++ workspace) []

private def restoreValues (result : RawRouter.ComparisonResult) : List Nat :=
  BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison result)

private def restoreSteps (result : RawRouter.ComparisonResult) : Nat :=
  BuilderRegionResidualRegisters.workSteps (BuilderRegionResidualRegisters.ofComparison result)

private def continuationEntry : RawRouter.ComparisonResult → Endpoint
  | .less _ _ => .node restoreSelectedNode.reference
  | .equal _ | .greater _ _ => .node restoreResidualNode.reference

def continuationSteps : RawRouter.ComparisonResult → Nat
  | .less matched rest =>
      restoreSteps (.less matched rest) + RegisterCopy.steps [0, rest + 1 + matched] matched + 2
  | .equal matched =>
      restoreSteps (.equal matched) + RegisterCopy.steps [matched] 0 + 2
  | .greater matched rest =>
      restoreSteps (.greater matched rest) + RegisterCopy.steps [matched] rest + 5

def workSteps (coordinate boundary : Nat) : Nat :=
  BuilderRegionPairComparison.workSteps coordinate boundary + 1 +
    continuationSteps (RawRouter.compareResult 0 coordinate boundary)

def initialConfiguration (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [coordinate, boundary]) workspace [])

def finalConfiguration (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration
    (resultEndpoint (RawRouter.compareResult 0 coordinate boundary))
    (endTape (older ++ scratchValues (RawRouter.compareResult 0 coordinate boundary)) workspace [])

private theorem endTape_append (older values : List Nat) (workspace : List WorkSymbol) :
    endTape values ((registerWord older).reverse ++ workspace) [] =
      endTape (older ++ values) workspace [] := by
  simp only [endTape, registerWord_append, List.reverse_append, List.append_assoc]

private theorem restore_run (result : RawRouter.ComparisonResult) (older : List Nat)
    (workspace : List WorkSymbol) :
    workRunExact? BuilderRegionResidualRegisters.machine (restoreSteps result)
      (workStartConfiguration BuilderRegionResidualRegisters.machine (resultTape result older workspace)) =
      some {
        state := BuilderRegionResidualRegisters.terminalState (BuilderRegionResidualRegisters.isGreater result)
        tape := endTape (older ++ restoreValues result) workspace []
      } := by
  have h := BuilderRegionResidualRegisters.workRunExact
    (BuilderRegionResidualRegisters.ofComparison result) ((registerWord older).reverse ++ workspace) [] rfl
  simp only [BuilderRegionResidualRegisters.initialConfiguration,
    BuilderRegionResidualRegisters.finalConfiguration, List.drop_nil,
    BuilderRegionResidualRegisters.ofComparison_markedParity, endTape_append] at h
  exact h

private theorem copy_selected_run (older : List Nat) (a c d : Nat) (workspace : List WorkSymbol) :
    workRunExact? (RegisterCopy.machine 2) (RegisterCopy.steps [c, a] d)
      (workStartConfiguration (RegisterCopy.machine 2) (endTape (older ++ [d, c, a]) workspace [])) =
      some {
        state := (RegisterCopy.machine 2).acceptState
        tape := endTape (older ++ [d, c, a, d]) workspace []
      } := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append, List.drop_nil] using
    BuilderRegionComparisonOperands.copy_workRunExact 2 older [c, a] d workspace [] rfl

private theorem copy_residual_run (older : List Nat) (a c d : Nat) (workspace : List WorkSymbol) :
    workRunExact? (RegisterCopy.machine 1) (RegisterCopy.steps [a] c)
      (workStartConfiguration (RegisterCopy.machine 1) (endTape (older ++ [d, c, a]) workspace [])) =
      some {
        state := (RegisterCopy.machine 1).acceptState
        tape := endTape (older ++ [d, c, a, c]) workspace []
      } := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append, List.drop_nil] using
    BuilderRegionComparisonOperands.copy_workRunExact 1 (older ++ [d]) [a] c workspace [] rfl

private theorem continuation_path (result : RawRouter.ComparisonResult) (older : List Nat)
    (workspace : List WorkSymbol) :
    AcceptPath graph (continuationEntry result) (resultEndpoint result) (continuationSteps result)
      (resultTape result older workspace) (endTape (older ++ scratchValues result) workspace []) := by
  cases result with
  | less matched rest =>
    have hN := restore_run (.less matched rest) older workspace
    simp only [restoreValues, BuilderRegionResidualRegisters.ofComparison,
      BuilderRegionResidualRegisters.restoredValues] at hN
    have hC := copy_selected_run older (rest + 1 + matched) 0 matched workspace
    have copyPath := AcceptPath.step copySelectedNode .accept
      (RegisterCopy.steps [0, rest + 1 + matched] matched) 0 _ _ _
      copySelected_mem hC (.terminal .accept _)
    have allPath := AcceptPath.step restoreSelectedNode .accept (restoreSteps (.less matched rest))
      (RegisterCopy.steps [0, rest + 1 + matched] matched + 1 + 0) _ _ _
      restoreSelected_mem hN copyPath
    have hSteps : restoreSteps (.less matched rest) + 1 +
        (RegisterCopy.steps [0, rest + 1 + matched] matched + 1 + 0) =
        continuationSteps (.less matched rest) := by
      simp only [continuationSteps]
      omega
    rw [hSteps] at allPath
    simpa only [continuationEntry, resultEndpoint, scratchValues,
      BuilderRegionResidualRegisters.ofComparison, BuilderRegionResidualRegisters.restoredValues,
      resultCoordinate, List.cons_append, List.nil_append] using allPath
  | equal matched =>
    have hN := restore_run (.equal matched) older workspace
    simp only [restoreValues, BuilderRegionResidualRegisters.ofComparison,
      BuilderRegionResidualRegisters.restoredValues, Nat.zero_add] at hN
    have hC := copy_residual_run older matched 0 matched workspace
    have copyPath := AcceptPath.step copyZeroNode .reject
      (RegisterCopy.steps [matched] 0) 0 _ _ _ copyZero_mem hC (.terminal .reject _)
    have allPath := AcceptPath.step restoreResidualNode .reject (restoreSteps (.equal matched))
      (RegisterCopy.steps [matched] 0 + 1 + 0) _ _ _ restoreResidual_mem hN copyPath
    have hSteps : restoreSteps (.equal matched) + 1 + (RegisterCopy.steps [matched] 0 + 1 + 0) =
        continuationSteps (.equal matched) := by
      simp only [continuationSteps]
      omega
    rw [hSteps] at allPath
    simpa only [continuationEntry, resultEndpoint, scratchValues,
      BuilderRegionResidualRegisters.ofComparison, BuilderRegionResidualRegisters.restoredValues,
      resultCoordinate, Nat.zero_add, List.cons_append, List.nil_append] using allPath
  | greater matched rest =>
    have hN := restore_run (.greater matched rest) older workspace
    simp only [restoreValues, BuilderRegionResidualRegisters.ofComparison,
      BuilderRegionResidualRegisters.restoredValues, Nat.zero_add] at hN
    have hC := copy_residual_run older matched rest (matched + 1) workspace
    have hI := BuilderConstraintRegionAssembly.Increment.workRunExact
      (older ++ [matched + 1, rest, matched]) rest workspace []
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_nil] at hI
    have incrementPath := AcceptPath.step incrementNode .reject 2 0 _ _ _
      increment_mem hI (.terminal .reject _)
    have copyPath := AcceptPath.step copyRemainderNode .reject
      (RegisterCopy.steps [matched] rest) (2 + 1 + 0) _ _ _
      copyRemainder_mem hC incrementPath
    have allPath := AcceptPath.stepReject restoreResidualNode .reject (restoreSteps (.greater matched rest))
      (RegisterCopy.steps [matched] rest + 1 + (2 + 1 + 0)) _ _ _
      restoreResidual_mem hN copyPath
    have hSteps : restoreSteps (.greater matched rest) + 1 +
        (RegisterCopy.steps [matched] rest + 1 + (2 + 1 + 0)) =
        continuationSteps (.greater matched rest) := by
      simp only [continuationSteps]
      omega
    rw [hSteps] at allPath
    simpa only [continuationEntry, resultEndpoint, scratchValues,
      BuilderRegionResidualRegisters.ofComparison, BuilderRegionResidualRegisters.restoredValues,
      resultCoordinate, Nat.zero_add, List.cons_append, List.nil_append] using allPath

private theorem pair_final_tape (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    (BuilderRegionPairComparison.finalConfiguration coordinate boundary older workspace).tape =
      resultTape (RawRouter.compareResult 0 coordinate boundary) older workspace := by
  unfold resultTape
  rw [BuilderRegionResidualRegisters.inputTape_ofComparison]
  rfl

private theorem pair_final_state (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    (BuilderRegionPairComparison.finalConfiguration coordinate boundary older workspace).state =
      if (RawRouter.compareResult 0 coordinate boundary).isLess then
        BuilderRegionPairComparison.machine.acceptState else BuilderRegionPairComparison.machine.rejectState := by
  change WorkMachineChain.secondState
    (RawRouter.resultConfiguration (RawRouter.compareResult 0 coordinate boundary)).state = _
  rw [RawRouter.resultConfiguration_state]
  cases RawRouter.compareResult 0 coordinate boundary <;> rfl

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat)
    (tape : WorkTape) (hState : config.state = state) (hTape : config.tape = tape) :
    config = { state := state, tape := tape } := by
  cases config with
  | mk currentState currentTape =>
    change currentState = state at hState
    change currentTape = tape at hTape
    subst currentState
    subst currentTape
    rfl

private theorem pair_run (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    workRunExact? BuilderRegionPairComparison.machine (BuilderRegionPairComparison.workSteps coordinate boundary)
      (workStartConfiguration BuilderRegionPairComparison.machine
        (endTape (older ++ [coordinate, boundary]) workspace [])) =
      some {
        state := if (RawRouter.compareResult 0 coordinate boundary).isLess then
          BuilderRegionPairComparison.machine.acceptState else BuilderRegionPairComparison.machine.rejectState
        tape := resultTape (RawRouter.compareResult 0 coordinate boundary) older workspace
      } := by
  change workRunExact? BuilderRegionPairComparison.machine (BuilderRegionPairComparison.workSteps coordinate boundary)
    (BuilderRegionPairComparison.initialConfiguration coordinate boundary older workspace) = _
  rw [BuilderRegionPairComparison.workRunExact]
  apply congrArg some
  exact configuration_eq_of_fields _ _ _
    (pair_final_state coordinate boundary older workspace) (pair_final_tape coordinate boundary older workspace)

/-- Exact execution of the one fixed graph; every branch is derived from its actual comparator run. -/
theorem workRunExact (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary) (initialConfiguration coordinate boundary older workspace) =
      some (finalConfiguration coordinate boundary older workspace) := by
  have hCompare := pair_run coordinate boundary older workspace
  have hTail := continuation_path (RawRouter.compareResult 0 coordinate boundary) older workspace
  have hPath : AcceptPath graph (.node compareNode.reference)
      (resultEndpoint (RawRouter.compareResult 0 coordinate boundary))
      (BuilderRegionPairComparison.workSteps coordinate boundary + 1 +
        continuationSteps (RawRouter.compareResult 0 coordinate boundary))
      (endTape (older ++ [coordinate, boundary]) workspace [])
      (endTape (older ++ scratchValues (RawRouter.compareResult 0 coordinate boundary)) workspace []) := by
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
  exact WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath

theorem run_compile_exact (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration coordinate boundary older workspace)) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary older workspace) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact coordinate boundary older workspace)

theorem scratchValues_length (result : RawRouter.ComparisonResult) : (scratchValues result).length = 4 := by
  cases result <;> rfl

theorem scratchValues_last (result : RawRouter.ComparisonResult) :
    (scratchValues result).getLast? = some (resultCoordinate result) := by
  cases result <;> rfl

theorem final_accept_iff (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).state = machine.acceptState ↔ coordinate < boundary := by
  change WorkMachineProgramGraph.endpointState (resultEndpoint (RawRouter.compareResult 0 coordinate boundary)) =
    WorkMachineProgramGraph.globalAcceptState ↔ coordinate < boundary
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

theorem final_reject_iff (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).state = machine.rejectState ↔ boundary ≤ coordinate := by
  have h := comparison_facts 0 coordinate boundary
  change WorkMachineProgramGraph.endpointState (resultEndpoint (RawRouter.compareResult 0 coordinate boundary)) =
    WorkMachineProgramGraph.globalRejectState ↔ boundary ≤ coordinate
  cases hResult : RawRouter.compareResult 0 coordinate boundary with
  | less matched rest =>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at h
    exact iff_of_false (by change ¬(0 = 1); decide) (by omega)
  | equal matched =>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at h
    exact iff_of_true rfl (by omega)
  | greater matched rest =>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at h
    exact iff_of_true rfl (by omega)

theorem final_exterior_preserved (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).tape.right =
      (registerWord (scratchValues (RawRouter.compareResult 0 coordinate boundary))).reverse ++
        ((registerWord older).reverse ++ workspace) := by
  simp only [finalConfiguration, WorkMachineProgramGraph.endpointConfiguration,
    endTape, registerWord_append, List.reverse_append, List.append_assoc]

theorem final_outer_empty (coordinate boundary : Nat) (older : List Nat) (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).tape.left = [] := rfl

private theorem comparison_fields_le (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    let view := BuilderRegionResidualRegisters.ofComparison (RawRouter.compareResult 0 coordinate boundary)
    view.boundaryRest ≤ bound ∧ view.boundaryMarked ≤ bound ∧
      view.coordinateRest ≤ bound ∧ view.coordinateMarked ≤ bound := by
  have h := comparison_facts 0 coordinate boundary
  cases hResult : RawRouter.compareResult 0 coordinate boundary <;>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at h <;>
    simp only [BuilderRegionResidualRegisters.ofComparison] <;>
    exact ⟨by omega, by omega, by omega, by omega⟩

private def copyWorkBound (bound : Nat) : Nat :=
  4 * (2 * bound + 3) * (2 * bound + 3) + 9 * (2 * bound + 3) + 5

private theorem copy_steps_le (newer : List Nat) (value bound : Nat)
    (hValue : value ≤ bound) (hNewer : newer.length + newer.sum ≤ 2 * bound + 2) :
    RegisterCopy.steps newer value ≤ copyWorkBound bound := by
  have h := RegisterCopy.steps_le newer value (2 * bound + 2) (by omega) hNewer
  simpa only [copyWorkBound, Nat.add_assoc] using h

private theorem continuationSteps_le (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    continuationSteps (RawRouter.compareResult 0 coordinate boundary) ≤
      15 * bound + 13 + copyWorkBound bound + 5 := by
  have hFields := comparison_fields_le coordinate boundary bound hCoordinate hBoundary
  have hN := BuilderRegionResidualRegisters.workSteps_le
    (BuilderRegionResidualRegisters.ofComparison (RawRouter.compareResult 0 coordinate boundary)) bound
    hFields.1 hFields.2.1 hFields.2.2.1 hFields.2.2.2
  have hFacts := comparison_facts 0 coordinate boundary
  cases hResult : RawRouter.compareResult 0 coordinate boundary with
  | less matched rest =>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at hFacts
    simp only [hResult] at hN
    change restoreSteps (.less matched rest) ≤ 15 * bound + 13 at hN
    have hC := copy_steps_le [0, rest + 1 + matched] matched bound (by omega) (by
      simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
      omega)
    simp only [continuationSteps]
    omega
  | equal matched =>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at hFacts
    simp only [hResult] at hN
    change restoreSteps (.equal matched) ≤ 15 * bound + 13 at hN
    have hC := copy_steps_le [matched] 0 bound (by omega) (by
      simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega)
    simp only [continuationSteps]
    omega
  | greater matched rest =>
    simp only [hResult, ComparisonFacts, Nat.zero_add] at hFacts
    simp only [hResult] at hN
    change restoreSteps (.greater matched rest) ≤ 15 * bound + 13 at hN
    have hC := copy_steps_le [matched] rest bound (by omega) (by
      simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega)
    simp only [continuationSteps]
    omega

def workBound (bound : Nat) : Nat :=
  17 * bound + 23 + 6 * (bound + 1) * (bound + 1) + copyWorkBound bound

theorem workSteps_le (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    workSteps coordinate boundary ≤ workBound bound := by
  have hPair := BuilderRegionPairComparison.workSteps_le coordinate boundary bound hCoordinate hBoundary
  have hTail := continuationSteps_le coordinate boundary bound hCoordinate hBoundary
  unfold workSteps workBound
  omega

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  let oneMore := NatPolynomial.add bound (.constant 1)
  let doublePlusThree := NatPolynomial.add (.mul (.constant 2) bound) (.constant 3)
  let copyBound := NatPolynomial.add
    (.add (.mul (.mul (.constant 4) doublePlusThree) doublePlusThree)
      (.mul (.constant 9) doublePlusThree)) (.constant 5)
  .mul (.constant 6)
    (.add (.add (.add (.mul (.constant 17) bound) (.constant 23))
      (.mul (.mul (.constant 6) oneMore) oneMore)) copyBound)

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := rfl

theorem rawTimePolynomial_le (coordinate boundary : Nat) (bound : NatPolynomial) (input : Nat)
    (hCoordinate : coordinate ≤ bound.eval input) (hBoundary : boundary ≤ bound.eval input) :
    6 * workSteps coordinate boundary ≤ (rawTimePolynomial bound).eval input := by
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le coordinate boundary (bound.eval input) hCoordinate hBoundary)

end PNP.Concrete.CookLevin.BuilderRegionResidualSelection
