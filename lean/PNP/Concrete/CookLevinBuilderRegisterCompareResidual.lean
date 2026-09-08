/-
Copyright (c) 2026 PNP Labs.

One fixed graph compares a disposable coordinate/boundary pair, restores
the physical comparator registers, and appends a boundary and usable
residual. The greater branch corrects its one already marked coordinate
unit. Older registers and arbitrary source/exterior tape data are retained.
This is a row-loop primitive, not the completed Cook--Levin formula builder.
-/

import PNP.Concrete.CookLevinBuilderRegisterLessThan
import PNP.Concrete.CookLevinBuilderRegisterPack

namespace PNP.Concrete.CookLevin.BuilderRegisterCompareResidual

open BuilderUnaryPolynomial (registerWord registerWord_append registerWord_length)
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)
open BuilderRegisterLessThan (reserveMachine resultValues resultValues_length restoreSteps resultTape resultEndpoint)

/-- The three ordinary registers actually produced by physical restoration. -/
def environment (result : RawRouter.ComparisonResult) (index : Fin 3) : Nat :=
  match result, index.val with
  | .less processed _, 0 => processed
  | .less _ _, 1 => 0
  | .less processed remaining, _ => remaining + 1 + processed
  | .equal processed, 0 => processed
  | .equal _, 1 => 0
  | .equal processed, _ => processed
  | .greater processed _, 0 => processed + 1
  | .greater _ remaining, 1 => remaining
  | .greater processed _, _ => processed

theorem environment_ofFn (result : RawRouter.ComparisonResult) :
    List.ofFn (environment result) = resultValues result := by
  cases result <;>
    simp only [resultValues, BuilderRegionResidualRegisters.restoredValues,
      BuilderRegionResidualRegisters.ofComparison, Nat.zero_add] <;> rfl

def lessFields : List (BuilderRegisterPack.Field 3) :=
  [.argument ⟨2, by decide⟩, .argument ⟨0, by decide⟩]
def residualFields : List (BuilderRegisterPack.Field 3) :=
  [.argument ⟨2, by decide⟩, .argument ⟨1, by decide⟩]
def fields : RawRouter.ComparisonResult → List (BuilderRegisterPack.Field 3)
  | .less _ _ => lessFields
  | .equal _ | .greater _ _ => residualFields

def resultBoundary : RawRouter.ComparisonResult → Nat
  | .less processed remaining => remaining + 1 + processed
  | .equal processed | .greater processed _ => processed
def copiedCoordinate : RawRouter.ComparisonResult → Nat
  | .less processed _ => processed
  | .equal _ => 0
  | .greater _ remaining => remaining
def resultCoordinate : RawRouter.ComparisonResult → Nat
  | .less processed _ => processed
  | .equal _ => 0
  | .greater _ remaining => remaining + 1
def extraSteps : RawRouter.ComparisonResult → Nat
  | .less _ _ | .equal _ => 0
  | .greater _ _ => 3

def packedValues (result : RawRouter.ComparisonResult) : List Nat :=
  [resultBoundary result, copiedCoordinate result]
def outputValues (result : RawRouter.ComparisonResult) : List Nat :=
  resultValues result ++ [resultBoundary result, resultCoordinate result]
def allocatedCells (result : RawRouter.ComparisonResult) : Nat :=
  resultBoundary result + resultCoordinate result + 3
def packSteps (result : RawRouter.ComparisonResult) : Nat :=
  BuilderRegisterPack.workSteps (fields result) (environment result) []

theorem packedValues_eq (result : RawRouter.ComparisonResult) :
    BuilderRegisterPack.values (fields result) (environment result) = packedValues result := by
  cases result <;> rfl

theorem outputValues_length (result : RawRouter.ComparisonResult) :
    (outputValues result).length = 5 := by
  rw [outputValues, List.length_append, resultValues_length]
  rfl

private theorem boundary_all (processed coordinate boundary : Nat) :
    resultBoundary (RawRouter.compareResult processed coordinate boundary) = processed + boundary := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary <;> simp only [RawRouter.compareResult, resultBoundary] <;> omega
  | succ coordinate ih =>
      cases boundary with
      | zero => simp only [RawRouter.compareResult, resultBoundary, Nat.add_zero]
      | succ boundary =>
          change resultBoundary (RawRouter.compareResult (processed + 1) coordinate boundary) = _
          rw [ih]
          omega

theorem resultBoundary_eq (coordinate boundary : Nat) :
    resultBoundary (RawRouter.compareResult 0 coordinate boundary) = boundary := by
  simpa only [Nat.zero_add] using boundary_all 0 coordinate boundary

private theorem coordinate_all (processed coordinate boundary : Nat) :
    resultCoordinate (RawRouter.compareResult processed coordinate boundary) =
      if coordinate < boundary then processed + coordinate else coordinate - boundary := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary <;> simp only [RawRouter.compareResult, resultCoordinate,
        Nat.add_zero, Nat.zero_sub, Nat.lt_irrefl, Nat.zero_lt_succ, ite_false, ite_true]
  | succ coordinate ih =>
      cases boundary with
      | zero =>
          simp only [RawRouter.compareResult, resultCoordinate, Nat.not_lt_zero, ite_false, Nat.sub_zero]
      | succ boundary =>
          change resultCoordinate (RawRouter.compareResult (processed + 1) coordinate boundary) = _
          rw [ih]
          by_cases hLess : coordinate < boundary
          · have hNext : coordinate + 1 < boundary + 1 := by omega
            simp only [if_pos hLess, if_pos hNext]
            omega
          · have hNext : ¬ coordinate + 1 < boundary + 1 := by omega
            simp only [if_neg hLess, if_neg hNext]
            omega

theorem resultCoordinate_eq (coordinate boundary : Nat) :
    resultCoordinate (RawRouter.compareResult 0 coordinate boundary) =
      if coordinate < boundary then coordinate else coordinate - boundary := by
  simpa only [Nat.zero_add] using coordinate_all 0 coordinate boundary

theorem allocatedCells_eq (coordinate boundary : Nat) :
    allocatedCells (RawRouter.compareResult 0 coordinate boundary) =
      boundary + (if coordinate < boundary then coordinate else coordinate - boundary) + 3 := by
  rw [allocatedCells, resultBoundary_eq, resultCoordinate_eq]

def packLessNode : Node :=
  {name := 4, program := BuilderRegisterPack.machine lessFields 0,
   onAccept := .accept, onReject := .dead}
def packEqualNode : Node :=
  {name := 5, program := BuilderRegisterPack.machine residualFields 0,
   onAccept := .reject, onReject := .dead}
def incrementNode : Node :=
  {name := 7, program := BuilderConstraintRegionAssembly.Increment.machine,
   onAccept := .reject, onReject := .dead}
def packGreaterNode : Node :=
  {name := 6, program := BuilderRegisterPack.machine residualFields 0,
   onAccept := .node incrementNode.reference, onReject := .dead}
def restoreLessNode : Node :=
  {name := 2, program := BuilderRegionResidualRegisters.machine,
   onAccept := .node packLessNode.reference, onReject := .dead}
def restoreNotLessNode : Node :=
  {name := 3, program := BuilderRegionResidualRegisters.machine,
   onAccept := .node packEqualNode.reference, onReject := .node packGreaterNode.reference}
def compareNode : Node :=
  {name := 1, program := BuilderRegionPairComparison.machine,
   onAccept := .node restoreLessNode.reference, onReject := .node restoreNotLessNode.reference}
def reserveNode : Node :=
  {name := 0, program := reserveMachine, onAccept := .node compareNode.reference, onReject := .dead}
def graph : Graph :=
  {nodes := [reserveNode, compareNode, restoreLessNode, restoreNotLessNode,
    packLessNode, packEqualNode, packGreaterNode, incrementNode], entry := reserveNode.reference}
/-- A single finite machine, independent of every runtime operand and result. -/
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

theorem graph_nodes_length : graph.nodes.length = 8 := rfl

private theorem reserve_mem : reserveNode ∈ graph.nodes := List.Mem.head _
private theorem compare_mem : compareNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem restoreLess_mem : restoreLessNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem restoreNotLess_mem : restoreNotLessNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem packLess_mem : packLessNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem packEqual_mem : packEqualNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
private theorem packGreater_mem : packGreaterNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
private theorem increment_mem : incrementNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem reserve_good : Good reserveMachine :=
  BuilderRegisterLessThan.graph_wellFormed.2.1 BuilderRegisterLessThan.reserveNode (List.Mem.head _)
private theorem comparison_good : Good BuilderRegionPairComparison.machine :=
  BuilderRegisterLessThan.graph_wellFormed.2.1 BuilderRegisterLessThan.compareNode
    (List.Mem.tail _ (List.Mem.head _))
private theorem restoration_good : Good BuilderRegionResidualRegisters.machine :=
  BuilderRegisterLessThan.graph_wellFormed.2.1 BuilderRegisterLessThan.restoreLessNode
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem pack_good (selected : List (BuilderRegisterPack.Field 3)) :
    Good (BuilderRegisterPack.machine selected 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct selected 0,
    BuilderRegisterPack.noRuleAtAccept selected 0, BuilderRegisterPack.noRuleAtReject selected 0,
    BuilderRegisterPack.acceptState_ne_rejectState selected 0⟩
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
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reserve_good
    · exact comparison_good
    · exact restoration_good
    · exact restoration_good
    · exact pack_good lessFields
    · exact pack_good residualFields
    · exact pack_good residualFields
    · exact increment_good
  · exact ⟨reserveNode, reserve_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨compareNode, compare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨restoreLessNode, restoreLess_mem, rfl, rfl⟩,
        ⟨restoreNotLessNode, restoreNotLess_mem, rfl, rfl⟩⟩
    · exact ⟨⟨packLessNode, packLess_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨packEqualNode, packEqual_mem, rfl, rfl⟩,
        ⟨packGreaterNode, packGreater_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨incrementNode, increment_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def outputTape (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  endTape (older ++ outputValues result) inside (outside.drop (allocatedCells result))
def continuationEntry : RawRouter.ComparisonResult → Endpoint
  | .less _ _ => .node restoreLessNode.reference
  | .equal _ | .greater _ _ => .node restoreNotLessNode.reference
def continuationSteps (result : RawRouter.ComparisonResult) : Nat :=
  restoreSteps result + 1 + packSteps result + 1 + extraSteps result
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
    (outputTape (RawRouter.compareResult 0 coordinate boundary) older inside outside)

private def copyTape (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkTape :=
  endTape (older ++ resultValues result ++ packedValues result) inside
    (outside.drop (resultBoundary result + copiedCoordinate result + 3))

private theorem packed_span (result : RawRouter.ComparisonResult) :
    (registerWord (packedValues result)).length = resultBoundary result + copiedCoordinate result + 2 := by
  simp only [packedValues, registerWord_length, List.length_cons, List.length_nil,
    List.sum_cons, List.sum_nil]
  omega

private theorem pack_run (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? (BuilderRegisterPack.machine (fields result) 0) (packSteps result)
      (workStartConfiguration (BuilderRegisterPack.machine (fields result) 0)
        (endTape (older ++ resultValues result) inside (outside.drop 1))) =
      some {
        state := (BuilderRegisterPack.machine (fields result) 0).acceptState
        tape := copyTape result older inside outside } := by
  have h := BuilderRegisterPack.workRunExact (fields result) 0 older (environment result) []
    inside (outside.drop 1) rfl
  have hDrop : (outside.drop 1).drop (registerWord (packedValues result)).length =
      outside.drop (resultBoundary result + copiedCoordinate result + 3) := by
    rw [List.drop_drop, packed_span] <;> congr 1 <;> omega
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    environment_ofFn, packedValues_eq, List.append_nil, hDrop, copyTape, packSteps] using h

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
      (resultTape result older inside outside) (outputTape result older inside outside) := by
  have hRestore := restore_run result older inside outside
  have hPack := pack_run result older inside outside
  cases result with
  | less matched rest =>
      have hTape : copyTape (.less matched rest) older inside outside =
          outputTape (.less matched rest) older inside outside := by
        simp only [copyTape, outputTape, outputValues, packedValues, allocatedCells,
          resultBoundary, copiedCoordinate, resultCoordinate, List.append_assoc]
      rw [hTape] at hPack
      have hP := AcceptPath.step packLessNode .accept (packSteps (.less matched rest))
        0 _ _ _ packLess_mem hPack (.terminal .accept _)
      have hR := AcceptPath.step restoreLessNode .accept (restoreSteps (.less matched rest))
        _ _ _ _ restoreLess_mem hRestore hP
      simpa only [continuationEntry, resultEndpoint, continuationSteps, extraSteps,
        Nat.add_zero, Nat.add_assoc] using hR
  | equal matched =>
      have hTape : copyTape (.equal matched) older inside outside =
          outputTape (.equal matched) older inside outside := by
        simp only [copyTape, outputTape, outputValues, packedValues, allocatedCells,
          resultBoundary, copiedCoordinate, resultCoordinate, List.append_assoc]
      rw [hTape] at hPack
      have hP := AcceptPath.step packEqualNode .reject (packSteps (.equal matched))
        0 _ _ _ packEqual_mem hPack (.terminal .reject _)
      have hR := AcceptPath.step restoreNotLessNode .reject (restoreSteps (.equal matched))
        _ _ _ _ restoreNotLess_mem hRestore hP
      simpa only [continuationEntry, resultEndpoint, continuationSteps, extraSteps,
        Nat.add_zero, Nat.add_assoc] using hR
  | greater matched rest =>
      have hIncrement :
          workRunExact? BuilderConstraintRegionAssembly.Increment.machine 2
            (workStartConfiguration BuilderConstraintRegionAssembly.Increment.machine
              (copyTape (.greater matched rest) older inside outside)) =
          some {
            state := BuilderConstraintRegionAssembly.Increment.machine.acceptState
            tape := outputTape (.greater matched rest) older inside outside } := by
        have h := BuilderConstraintRegionAssembly.Increment.workRunExact
          (older ++ resultValues (.greater matched rest) ++ [matched]) rest inside
          (outside.drop (matched + rest + 3))
        have hDrop : (outside.drop (matched + rest + 3)).drop 1 =
            outside.drop (matched + (rest + 1) + 3) := by
          rw [List.drop_drop] <;> congr 1 <;> omega
        simpa only [copyTape, outputTape, outputValues, packedValues, allocatedCells,
          resultBoundary, copiedCoordinate, resultCoordinate, List.append_assoc,
          List.cons_append, List.nil_append, hDrop] using h
      have hI := AcceptPath.step incrementNode .reject 2 0 _ _ _ increment_mem
        hIncrement (.terminal .reject _)
      have hP := AcceptPath.step packGreaterNode .reject (packSteps (.greater matched rest))
        _ _ _ _ packGreater_mem hPack hI
      have hR := AcceptPath.stepReject restoreNotLessNode .reject (restoreSteps (.greater matched rest))
        _ _ _ _ restoreNotLess_mem hRestore hP
      simpa only [continuationEntry, resultEndpoint, continuationSteps, extraSteps,
        Nat.add_zero, Nat.add_assoc] using hR

/-- Exact all-operand execution; the machine is fixed, not generated from a verdict. -/
theorem workRunExact (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary)
      (initialConfiguration coordinate boundary older inside outside) =
      some (finalConfiguration coordinate boundary older inside outside) := by
  have hReserve := BuilderRegisterLessThan.reserve_workRunExact boundary (older ++ [coordinate]) inside outside
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hReserve
  have hCompare := pair_run coordinate boundary older inside outside
  have hTail := continuation_path (RawRouter.compareResult 0 coordinate boundary) older inside outside
  have hPath : AcceptPath graph (.node compareNode.reference)
      (resultEndpoint (RawRouter.compareResult 0 coordinate boundary))
      (BuilderRegionPairComparison.workSteps coordinate boundary + 1 +
        continuationSteps (RawRouter.compareResult 0 coordinate boundary))
      (endTape (older ++ [coordinate, boundary]) inside (WorkSymbol.blank :: outside.drop 1))
      (outputTape (RawRouter.compareResult 0 coordinate boundary) older inside outside) := by
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
      coordinate < boundary :=
  BuilderRegisterLessThan.final_accept_iff coordinate boundary older inside outside

theorem final_reject_iff (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).state = machine.rejectState ↔
      boundary ≤ coordinate :=
  BuilderRegisterLessThan.final_reject_iff coordinate boundary older inside outside

theorem final_tape (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).tape =
      endTape (older ++ resultValues (RawRouter.compareResult 0 coordinate boundary) ++
        [boundary, if coordinate < boundary then coordinate else coordinate - boundary])
        inside (outside.drop (boundary +
          (if coordinate < boundary then coordinate else coordinate - boundary) + 3)) := by
  change outputTape (RawRouter.compareResult 0 coordinate boundary) older inside outside = _
  simp only [outputTape, outputValues, allocatedCells, resultBoundary_eq, resultCoordinate_eq,
    List.append_assoc]

theorem final_exterior (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).tape.left =
      outside.drop (boundary + (if coordinate < boundary then coordinate else coordinate - boundary) + 3) := by
  rw [final_tape]
  rfl

private theorem pair_span (first second : Nat) :
    (registerWord [first, second]).length = first + second + 2 := by
  simp only [registerWord_length, List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

private theorem workSteps_le_previous_and_pack (coordinate boundary : Nat) :
    workSteps coordinate boundary ≤ BuilderRegisterLessThan.workSteps coordinate boundary +
      packSteps (RawRouter.compareResult 0 coordinate boundary) + 3 := by
  have hExtra : extraSteps (RawRouter.compareResult 0 coordinate boundary) ≤ 3 := by
    cases RawRouter.compareResult 0 coordinate boundary <;> simp only [extraSteps] <;> decide
  simp only [workSteps, continuationSteps, BuilderRegisterLessThan.workSteps,
    BuilderRegisterLessThan.continuationSteps]
  omega

/-- Linear encoded register-span growth; includes the retained recovery scratch. -/
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 3) bound) (.constant 3)

/-- Primitive runtime, both copy operations, correction and graph bridges. -/
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegisterLessThan.rawTimePolynomial bound)
    (BuilderRegisterPack.rawTimePolynomial lessFields (.add bound (.constant 1)))) (.constant 18)

theorem source_polynomial_bounds (coordinate boundary : Nat) (older : List Nat)
    (bound : NatPolynomial) (inputLength : Nat)
    (hSpan : (registerWord (older ++ [coordinate, boundary])).length ≤ bound.eval inputLength) :
    (registerWord (older ++ outputValues (RawRouter.compareResult 0 coordinate boundary))).length ≤
        (spanPolynomial bound).eval inputLength ∧
      6 * workSteps coordinate boundary ≤ (rawTimePolynomial bound).eval inputLength := by
  rw [registerWord_append, List.length_append, pair_span] at hSpan
  have hCoordinate : coordinate ≤ bound.eval inputLength := by omega
  have hBoundary : boundary ≤ bound.eval inputLength := by omega
  have hRestoreSpan :
      (registerWord (resultValues (RawRouter.compareResult 0 coordinate boundary))).length =
        coordinate + boundary + 3 :=
    BuilderRegisterLessThan.clearedSpan_eq coordinate boundary
  have hRestored :
      (registerWord (older ++ List.ofFn (environment (RawRouter.compareResult 0 coordinate boundary)) ++ [])).length ≤
        (NatPolynomial.add bound (.constant 1)).eval inputLength := by
    rw [List.append_nil, environment_ofFn, registerWord_append, List.length_append, hRestoreSpan]
    simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  have hPack := BuilderRegisterPack.source_polynomial_bounds
    (fields (RawRouter.compareResult 0 coordinate boundary)) (.add bound (.constant 1))
    inputLength older (environment (RawRouter.compareResult 0 coordinate boundary)) [] hRestored
  have hPackPolynomial :
      BuilderRegisterPack.rawTimePolynomial (fields (RawRouter.compareResult 0 coordinate boundary))
          (.add bound (.constant 1)) =
        BuilderRegisterPack.rawTimePolynomial lessFields (.add bound (.constant 1)) := by
    cases RawRouter.compareResult 0 coordinate boundary <;> rfl
  have hPackTime : 6 * packSteps (RawRouter.compareResult 0 coordinate boundary) ≤
      (BuilderRegisterPack.rawTimePolynomial lessFields (.add bound (.constant 1))).eval inputLength := by
    simpa only [packSteps, hPackPolynomial] using hPack.2
  have hBaseTime := BuilderRegisterLessThan.raw_time_polynomial coordinate boundary bound inputLength
    hCoordinate hBoundary
  have hWork := workSteps_le_previous_and_pack coordinate boundary
  have hNext : resultCoordinate (RawRouter.compareResult 0 coordinate boundary) ≤ coordinate := by
    rw [resultCoordinate_eq]
    split <;> omega
  constructor
  · simp only [outputValues, registerWord_append, List.length_append, hRestoreSpan,
      pair_span, resultBoundary_eq, spanPolynomial, NatPolynomial.eval_mul,
      NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega
  · simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderRegisterCompareResidual
