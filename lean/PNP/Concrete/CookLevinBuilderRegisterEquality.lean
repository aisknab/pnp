/-
Copyright (c) 2026 PNP Labs.

One fixed equality dispatcher for two disposable unary registers. It uses the
physical less-than/residual selector and a zero-tag test, then actually erases
all comparison scratch. Equal and unequal outcomes restore the same retained
source frame, with every cleared exterior cell recorded explicitly.

This is runtime control for preservation padding, not a supplied equality
verdict, and not yet the complete preservation payload or formula builder.
-/

import PNP.Concrete.CookLevinBuilderRegisterErase
import PNP.Concrete.CookLevinBuilderRegionResidualOperands
import PNP.Concrete.CookLevinBuilderUnaryTagMatch

namespace PNP.Concrete.CookLevin.BuilderRegisterEquality

open BuilderUnaryPolynomial (registerWord registerWord_length)
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (LocalAcceptRun LocalRejectRun AcceptPath)

def eraseEqualNode : Node :=
  { name := 3, program := BuilderRegisterErase.machine 4, onAccept := .accept, onReject := .dead }

def eraseUnequalNode : Node :=
  { name := 2, program := BuilderRegisterErase.machine 4, onAccept := .reject, onReject := .dead }

def zeroNode : Node :=
  { name := 1, program := BuilderUnaryTagMatch.machine 0,
    onAccept := .node eraseEqualNode.reference, onReject := .node eraseUnequalNode.reference }

def compareNode : Node :=
  { name := 0, program := BuilderRegionResidualSelection.machine,
    onAccept := .node eraseUnequalNode.reference, onReject := .node zeroNode.reference }

def graph : Graph :=
  { nodes := [compareNode, zeroNode, eraseUnequalNode, eraseEqualNode], entry := compareNode.reference }

def machine : WorkMachine := WorkMachineProgramGraph.machine graph

private theorem compare_mem : compareNode ∈ graph.nodes := List.Mem.head _
private theorem zero_mem : zeroNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem eraseUnequal_mem : eraseUnequalNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem eraseEqual_mem : eraseEqualNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem compare_good : Good BuilderRegionResidualSelection.machine :=
  ⟨BuilderRegionResidualSelection.rules_pairwise_query_distinct,
    BuilderRegionResidualSelection.noRuleAtAccept, BuilderRegionResidualSelection.noRuleAtReject,
    BuilderRegionResidualSelection.acceptState_ne_rejectState⟩

private theorem zero_good : Good (BuilderUnaryTagMatch.machine 0) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct 0,
    BuilderUnaryTagMatch.noRuleAtAccept 0, BuilderUnaryTagMatch.noRuleAtReject 0,
    BuilderUnaryTagMatch.acceptState_ne_rejectState 0⟩

private theorem erase_good : Good (BuilderRegisterErase.machine 4) :=
  ⟨BuilderRegisterErase.rules_pairwise_query_distinct 4,
    BuilderRegisterErase.noRuleAtAccept 4, BuilderRegisterErase.noRuleAtReject 4,
    BuilderRegisterErase.acceptState_ne_rejectState 4⟩

theorem graph_wellFormed : graph.WellFormed := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact compare_good
    · exact zero_good
    · exact erase_good
    · exact erase_good
  · exact ⟨compareNode, compare_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl
    · exact ⟨⟨eraseUnequalNode, eraseUnequal_mem, rfl, rfl⟩, ⟨zeroNode, zero_mem, rfl, rfl⟩⟩
    · exact ⟨⟨eraseEqualNode, eraseEqual_mem, rfl, rfl⟩, ⟨eraseUnequalNode, eraseUnequal_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def resultEndpoint : RawRouter.ComparisonResult → Endpoint
  | .equal _ => .accept
  | .less _ _ | .greater _ _ => .reject

def clearedSpan (coordinate boundary : Nat) : Nat :=
  BuilderRegisterErase.clearedSpan
    (BuilderRegionResidualSelection.scratchValues (RawRouter.compareResult 0 coordinate boundary))

private def resultTape (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside : List WorkSymbol) : WorkTape :=
  endTape (older ++ BuilderRegionResidualSelection.scratchValues result) inside []

private def restoredTape (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside : List WorkSymbol) : WorkTape :=
  endTape older inside (List.replicate
    (BuilderRegisterErase.clearedSpan (BuilderRegionResidualSelection.scratchValues result)) .blank)

def continuationSteps (result : RawRouter.ComparisonResult) : Nat :=
  let eraseSteps := BuilderRegisterErase.workSteps (BuilderRegionResidualSelection.scratchValues result) + 1
  match result with
  | .less _ _ => eraseSteps
  | .equal _ | .greater _ _ =>
      BuilderUnaryTagMatch.workSteps 0 (BuilderRegionResidualSelection.resultCoordinate result) + 1 + eraseSteps

def workSteps (coordinate boundary : Nat) : Nat :=
  BuilderRegionResidualSelection.workSteps coordinate boundary + 1 +
    continuationSteps (RawRouter.compareResult 0 coordinate boundary)

def initialConfiguration (coordinate boundary : Nat) (older : List Nat)
    (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [coordinate, boundary]) inside [])

def finalConfiguration (coordinate boundary : Nat) (older : List Nat)
    (inside : List WorkSymbol) : WorkConfiguration :=
  WorkMachineProgramGraph.endpointConfiguration
    (resultEndpoint (RawRouter.compareResult 0 coordinate boundary))
    (endTape older inside (List.replicate (clearedSpan coordinate boundary) .blank))

private theorem erase_run (result : RawRouter.ComparisonResult) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? (BuilderRegisterErase.machine 4)
      (BuilderRegisterErase.workSteps (BuilderRegionResidualSelection.scratchValues result))
      (workStartConfiguration (BuilderRegisterErase.machine 4) (resultTape result older inside)) =
      some { state := (BuilderRegisterErase.machine 4).acceptState, tape := restoredTape result older inside } := by
  simpa only [BuilderRegisterErase.initialConfiguration, BuilderRegisterErase.finalConfiguration,
    resultTape, restoredTape, List.append_nil] using
    BuilderRegisterErase.workRunExact 4 older _ inside [] (BuilderRegionResidualSelection.scratchValues_length result)

private theorem erase_unequal_path (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside : List WorkSymbol) :
    AcceptPath graph (.node eraseUnequalNode.reference) .reject
      (BuilderRegisterErase.workSteps (BuilderRegionResidualSelection.scratchValues result) + 1)
      (resultTape result older inside) (restoredTape result older inside) := by
  have hLocal : LocalAcceptRun eraseUnequalNode
      (BuilderRegisterErase.workSteps (BuilderRegionResidualSelection.scratchValues result))
      (resultTape result older inside) (restoredTape result older inside) := erase_run result older inside
  simpa only [Nat.add_zero] using
    AcceptPath.step eraseUnequalNode .reject _ 0 _ _ _ eraseUnequal_mem hLocal
      (AcceptPath.terminal .reject (restoredTape result older inside))

private theorem erase_equal_path (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside : List WorkSymbol) :
    AcceptPath graph (.node eraseEqualNode.reference) .accept
      (BuilderRegisterErase.workSteps (BuilderRegionResidualSelection.scratchValues result) + 1)
      (resultTape result older inside) (restoredTape result older inside) := by
  have hLocal : LocalAcceptRun eraseEqualNode
      (BuilderRegisterErase.workSteps (BuilderRegionResidualSelection.scratchValues result))
      (resultTape result older inside) (restoredTape result older inside) := erase_run result older inside
  simpa only [Nat.add_zero] using
    AcceptPath.step eraseEqualNode .accept _ 0 _ _ _ eraseEqual_mem hLocal
      (AcceptPath.terminal .accept (restoredTape result older inside))

private def continuationEntry : RawRouter.ComparisonResult → Endpoint
  | .less _ _ => .node eraseUnequalNode.reference
  | .equal _ | .greater _ _ => .node zeroNode.reference

private theorem continuation_path (result : RawRouter.ComparisonResult) (older : List Nat)
    (inside : List WorkSymbol) :
    AcceptPath graph (continuationEntry result) (resultEndpoint result) (continuationSteps result)
      (resultTape result older inside) (restoredTape result older inside) := by
  cases result with
  | less matched rest => exact erase_unequal_path (.less matched rest) older inside
  | equal matched =>
      have hZero := BuilderUnaryTagMatch.accept_workRunExact 0
        (older ++ BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison (.equal matched)))
        inside []
      have hLocal : LocalAcceptRun zeroNode (BuilderUnaryTagMatch.workSteps 0 0)
          (resultTape (.equal matched) older inside) (resultTape (.equal matched) older inside) := by
        simpa only [LocalAcceptRun, zeroNode, workStartConfiguration, resultTape,
          BuilderRegionResidualSelection.scratchValues,
          BuilderRegionResidualSelection.resultCoordinate, List.append_assoc] using hZero
      exact AcceptPath.step zeroNode .accept _ _ _ _ _ zero_mem hLocal
        (erase_equal_path (.equal matched) older inside)
  | greater matched rest =>
      have hZero := BuilderUnaryTagMatch.reject_workRunExact 0 (rest + 1)
        (older ++ BuilderRegionResidualRegisters.restoredValues (BuilderRegionResidualRegisters.ofComparison (.greater matched rest)))
        inside [] (by omega)
      have hLocal : LocalRejectRun zeroNode (BuilderUnaryTagMatch.workSteps 0 (rest + 1))
          (resultTape (.greater matched rest) older inside) (resultTape (.greater matched rest) older inside) := by
        simpa only [LocalRejectRun, zeroNode, workStartConfiguration, resultTape,
          BuilderRegionResidualSelection.scratchValues,
          BuilderRegionResidualSelection.resultCoordinate, List.append_assoc] using hZero
      exact AcceptPath.stepReject zeroNode .reject _ _ _ _ _ zero_mem hLocal
        (erase_unequal_path (.greater matched rest) older inside)

/-- The runtime successor follows only the physical compare/zero outcomes. -/
theorem workRunExact (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary) (initialConfiguration coordinate boundary older inside) =
      some (finalConfiguration coordinate boundary older inside) := by
  have hCompare := BuilderRegionResidualSelection.workRunExact coordinate boundary older inside
  simp only [BuilderRegionResidualSelection.initialConfiguration, BuilderRegionResidualSelection.finalConfiguration] at hCompare
  have hTail := continuation_path (RawRouter.compareResult 0 coordinate boundary) older inside
  have hPath : AcceptPath graph (.node compareNode.reference)
      (resultEndpoint (RawRouter.compareResult 0 coordinate boundary)) (workSteps coordinate boundary)
      (endTape (older ++ [coordinate, boundary]) inside [])
      (restoredTape (RawRouter.compareResult 0 coordinate boundary) older inside) := by
    cases hResult : RawRouter.compareResult 0 coordinate boundary with
    | less matched rest =>
        simp only [workSteps, hResult] at hCompare hTail ⊢
        exact AcceptPath.step compareNode .reject _ _ _ _ _ compare_mem hCompare hTail
    | equal matched =>
        simp only [workSteps, hResult] at hCompare hTail ⊢
        exact AcceptPath.stepReject compareNode .accept _ _ _ _ _ compare_mem hCompare hTail
    | greater matched rest =>
        simp only [workSteps, hResult] at hCompare hTail ⊢
        exact AcceptPath.stepReject compareNode .reject _ _ _ _ _ compare_mem hCompare hTail
  exact WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath

theorem run_compile_exact (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration coordinate boundary older inside)) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact coordinate boundary older inside)

theorem final_accept_iff (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside).state = machine.acceptState ↔ coordinate = boundary := by
  have h := BuilderSourceRegisterRestore.compareResult_totals 0 coordinate boundary
  change WorkMachineProgramGraph.endpointState (resultEndpoint (RawRouter.compareResult 0 coordinate boundary)) =
    WorkMachineProgramGraph.globalAcceptState ↔ coordinate = boundary
  cases hResult : RawRouter.compareResult 0 coordinate boundary with
  | less matched rest =>
      simp only [hResult, BuilderSourceRegisterRestore.resultQuotient, BuilderSourceRegisterRestore.resultCount,
        Nat.zero_add] at h
      change (1 = 0 ↔ coordinate = boundary)
      exact iff_of_false (by decide) (by omega)
  | equal matched =>
      simp only [hResult, BuilderSourceRegisterRestore.resultQuotient, BuilderSourceRegisterRestore.resultCount,
        Nat.zero_add] at h
      change (0 = 0 ↔ coordinate = boundary)
      exact iff_of_true rfl (by omega)
  | greater matched rest =>
      simp only [hResult, BuilderSourceRegisterRestore.resultQuotient, BuilderSourceRegisterRestore.resultCount,
        Nat.zero_add] at h
      change (1 = 0 ↔ coordinate = boundary)
      exact iff_of_false (by decide) (by omega)

theorem final_reject_iff (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside).state = machine.rejectState ↔ coordinate ≠ boundary := by
  have h := BuilderSourceRegisterRestore.compareResult_totals 0 coordinate boundary
  change WorkMachineProgramGraph.endpointState (resultEndpoint (RawRouter.compareResult 0 coordinate boundary)) =
    WorkMachineProgramGraph.globalRejectState ↔ coordinate ≠ boundary
  cases hResult : RawRouter.compareResult 0 coordinate boundary with
  | less matched rest =>
      simp only [hResult, BuilderSourceRegisterRestore.resultQuotient, BuilderSourceRegisterRestore.resultCount,
        Nat.zero_add] at h
      change (1 = 1 ↔ coordinate ≠ boundary)
      exact iff_of_true rfl (by omega)
  | equal matched =>
      simp only [hResult, BuilderSourceRegisterRestore.resultQuotient, BuilderSourceRegisterRestore.resultCount,
        Nat.zero_add] at h
      change (0 = 1 ↔ coordinate ≠ boundary)
      exact iff_of_false (by decide) (by omega)
  | greater matched rest =>
      simp only [hResult, BuilderSourceRegisterRestore.resultQuotient, BuilderSourceRegisterRestore.resultCount,
        Nat.zero_add] at h
      change (1 = 1 ↔ coordinate ≠ boundary)
      exact iff_of_true rfl (by omega)

theorem final_tape (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside).tape =
      endTape older inside (List.replicate (clearedSpan coordinate boundary) .blank) := rfl

theorem clearedSpan_le (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    clearedSpan coordinate boundary ≤ 4 + 4 * bound := by
  have h := BuilderRegionResidualOperands.scratch_size_le coordinate boundary bound hCoordinate hBoundary
  simpa only [clearedSpan, BuilderRegisterErase.clearedSpan, registerWord_length] using h

private theorem continuationSteps_le (result : RawRouter.ComparisonResult) :
    continuationSteps result ≤ 3 * BuilderRegisterErase.clearedSpan
        (BuilderRegionResidualSelection.scratchValues result) + 5 := by
  have hErase := BuilderRegisterErase.workSteps_le (BuilderRegionResidualSelection.scratchValues result)
  have hTag := BuilderUnaryTagMatch.workSteps_le 0 (BuilderRegionResidualSelection.resultCoordinate result)
  cases result <;> simp only [continuationSteps] <;> omega

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (BuilderRegionResidualSelection.rawTimePolynomial bound) (.constant 6))
    (.mul (.constant 6) (.add (.mul (.constant 3) (.add (.constant 4) (.mul (.constant 4) bound))) (.constant 5)))

theorem source_polynomial_bounds (coordinate boundary inputLength : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval inputLength) (hBoundary : boundary ≤ bound.eval inputLength) :
    clearedSpan coordinate boundary ≤ 4 + 4 * bound.eval inputLength ∧
      6 * workSteps coordinate boundary ≤ (rawTimePolynomial bound).eval inputLength := by
  have hSpan := clearedSpan_le coordinate boundary (bound.eval inputLength) hCoordinate hBoundary
  have hCompare := BuilderRegionResidualSelection.rawTimePolynomial_le coordinate boundary bound inputLength hCoordinate hBoundary
  have hTail := continuationSteps_le (RawRouter.compareResult 0 coordinate boundary)
  refine ⟨hSpan, ?_⟩
  change continuationSteps (RawRouter.compareResult 0 coordinate boundary) ≤ 3 * clearedSpan coordinate boundary + 5 at hTail
  simp only [workSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  omega

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph

theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

end PNP.Concrete.CookLevin.BuilderRegisterEquality
