/-
Copyright (c) 2026 PNP Labs.

Complete physical stay/left/right movement of a source-selected control head.
One fixed finite graph reads the written direction tag and unary operands,
handles both tape edges, and appends exactly one result register. Its branch
and moved position are not supplied as executable answers.
-/

import PNP.Concrete.CookLevinBuilderControlActionSource
import PNP.Concrete.CookLevinBuilderRegisterLessThan

namespace PNP.Concrete.CookLevin.BuilderRegisterHeadMove

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

abbrev moveCode := BuilderControlActionSource.moveCode

/-- Canonical numeric specification; the program below does not receive this answer. -/
def moved (width position : Nat) : HeadMove → Nat
  | .stay => position
  | .left => position - 1
  | .right => if position + 1 < width then position + 1 else position

theorem moved_eq_canonical {width : Nat} (position : Fin width) (move : HeadMove) :
    moved width position.val move = (VerifierTableauProblem.movePosition position move).val := by
  cases move with
  | stay => rfl
  | left => rfl
  | right =>
      by_cases hNext : position.val + 1 < width
      · simp only [moved, VerifierTableauProblem.movePosition, if_pos hNext, dif_pos hNext]
      · simp only [moved, VerifierTableauProblem.movePosition, if_neg hNext, dif_neg hNext]

theorem moved_lt {width : Nat} (position : Fin width) (move : HeadMove) :
    moved width position.val move < width := by
  rw [moved_eq_canonical]
  exact (VerifierTableauProblem.movePosition position move).isLt

theorem moveCode_le (move : HeadMove) : moveCode move ≤ 2 := by
  cases move <;> decide

theorem moved_le (width position : Nat) (move : HeadMove) : moved width position move ≤ position + 1 := by
  cases move with
  | stay => simp only [moved]; omega
  | left => simp only [moved]; omega
  | right =>
      by_cases hNext : position + 1 < width
      · simp only [moved, if_pos hNext]; omega
      · simp only [moved, if_neg hNext]; omega

def rightDecrementNode : Node :=
  {name := 12, program := BuilderRegisterCountdownControl.decrement,
   onAccept := .accept, onReject := .dead}
def compareNode : Node :=
  {name := 11, program := BuilderRegisterLessThan.machine,
   onAccept := .accept, onReject := .node rightDecrementNode.reference}
def copyWidthNode : Node :=
  {name := 10, program := RegisterCopy.machine 4,
   onAccept := .node compareNode.reference, onReject := .dead}
def copyCandidateNode : Node :=
  {name := 9, program := RegisterCopy.machine 0,
   onAccept := .node copyWidthNode.reference, onReject := .dead}
def incrementNode : Node :=
  {name := 8, program := BuilderConstraintRegionAssembly.Increment.machine,
   onAccept := .node copyCandidateNode.reference, onReject := .dead}
def rightCopyNode : Node :=
  {name := 7, program := RegisterCopy.machine 1,
   onAccept := .node incrementNode.reference, onReject := .dead}
def leftDecrementNode : Node :=
  {name := 6, program := BuilderRegisterCountdownControl.decrement,
   onAccept := .accept, onReject := .dead}
def zeroNode : Node :=
  {name := 5, program := BuilderUnaryTagMatch.machine 0,
   onAccept := .accept, onReject := .node leftDecrementNode.reference}
def leftCopyNode : Node :=
  {name := 4, program := RegisterCopy.machine 1,
   onAccept := .node zeroNode.reference, onReject := .dead}
def stayCopyNode : Node :=
  {name := 3, program := RegisterCopy.machine 1, onAccept := .accept, onReject := .dead}
def rightTestNode : Node :=
  {name := 2, program := BuilderUnaryTagMatch.machine 2,
   onAccept := .node rightCopyNode.reference, onReject := .reject}
def leftTestNode : Node :=
  {name := 1, program := BuilderUnaryTagMatch.machine 1,
   onAccept := .node leftCopyNode.reference, onReject := .node rightTestNode.reference}
def stayTestNode : Node :=
  {name := 0, program := BuilderUnaryTagMatch.machine 0,
   onAccept := .node stayCopyNode.reference, onReject := .node leftTestNode.reference}

def graph : Graph :=
  {nodes := [stayTestNode, leftTestNode, rightTestNode, stayCopyNode, leftCopyNode, zeroNode,
    leftDecrementNode, rightCopyNode, incrementNode, copyCandidateNode, copyWidthNode,
    compareNode, rightDecrementNode], entry := stayTestNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

private theorem stayTest_mem : stayTestNode ∈ graph.nodes := List.Mem.head _
private theorem leftTest_mem : leftTestNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)
private theorem rightTest_mem : rightTestNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem stayCopy_mem : stayCopyNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem leftCopy_mem : leftCopyNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
private theorem zero_mem : zeroNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
private theorem leftDecrement_mem : leftDecrementNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.head _))))))
private theorem rightCopy_mem : rightCopyNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
private theorem increment_mem : incrementNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
private theorem copyCandidate_mem : copyCandidateNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
private theorem copyWidth_mem : copyWidthNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.head _))))))))))
private theorem compare_mem : compareNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
private theorem rightDecrement_mem : rightDecrementNode ∈ graph.nodes :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem test_good (tag : Nat) : Good (BuilderUnaryTagMatch.machine tag) :=
  ⟨BuilderUnaryTagMatch.rules_pairwise_query_distinct tag,
    BuilderUnaryTagMatch.noRuleAtAccept tag, BuilderUnaryTagMatch.noRuleAtReject tag,
    BuilderUnaryTagMatch.acceptState_ne_rejectState tag⟩
private theorem decrement_good : Good BuilderRegisterCountdownControl.decrement :=
  BuilderRegisterCountdownControl.decrement_control
private theorem comparison_good : Good BuilderRegisterLessThan.machine :=
  ⟨BuilderRegisterLessThan.rules_pairwise_query_distinct, BuilderRegisterLessThan.noRuleAtAccept,
    BuilderRegisterLessThan.noRuleAtReject, BuilderRegisterLessThan.acceptState_ne_rejectState⟩
private theorem copy_good (offset : Nat) : Good (RegisterCopy.machine offset) := by
  refine ⟨RegisterCopy.rules_pairwise_query_distinct offset, ?_, ?_,
    RegisterCopy.machine_acceptState_ne_rejectState offset⟩
  · intro rule hMem
    exact Nat.ne_of_lt (RegisterCopy.rule_source_lt_acceptState offset rule hMem)
  · intro rule hMem
    have hLt := RegisterCopy.rule_source_lt_acceptState offset rule hMem
    rw [RegisterCopy.machine_acceptState] at hLt
    rw [RegisterCopy.machine_rejectState]
    omega
private theorem increment_good : Good BuilderConstraintRegionAssembly.Increment.machine := by
  refine ⟨BuilderConstraintRegionAssembly.Increment.rules_pairwise_query_distinct,
    BuilderConstraintRegionAssembly.Increment.noRuleAtAccept, ?_,
    BuilderConstraintRegionAssembly.Increment.acceptState_ne_rejectState⟩
  intro rule hMem
  decide +revert

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun left right : Nat => left ≠ right) := by
    change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact test_good 0
    · exact test_good 1
    · exact test_good 2
    · exact copy_good 1
    · exact copy_good 1
    · exact test_good 0
    · exact decrement_good
    · exact copy_good 1
    · exact increment_good
    · exact copy_good 0
    · exact copy_good 4
    · exact comparison_good
    · exact decrement_good
  · exact ⟨stayTestNode, stayTest_mem, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨stayCopyNode, stayCopy_mem, rfl, rfl⟩, ⟨leftTestNode, leftTest_mem, rfl, rfl⟩⟩
    · exact ⟨⟨leftCopyNode, leftCopy_mem, rfl, rfl⟩, ⟨rightTestNode, rightTest_mem, rfl, rfl⟩⟩
    · exact ⟨⟨rightCopyNode, rightCopy_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨zeroNode, zero_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, ⟨leftDecrementNode, leftDecrement_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨incrementNode, increment_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨copyCandidateNode, copyCandidate_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨copyWidthNode, copyWidth_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨compareNode, compare_mem, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, ⟨rightDecrementNode, rightDecrement_mem, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩

def inputValues (width position : Nat) (move : HeadMove) : List Nat :=
  [width, position, moveCode move]
def finalValues (width position : Nat) (move : HeadMove) : List Nat :=
  [width, position, moveCode move, moved width position move]

theorem finalValues_length (width position : Nat) (move : HeadMove) :
    (finalValues width position move).length = 4 := rfl

def copiedOutside (position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  outside.drop (position + 1)
def candidateOutside (position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  (copiedOutside position outside).drop 1
def pairOutside (width position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  ((candidateOutside position outside).drop (position + 2)).drop (width + 1)
def comparedOutside (width position : Nat) (outside : List WorkSymbol) : List WorkSymbol :=
  List.replicate ((position + 1) + width + 3) WorkSymbol.blank ++
    (pairOutside width position outside).drop 1

def finalOutside (width position : Nat) (move : HeadMove) (outside : List WorkSymbol) :
    List WorkSymbol :=
  match move with
  | .stay => copiedOutside position outside
  | .left => if position = 0 then copiedOutside position outside
      else WorkSymbol.blank :: copiedOutside position outside
  | .right => if position + 1 < width then comparedOutside width position outside
      else WorkSymbol.blank :: comparedOutside width position outside

theorem comparedOutside_eq (width position : Nat) (outside : List WorkSymbol) :
    comparedOutside width position outside =
      List.replicate (position + width + 4) WorkSymbol.blank ++
        outside.drop (2 * position + width + 6) := by
  simp only [comparedOutside, pairOutside, candidateOutside, copiedOutside, List.drop_drop]
  congr 2 <;> omega

def copySteps (position code : Nat) : Nat := RegisterCopy.steps [code] position
def leftContinuationSteps (position : Nat) : Nat :=
  BuilderUnaryTagMatch.workSteps 0 position + 1 + (if position = 0 then 0 else 2 + 1)
def leftSteps (position : Nat) : Nat := copySteps position 1 + 1 + leftContinuationSteps position
def rightComparisonSteps (width position : Nat) : Nat :=
  BuilderRegisterLessThan.workSteps (position + 1) width + 1 +
    (if position + 1 < width then 0 else 2 + 1)
def rightContinuationSteps (width position : Nat) : Nat :=
  RegisterCopy.steps [] (position + 1) + 1 +
    (RegisterCopy.steps [position, 2, position + 1, position + 1] width + 1 +
      rightComparisonSteps width position)
def rightSteps (width position : Nat) : Nat :=
  copySteps position 2 + 1 + (2 + 1 + rightContinuationSteps width position)
def workSteps (width position : Nat) : HeadMove → Nat
  | .stay => BuilderUnaryTagMatch.workSteps 0 0 + 1 + (copySteps position 0 + 1)
  | .left => BuilderUnaryTagMatch.workSteps 0 1 + 1 +
      (BuilderUnaryTagMatch.workSteps 1 1 + 1 + leftSteps position)
  | .right => BuilderUnaryTagMatch.workSteps 0 2 + 1 +
      (BuilderUnaryTagMatch.workSteps 1 2 + 1 +
        (BuilderUnaryTagMatch.workSteps 2 2 + 1 + rightSteps width position))

def initialConfiguration (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ inputValues width position move) inside outside)
def finalConfiguration (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  {
    state := machine.acceptState
    tape := endTape (older ++ finalValues width position move) inside
     (finalOutside width position move outside)}

private theorem copy_position (width position code : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? (RegisterCopy.machine 1) (copySteps position code)
      (workStartConfiguration (RegisterCopy.machine 1) (endTape (older ++ [width, position, code]) inside outside)) =
      some {
        state := (RegisterCopy.machine 1).acceptState
        tape := endTape (older ++ [width, position, code, position]) inside (copiedOutside position outside) } := by
  simpa only [copySteps, copiedOutside, List.append_assoc, List.cons_append, List.nil_append] using
    BuilderRegionComparisonOperands.copy_workRunExact 1 (older ++ [width]) [code] position inside outside rfl

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

private theorem stay_path (width position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath graph (.node stayCopyNode.reference) .accept (copySteps position 0 + 1)
      (endTape (older ++ [width, position, 0]) inside outside)
      (endTape (older ++ finalValues width position .stay) inside (finalOutside width position .stay outside)) := by
  have hCopy := copy_position width position 0 older inside outside
  have hPath := AcceptPath.step stayCopyNode .accept _ 0 _ _ _ stayCopy_mem hCopy (.terminal .accept _)
  simpa only [Nat.add_zero, finalValues, finalOutside, moved, moveCode,
    BuilderControlActionSource.moveCode] using hPath

private theorem left_continuation (width position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (.node zeroNode.reference) .accept (leftContinuationSteps position)
      (endTape (older ++ [width, position, 1, position]) inside (copiedOutside position outside))
      (endTape (older ++ finalValues width position .left) inside (finalOutside width position .left outside)) := by
  cases position with
  | zero =>
      have hTest := BuilderUnaryTagMatch.accept_workRunExact 0 (older ++ [width, 0, 1])
        inside (copiedOutside 0 outside)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hTest
      have hPath := AcceptPath.step zeroNode .accept _ 0 _ _ _ zero_mem hTest (.terminal .accept _)
      simpa only [leftContinuationSteps, finalValues, finalOutside, moved, moveCode,
        BuilderControlActionSource.moveCode, if_pos rfl, ite_true, Nat.zero_sub] using hPath
  | succ position =>
      have hTest := BuilderUnaryTagMatch.reject_workRunExact 0 (position + 1)
        (older ++ [width, position + 1, 1]) inside (copiedOutside (position + 1) outside) (by omega)
      have hDecrement := BuilderRegisterLessThan.decrement_workRunExact position
        (older ++ [width, position + 1, 1]) inside (copiedOutside (position + 1) outside)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hTest hDecrement
      have hD := AcceptPath.step leftDecrementNode .accept 2 0 _ _ _ leftDecrement_mem hDecrement (.terminal .accept _)
      have hPath := AcceptPath.stepReject zeroNode .accept _ _ _ _ _ zero_mem hTest hD
      have hNonzero : position + 1 ≠ 0 := by omega
      simpa only [leftContinuationSteps, finalValues, finalOutside, moved, moveCode,
        BuilderControlActionSource.moveCode, if_neg hNonzero, Nat.add_sub_cancel, Nat.add_zero] using hPath

private theorem left_path (width position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath graph (.node leftCopyNode.reference) .accept (leftSteps position)
      (endTape (older ++ [width, position, 1]) inside outside)
      (endTape (older ++ finalValues width position .left) inside (finalOutside width position .left outside)) :=
  AcceptPath.step leftCopyNode .accept _ _ _ _ _ leftCopy_mem
    (copy_position width position 1 older inside outside) (left_continuation width position older inside outside)

private theorem right_comparison (width position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (.node compareNode.reference) .accept (rightComparisonSteps width position)
      (endTape (older ++ [width, position, 2, position + 1, position + 1, width]) inside
        (pairOutside width position outside))
      (endTape (older ++ finalValues width position .right) inside (finalOutside width position .right outside)) := by
  let saved := older ++ [width, position, 2, position + 1]
  have hCompare := BuilderRegisterLessThan.workRunExact (position + 1) width saved inside
    (pairOutside width position outside)
  have hTape :
      (BuilderRegisterLessThan.finalConfiguration (position + 1) width saved inside
        (pairOutside width position outside)).tape =
      endTape saved inside (comparedOutside width position outside) := rfl
  by_cases hNext : position + 1 < width
  · have hState := (BuilderRegisterLessThan.final_accept_iff (position + 1) width saved inside
      (pairOutside width position outside)).2 hNext
    rw [configuration_eq_of_fields _ _ _ hState hTape] at hCompare
    simp only [BuilderRegisterLessThan.initialConfiguration, saved, List.append_assoc,
      List.cons_append, List.nil_append] at hCompare
    have hPath := AcceptPath.step compareNode .accept _ 0 _ _ _ compare_mem hCompare (.terminal .accept _)
    simpa only [rightComparisonSteps, finalValues, finalOutside, moved, moveCode,
      BuilderControlActionSource.moveCode, if_pos hNext] using hPath
  · have hState := (BuilderRegisterLessThan.final_reject_iff (position + 1) width saved inside
      (pairOutside width position outside)).2 (by omega)
    rw [configuration_eq_of_fields _ _ _ hState hTape] at hCompare
    simp only [BuilderRegisterLessThan.initialConfiguration, saved, List.append_assoc,
      List.cons_append, List.nil_append] at hCompare
    have hDecrement := BuilderRegisterLessThan.decrement_workRunExact position
      (older ++ [width, position, 2]) inside (comparedOutside width position outside)
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hDecrement
    have hD := AcceptPath.step rightDecrementNode .accept 2 0 _ _ _ rightDecrement_mem
      hDecrement (.terminal .accept _)
    have hPath := AcceptPath.stepReject compareNode .accept _ _ _ _ _ compare_mem hCompare hD
    simpa only [rightComparisonSteps, finalValues, finalOutside, moved, moveCode,
      BuilderControlActionSource.moveCode, if_neg hNext, Nat.add_zero] using hPath

private theorem right_continuation (width position : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    AcceptPath graph (.node copyCandidateNode.reference) .accept (rightContinuationSteps width position)
      (endTape (older ++ [width, position, 2, position + 1]) inside (candidateOutside position outside))
      (endTape (older ++ finalValues width position .right) inside (finalOutside width position .right outside)) := by
  have hCandidate := BuilderRegionComparisonOperands.copy_workRunExact 0
    (older ++ [width, position, 2]) [] (position + 1) inside (candidateOutside position outside) rfl
  have hWidth := BuilderRegionComparisonOperands.copy_workRunExact 4 older
    [position, 2, position + 1, position + 1] width inside
    ((candidateOutside position outside).drop (position + 2)) rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at hCandidate hWidth
  have hW := AcceptPath.step copyWidthNode .accept _ _ _ _ _ copyWidth_mem hWidth
    (right_comparison width position older inside outside)
  exact AcceptPath.step copyCandidateNode .accept _ _ _ _ _ copyCandidate_mem hCandidate hW

private theorem right_path (width position : Nat) (older : List Nat) (inside outside : List WorkSymbol) :
    AcceptPath graph (.node rightCopyNode.reference) .accept (rightSteps width position)
      (endTape (older ++ [width, position, 2]) inside outside)
      (endTape (older ++ finalValues width position .right) inside (finalOutside width position .right outside)) := by
  have hIncrement := BuilderConstraintRegionAssembly.Increment.workRunExact
    (older ++ [width, position, 2]) position inside (copiedOutside position outside)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hIncrement
  have hI := AcceptPath.step incrementNode .accept 2 _ _ _ _ increment_mem hIncrement
    (right_continuation width position older inside outside)
  exact AcceptPath.step rightCopyNode .accept _ _ _ _ _ rightCopy_mem
    (copy_position width position 2 older inside outside) hI

/-- The direction is read by literal tag tests; all widths and positions have exact execution. -/
theorem workRunExact (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? machine (workSteps width position move)
      (initialConfiguration width position move older inside outside) =
      some (finalConfiguration width position move older inside outside) := by
  have hPath : AcceptPath graph (.node stayTestNode.reference) .accept (workSteps width position move)
      (endTape (older ++ inputValues width position move) inside outside)
      (endTape (older ++ finalValues width position move) inside (finalOutside width position move outside)) := by
    cases move with
    | stay =>
        have hTest := BuilderUnaryTagMatch.accept_workRunExact 0 (older ++ [width, position]) inside outside
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hTest
        exact AcceptPath.step stayTestNode .accept _ _ _ _ _ stayTest_mem hTest
          (stay_path width position older inside outside)
    | left =>
        have hStay := BuilderUnaryTagMatch.reject_workRunExact 0 1 (older ++ [width, position]) inside outside (by decide)
        have hLeft := BuilderUnaryTagMatch.accept_workRunExact 1 (older ++ [width, position]) inside outside
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hStay hLeft
        have hLeftPath := AcceptPath.step leftTestNode .accept _ _ _ _ _ leftTest_mem hLeft
          (left_path width position older inside outside)
        exact AcceptPath.stepReject stayTestNode .accept _ _ _ _ _ stayTest_mem hStay hLeftPath
    | right =>
        have hStay := BuilderUnaryTagMatch.reject_workRunExact 0 2 (older ++ [width, position]) inside outside (by decide)
        have hLeft := BuilderUnaryTagMatch.reject_workRunExact 1 2 (older ++ [width, position]) inside outside (by decide)
        have hRight := BuilderUnaryTagMatch.accept_workRunExact 2 (older ++ [width, position]) inside outside
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hStay hLeft hRight
        have hRightPath := AcceptPath.step rightTestNode .accept _ _ _ _ _ rightTest_mem hRight
          (right_path width position older inside outside)
        have hLeftPath := AcceptPath.stepReject leftTestNode .accept _ _ _ _ _ leftTest_mem hLeft hRightPath
        exact AcceptPath.stepReject stayTestNode .accept _ _ _ _ _ stayTest_mem hStay hLeftPath
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hPath
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node stayTestNode.reference) tape =
        workStartConfiguration machine tape := rfl
  rw [hStart] at h
  exact h

theorem run_compile_exact (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps width position move)
      (encodeWorkConfiguration (initialConfiguration width position move older inside outside)) =
      encodeWorkConfiguration (finalConfiguration width position move older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact width position move older inside outside)

def invalidSteps (code : Nat) : Nat :=
  BuilderUnaryTagMatch.workSteps 0 code + 1 +
    (BuilderUnaryTagMatch.workSteps 1 code + 1 + (BuilderUnaryTagMatch.workSteps 2 code + 1))

theorem invalid_workRunExact (width position code : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) (hInvalid : code ≠ 0 ∧ code ≠ 1 ∧ code ≠ 2) :
    workRunExact? machine (invalidSteps code)
      (workStartConfiguration machine (endTape (older ++ [width, position, code]) inside outside)) =
      some {
        state := machine.rejectState
        tape := endTape (older ++ [width, position, code]) inside outside } := by
  have hStay := BuilderUnaryTagMatch.reject_workRunExact 0 code (older ++ [width, position]) inside outside hInvalid.1
  have hLeft := BuilderUnaryTagMatch.reject_workRunExact 1 code (older ++ [width, position]) inside outside hInvalid.2.1
  have hRight := BuilderUnaryTagMatch.reject_workRunExact 2 code (older ++ [width, position]) inside outside hInvalid.2.2
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hStay hLeft hRight
  have hR := AcceptPath.stepReject rightTestNode .reject _ 0 _ _ _ rightTest_mem hRight (.terminal .reject _)
  have hL := AcceptPath.stepReject leftTestNode .reject _ _ _ _ _ leftTest_mem hLeft hR
  have hS := AcceptPath.stepReject stayTestNode .reject _ _ _ _ _ stayTest_mem hStay hL
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hS
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node stayTestNode.reference) tape =
        workStartConfiguration machine tape := rfl
  rw [hStart] at h
  have hReject (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .reject tape =
        {state := machine.rejectState, tape := tape} := rfl
  rw [hReject] at h
  simpa only [machine, invalidSteps, Nat.add_zero] using h

theorem final_inside_preserved (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration width position move older inside outside).tape.right =
      (registerWord (finalValues width position move)).reverse ++ ((registerWord older).reverse ++ inside) := by
  simp only [finalConfiguration, endTape, registerWord_append, List.reverse_append, List.append_assoc]

theorem final_exterior_accounted (width position : Nat) (move : HeadMove) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration width position move older inside outside).tape.left =
      finalOutside width position move outside := rfl

def copyBound (bound : Nat) : Nat :=
  4 * (3 * bound + 9) * (3 * bound + 9) + 9 * (3 * bound + 9) + 5

private theorem copy_steps_le (position code bound : Nat) (hp : position ≤ bound) (hc : code ≤ 2) :
    copySteps position code ≤ copyBound bound := by
  have h := RegisterCopy.steps_le [code] position (3 * bound + 8) (by omega)
    (by simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]; omega)
  simpa only [copySteps, copyBound, Nat.add_assoc] using h

private theorem candidate_steps_le (position bound : Nat) (hp : position ≤ bound) :
    RegisterCopy.steps [] (position + 1) ≤ copyBound bound := by
  have h := RegisterCopy.steps_le [] (position + 1) (3 * bound + 8) (by omega)
    (by simp only [List.length_nil, List.sum_nil]; omega)
  simpa only [copyBound, Nat.add_assoc] using h

private theorem width_steps_le (width position bound : Nat) (hw : width ≤ bound) (hp : position ≤ bound) :
    RegisterCopy.steps [position, 2, position + 1, position + 1] width ≤ copyBound bound := by
  have h := RegisterCopy.steps_le [position, 2, position + 1, position + 1] width (3 * bound + 8) (by omega)
    (by simp only [List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]; omega)
  simpa only [copyBound, Nat.add_assoc] using h

def workBound (bound : Nat) : Nat :=
  3 * copyBound bound + BuilderRegisterLessThan.workBound (bound + 1) + 28

theorem workSteps_le (width position bound : Nat) (move : HeadMove) (hw : width ≤ bound) (hp : position ≤ bound) :
    workSteps width position move ≤ workBound bound := by
  have hC0 := copy_steps_le position 0 bound hp (by decide)
  have hC1 := copy_steps_le position 1 bound hp (by decide)
  have hC2 := copy_steps_le position 2 bound hp (by decide)
  have hCandidate := candidate_steps_le position bound hp
  have hWidth := width_steps_le width position bound hw hp
  have hCompare := BuilderRegisterLessThan.workSteps_le (position + 1) width (bound + 1) (by omega) (by omega)
  have hZero := BuilderUnaryTagMatch.workSteps_le 0 position
  have hT00 : BuilderUnaryTagMatch.workSteps 0 0 = 3 := rfl
  have hT01 : BuilderUnaryTagMatch.workSteps 0 1 = 3 := rfl
  have hT11 : BuilderUnaryTagMatch.workSteps 1 1 = 5 := rfl
  have hT02 : BuilderUnaryTagMatch.workSteps 0 2 = 3 := rfl
  have hT12 : BuilderUnaryTagMatch.workSteps 1 2 = 5 := rfl
  have hT22 : BuilderUnaryTagMatch.workSteps 2 2 = 7 := rfl
  cases move with
  | stay =>
      simp only [workSteps, hT00, workBound]
      omega
  | left =>
      simp only [workSteps, leftSteps, leftContinuationSteps, hT01, hT11, workBound]
      split <;> omega
  | right =>
      simp only [workSteps, rightSteps, rightContinuationSteps, rightComparisonSteps, hT02, hT12, hT22, workBound]
      split <;> omega

def copyPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add
    (.add
      (.mul (.mul (.constant 4) (.add (.mul (.constant 3) bound) (.constant 9)))
        (.add (.mul (.constant 3) bound) (.constant 9)))
      (.mul (.constant 9) (.add (.mul (.constant 3) bound) (.constant 9))))
    (.constant 5)

theorem copyPolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (copyPolynomial bound).eval input = copyBound (bound.eval input) := rfl

def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.add (.mul (.constant 18) (copyPolynomial bound))
    (BuilderRegisterLessThan.rawTimePolynomial (.add bound (.constant 1)))) (.constant 168)

theorem rawTimePolynomial_eval (bound : NatPolynomial) (input : Nat) :
    (rawTimePolynomial bound).eval input = 6 * workBound (bound.eval input) := by
  simp only [rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_mul,
    NatPolynomial.eval_constant, copyPolynomial_eval, BuilderRegisterLessThan.rawTimePolynomial_eval, workBound]
  omega

theorem raw_time_polynomial (width position : Nat) (move : HeadMove) (bound : NatPolynomial) (input : Nat)
    (hw : width ≤ bound.eval input) (hp : position ≤ bound.eval input) :
    6 * workSteps width position move ≤ (rawTimePolynomial bound).eval input := by
  rw [rawTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6 (workSteps_le width position (bound.eval input) move hw hp)

theorem output_span (width position : Nat) (move : HeadMove) (older : List Nat) :
    (registerWord (older ++ finalValues width position move)).length =
      (registerWord (older ++ inputValues width position move)).length + moved width position move + 1 := by
  simp only [registerWord_length, finalValues, inputValues, List.length_append, List.length_cons,
    List.length_nil, List.sum_append, List.sum_cons, List.sum_nil]
  omega

def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (.mul (.constant 2) bound) (.constant 2)

/-- Polynomial work and retained span follow from the actual encoded register frame. -/
theorem source_polynomial_bounds (width position : Nat) (move : HeadMove) (older : List Nat)
    (bound : NatPolynomial) (input : Nat)
    (hInput : (registerWord (older ++ inputValues width position move)).length ≤ bound.eval input) :
    (registerWord (older ++ finalValues width position move)).length ≤ (spanPolynomial bound).eval input ∧
      6 * workSteps width position move ≤ (rawTimePolynomial bound).eval input := by
  have hFields := hInput
  simp only [registerWord_length, inputValues, List.length_append, List.length_cons,
    List.length_nil, List.sum_append, List.sum_cons, List.sum_nil] at hFields
  have hw : width ≤ bound.eval input := by omega
  have hp : position ≤ bound.eval input := by omega
  refine ⟨?_, raw_time_polynomial width position move bound input hw hp⟩
  rw [output_span]
  have hMoved := moved_le width position move
  simp only [spanPolynomial, NatPolynomial.eval]
  omega

theorem finalOutside_length_le (width position : Nat) (move : HeadMove) (outside : List WorkSymbol) :
    (finalOutside width position move outside).length ≤ outside.length + position + width + 5 := by
  have hCopy : (copiedOutside position outside).length ≤ outside.length := by
    simp only [copiedOutside, List.length_drop]
    omega
  have hPair : (pairOutside width position outside).length ≤ outside.length := by
    simp only [pairOutside, candidateOutside, copiedOutside, List.drop_drop, List.length_drop]
    omega
  have hDrop : ((pairOutside width position outside).drop 1).length ≤ outside.length := by
    simp only [List.length_drop]
    omega
  have hCompare : (comparedOutside width position outside).length ≤
      ((position + 1) + width + 3) + outside.length := by
    simp only [comparedOutside, List.length_append, List.length_replicate]
    omega
  cases move with
  | stay => simp only [finalOutside]; omega
  | left =>
      by_cases hZero : position = 0
      · simp only [finalOutside, if_pos hZero]; omega
      · simp only [finalOutside, if_neg hZero, List.length_cons]; omega
  | right =>
      by_cases hNext : position + 1 < width
      · simp only [finalOutside, if_pos hNext]; omega
      · simp only [finalOutside, if_neg hNext, List.length_cons]; omega

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide

end PNP.Concrete.CookLevin.BuilderRegisterHeadMove
