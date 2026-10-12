/-
Copyright (c) 2026 PNP Labs.

A closed finite-machine loop clearing a register of arbitrary length.
The register index is a compile-time constant; no length, termination, or
correctness witness is supplied to the executable machine. The proof preserves
the complete surrounding tape and accounts for every represented blank.
This is one register operation, not a compiler or whole normalizer theorem.
-/

import PNP.Concrete.BitRegisterOperations

namespace PNP.Concrete.BitRegister.Operation

open TapePrimitive Mutation WorkMachineProgramGraph
open PipelineStateNamespace

def clearHomeNode : Node :=
  { name := 3, program := home, onAccept := .accept, onReject := .reject }

def clearSeekNode (index : Nat) : Node :=
  { name := 2, program := seekFromBoundary index
    onAccept := .node ⟨0, 0⟩, onReject := .reject }

def clearEraseNode (index : Nat) : Node :=
  { name := 1, program := eraseCell
    onAccept := .node (clearSeekNode index).reference, onReject := .reject }

def clearTestNode (index : Nat) : Node :=
  Node.conditional 0 isEmpty clearHomeNode.reference (clearEraseNode index).reference

def clearGraph (index : Nat) : Graph :=
  { nodes := [clearTestNode index, clearEraseNode index, clearSeekNode index, clearHomeNode]
    entry := (clearTestNode index).reference }

theorem clearGraph_wellFormed (index : Nat) : (clearGraph index).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [clearGraph, clearTestNode, clearEraseNode, clearSeekNode, clearHomeNode,
      Node.conditional]
  · intro node member
    simp only [clearGraph, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact isEmpty_wellFormed
    · exact erase_wellFormed
    · exact seekFromBoundary_wellFormed index
    · exact home_wellFormed
  · exact resolves_member _ (clearTestNode index) (by simp [clearGraph])
  · intro node member
    simp only [clearGraph, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨resolves_member _ clearHomeNode (by simp [clearGraph]),
        resolves_member _ (clearEraseNode index) (by simp [clearGraph])⟩
    · exact ⟨resolves_member _ (clearSeekNode index) (by simp [clearGraph]), True.intro⟩
    · exact ⟨resolves_member _ (clearTestNode index) (by simp [clearGraph]), True.intro⟩
    · exact ⟨True.intro, True.intro⟩

/-- A fixed finite transition table with a loop, not an input-unrolled program. -/
def clear (index : Nat) : WorkMachine := WorkMachineProgramGraph.machine (clearGraph index)

theorem clear_wellFormed (index : Nat) : ProgramWellFormed (clear index) :=
  ⟨WorkMachineProgramGraph.rules_pairwise _ (clearGraph_wellFormed index),
    noRuleAt_globalAccept _, noRuleAt_globalReject _, machine_accept_ne_reject _⟩

def clearSteps (before : List BitString) : BitString → List Cell → Nat
  | [], _ => (fieldCells before).length + 5
  | _ :: rest, after =>
      4 * (rest.length + 1 + after.length) + 2 * (fieldCells before).length +
        before.length + 10 + clearSteps before rest after

theorem clear_empty_run (before : List BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (clear before.length) ((fieldCells before).length + 5)
      ⟨(clear before.length).startState, cursor before [] after outside slack⟩ =
    some ⟨(clear before.length).acceptState, atBoundary before [] after outside slack⟩ := by
  have hTest := WorkMachineProgramGraph.local_then_accept (clearGraph before.length)
    (clearTestNode before.length) 1 _ _ (clearGraph_wellFormed before.length)
    (by simp [clearGraph])
    (isEmpty_run [] (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside))
      (after.map Cell.symbol ++ tail slack)) rfl
  have hHome := WorkMachineProgramGraph.local_then_accept (clearGraph before.length)
    clearHomeNode ((fieldCells before).length + 2) _ _ (clearGraph_wellFormed before.length)
    (by simp [clearGraph])
    (home_run (fieldCells before) .separator outside (after.map Cell.symbol ++ tail slack)) rfl
  have hAll := PipelineMachineSimulation.workRunExact?_compose (clear before.length)
    2 ((fieldCells before).length + 2 + 1) _ _ _ hTest hHome
  have hSteps : 2 + ((fieldCells before).length + 2 + 1) = (fieldCells before).length + 5 := by omega
  rw [hSteps] at hAll
  exact hAll

/-- One iteration decreases the register length and returns to this same loop. -/
theorem clear_iteration (before : List BitString) (bit : Bool) (rest : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (clear before.length)
      (4 * (rest.length + 1 + after.length) + 2 * (fieldCells before).length + before.length + 10)
      ⟨(clear before.length).startState, cursor before (bit :: rest) after outside slack⟩ =
    some ⟨(clear before.length).startState, cursor before rest after outside (slack + 1)⟩ := by
  have hTest := WorkMachineProgramGraph.local_then_reject (clearGraph before.length)
    (clearTestNode before.length) 1 _ _ (clearGraph_wellFormed before.length)
    (by simp [clearGraph])
    (isEmpty_run (bit :: rest) (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside))
      (after.map Cell.symbol ++ tail slack)) rfl
  have hErase := WorkMachineProgramGraph.local_then_accept (clearGraph before.length)
    (clearEraseNode before.length)
    (4 * (rest.length + 1 + after.length) + (fieldCells before).length + 4)
    _ _ (clearGraph_wellFormed before.length) (by simp [clearGraph])
    (erase_register_run before bit rest after outside slack) rfl
  have hSeek := WorkMachineProgramGraph.local_then_accept (clearGraph before.length)
    (clearSeekNode before.length) (2 + seekSteps before)
    _ _ (clearGraph_wellFormed before.length) (by simp [clearGraph])
    (seekFromBoundary_run before outside (content rest after (slack + 1))) rfl
  have hFirst := PipelineMachineSimulation.workRunExact?_compose (clear before.length)
    2 (4 * (rest.length + 1 + after.length) + (fieldCells before).length + 4 + 1)
    _ _ _ hTest hErase
  have hAll := PipelineMachineSimulation.workRunExact?_compose (clear before.length)
    (2 + (4 * (rest.length + 1 + after.length) + (fieldCells before).length + 4 + 1))
    (2 + seekSteps before + 1) _ _ _ hFirst hSeek
  have hSteps :
      (2 + (4 * (rest.length + 1 + after.length) + (fieldCells before).length + 4 + 1)) +
        (2 + seekSteps before + 1) =
      4 * (rest.length + 1 + after.length) + 2 * (fieldCells before).length +
        before.length + 10 := by
    simp only [seekSteps, fieldWord_length]
    omega
  rw [hSteps] at hAll
  exact hAll

/-- Complete clearing, including empty input, with all surrounding data preserved. -/
theorem clear_run (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (clear before.length) (clearSteps before bits after)
      ⟨(clear before.length).startState, cursor before bits after outside slack⟩ =
    some ⟨(clear before.length).acceptState,
      atBoundary before [] after outside (slack + bits.length)⟩ := by
  induction bits generalizing slack with
  | nil => exact clear_empty_run before after outside slack
  | cons bit rest ih =>
      have hFirst := clear_iteration before bit rest after outside slack
      have hTail := ih (slack + 1)
      have hAll := PipelineMachineSimulation.workRunExact?_compose (clear before.length)
        (4 * (rest.length + 1 + after.length) + 2 * (fieldCells before).length + before.length + 10)
        (clearSteps before rest after) _ _ _ hFirst hTail
      have hSlack : slack + 1 + rest.length = slack + (rest.length + 1) := by omega
      simpa only [clearSteps, List.length_cons, hSlack] using hAll

theorem clear_raw_run (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (clear before.length))
      (6 * clearSteps before bits after)
      (encodeWorkConfiguration ⟨(clear before.length).startState, cursor before bits after outside slack⟩) =
    encodeWorkConfiguration ⟨(clear before.length).acceptState,
      atBoundary before [] after outside (slack + bits.length)⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (clear_run before bits after outside slack)

theorem clearSteps_eq (before : List BitString) (bits : BitString) (after : List Cell) :
    clearSteps before bits after =
      2 * bits.length * bits.length +
        (4 * after.length + 2 * (fieldCells before).length + before.length + 12) * bits.length +
        (fieldCells before).length + 5 := by
  induction bits with
  | nil => simp only [clearSteps, List.length_nil, Nat.mul_zero, Nat.zero_add]
  | cons bit rest ih =>
      simp only [clearSteps, List.length_cons, ih, Nat.mul_add, Nat.add_mul,
        Nat.mul_one]
      omega

theorem fieldCells_length_ge (before : List BitString) :
    before.length ≤ (fieldCells before).length := by
  induction before with
  | nil => exact Nat.le_refl 0
  | cons bits rest ih =>
      simp only [fieldCells, List.length_append, List.length_cons, bitCells_length]
      omega

/-- Encoded bank span: both boundaries and the selected register delimiter included. -/
def bankSpan (before : List BitString) (bits : BitString) (after : List Cell) : Nat :=
  (fieldCells before).length + bits.length + after.length + 3

/-- Uniform quadratic work bound for the complete clear loop, not merely one step. -/
theorem clearSteps_le_polynomial (before : List BitString) (bits : BitString) (after : List Cell) :
    clearSteps before bits after ≤
      9 * bankSpan before bits after * bankSpan before bits after +
        13 * bankSpan before bits after + 5 := by
  have hPrefix := fieldCells_length_ge before
  have hBits : bits.length ≤ bankSpan before bits after := by unfold bankSpan; omega
  have hBefore : (fieldCells before).length ≤ bankSpan before bits after := by unfold bankSpan; omega
  have hCoefficient :
      4 * after.length + 2 * (fieldCells before).length + before.length + 12 ≤
        7 * bankSpan before bits after + 12 := by unfold bankSpan; omega
  have hSquare := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hBits) hBits
  have hProduct := Nat.mul_le_mul hCoefficient hBits
  rw [clearSteps_eq]
  have hBound := Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add hSquare hProduct) hBefore) 5
  simp only [Nat.add_mul, Nat.mul_assoc] at hBound ⊢
  omega

theorem clearRawSteps_le_polynomial (before : List BitString) (bits : BitString) (after : List Cell) :
    6 * clearSteps before bits after ≤
      6 * (9 * bankSpan before bits after * bankSpan before bits after +
        13 * bankSpan before bits after + 5) :=
  Nat.mul_le_mul_left 6 (clearSteps_le_polynomial before bits after)

end PNP.Concrete.BitRegister.Operation
