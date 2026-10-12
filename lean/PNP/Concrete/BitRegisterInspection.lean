/-
Copyright (c) 2026 PNP Labs.

Canonical read-only register inspection. Both Boolean outcomes restore the
left boundary and preserve the complete tape. Empty testing covers every
register word; head-bit inspection is used only after the empty test rejects.
No empty register is silently interpreted as a zero bit.
-/

import PNP.Concrete.BitRegisterStoreTape

namespace PNP.Concrete.BitRegister

open TapePrimitive Mutation Operation WorkMachineProgramGraph
open PipelineStateNamespace

namespace Operation

theorem headBit_wellFormed : ProgramWellFormed headBit := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

def inspectAcceptNode : Node :=
  { name := 2, program := home, onAccept := .accept, onReject := .reject }

def inspectRejectNode : Node :=
  { name := 3, program := home, onAccept := .reject, onReject := .reject }

def inspectTestNode (test : WorkMachine) : Node :=
  Node.conditional 1 test inspectAcceptNode.reference inspectRejectNode.reference

def inspectSeekNode (index : Nat) (test : WorkMachine) : Node :=
  { name := 0, program := seekFromBoundary index
    onAccept := .node (inspectTestNode test).reference, onReject := .reject }

def inspectGraph (index : Nat) (test : WorkMachine) : Graph :=
  { nodes := [inspectSeekNode index test, inspectTestNode test, inspectAcceptNode, inspectRejectNode]
    entry := (inspectSeekNode index test).reference }

theorem inspectGraph_wellFormed (index : Nat) (test : WorkMachine)
    (valid : ProgramWellFormed test) : (inspectGraph index test).WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [inspectGraph, inspectSeekNode, inspectTestNode, inspectAcceptNode, inspectRejectNode,
      Node.conditional]
  · intro node member
    simp only [inspectGraph, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact seekFromBoundary_wellFormed index
    · exact valid
    · exact home_wellFormed
    · exact home_wellFormed
  · exact resolves_member _ (inspectSeekNode index test) (by simp [inspectGraph])
  · intro node member
    simp only [inspectGraph, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨resolves_member _ (inspectTestNode test) (by simp [inspectGraph]), True.intro⟩
    · exact ⟨resolves_member _ inspectAcceptNode (by simp [inspectGraph]),
        resolves_member _ inspectRejectNode (by simp [inspectGraph])⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

/-- The parameter is finite transition-table data, not a host-language predicate. -/
def inspectAt (index : Nat) (test : WorkMachine) : WorkMachine :=
  WorkMachineProgramGraph.machine (inspectGraph index test)

theorem inspectAt_wellFormed (index : Nat) (test : WorkMachine)
    (valid : ProgramWellFormed test) : ProgramWellFormed (inspectAt index test) :=
  ⟨WorkMachineProgramGraph.rules_pairwise _ (inspectGraph_wellFormed index test valid),
    noRuleAt_globalAccept _, noRuleAt_globalReject _, machine_accept_ne_reject _⟩

def inspectSteps (before : List BitString) : Nat :=
  2 * (fieldCells before).length + before.length + 8

/-- Trace composition only; the public operations below discharge the local test trace. -/
theorem inspect_accept_run (test : WorkMachine) (valid : ProgramWellFormed test)
    (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat)
    (tested : workRunExact? test 1
      ⟨test.startState, cursor before bits after outside slack⟩ =
      some ⟨test.acceptState, cursor before bits after outside slack⟩) :
    workRunExact? (inspectAt before.length test) (inspectSteps before)
      ⟨(inspectAt before.length test).startState, atBoundary before bits after outside slack⟩ =
    some ⟨(inspectAt before.length test).acceptState, atBoundary before bits after outside slack⟩ := by
  have wf := inspectGraph_wellFormed before.length test valid
  have hSeek := WorkMachineProgramGraph.local_then_accept (inspectGraph before.length test)
    (inspectSeekNode before.length test) (2 + seekSteps before) _ _ wf (by simp [inspectGraph])
    (seekFromBoundary_run before outside (content bits after slack)) rfl
  have hTest := WorkMachineProgramGraph.local_then_accept (inspectGraph before.length test)
    (inspectTestNode test) 1 _ _ wf (by simp [inspectGraph]) tested rfl
  have hHome := WorkMachineProgramGraph.local_then_accept (inspectGraph before.length test)
    inspectAcceptNode ((fieldCells before).length + 2) _ _ wf (by simp [inspectGraph])
    (home_cursor_run before bits after outside slack) rfl
  have hFirst := PipelineMachineSimulation.workRunExact?_compose (inspectAt before.length test)
    (2 + seekSteps before + 1) 2 _ _ _ hSeek hTest
  have hAll := PipelineMachineSimulation.workRunExact?_compose (inspectAt before.length test)
    (2 + seekSteps before + 1 + 2) ((fieldCells before).length + 2 + 1) _ _ _ hFirst hHome
  have hSteps : (2 + seekSteps before + 1 + 2) + ((fieldCells before).length + 2 + 1) =
      inspectSteps before := by
    simp only [seekSteps, fieldWord_length, inspectSteps]; omega
  rw [hSteps] at hAll
  exact hAll

theorem inspect_reject_run (test : WorkMachine) (valid : ProgramWellFormed test)
    (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat)
    (tested : workRunExact? test 1
      ⟨test.startState, cursor before bits after outside slack⟩ =
      some ⟨test.rejectState, cursor before bits after outside slack⟩) :
    workRunExact? (inspectAt before.length test) (inspectSteps before)
      ⟨(inspectAt before.length test).startState, atBoundary before bits after outside slack⟩ =
    some ⟨(inspectAt before.length test).rejectState, atBoundary before bits after outside slack⟩ := by
  have wf := inspectGraph_wellFormed before.length test valid
  have hSeek := WorkMachineProgramGraph.local_then_accept (inspectGraph before.length test)
    (inspectSeekNode before.length test) (2 + seekSteps before) _ _ wf (by simp [inspectGraph])
    (seekFromBoundary_run before outside (content bits after slack)) rfl
  have hTest := WorkMachineProgramGraph.local_then_reject (inspectGraph before.length test)
    (inspectTestNode test) 1 _ _ wf (by simp [inspectGraph]) tested rfl
  have hHome := WorkMachineProgramGraph.local_then_accept (inspectGraph before.length test)
    inspectRejectNode ((fieldCells before).length + 2) _ _ wf (by simp [inspectGraph])
    (home_cursor_run before bits after outside slack) rfl
  have hFirst := PipelineMachineSimulation.workRunExact?_compose (inspectAt before.length test)
    (2 + seekSteps before + 1) 2 _ _ _ hSeek hTest
  have hAll := PipelineMachineSimulation.workRunExact?_compose (inspectAt before.length test)
    (2 + seekSteps before + 1 + 2) ((fieldCells before).length + 2 + 1) _ _ _ hFirst hHome
  have hSteps : (2 + seekSteps before + 1 + 2) + ((fieldCells before).length + 2 + 1) =
      inspectSteps before := by
    simp only [seekSteps, fieldWord_length, inspectSteps]; omega
  rw [hSteps] at hAll
  exact hAll

def emptyAt (index : Nat) : WorkMachine := inspectAt index isEmpty
def headAt (index : Nat) : WorkMachine := inspectAt index headBit

theorem emptyAt_wellFormed (index : Nat) : ProgramWellFormed (emptyAt index) :=
  inspectAt_wellFormed index isEmpty isEmpty_wellFormed

theorem headAt_wellFormed (index : Nat) : ProgramWellFormed (headAt index) :=
  inspectAt_wellFormed index headBit headBit_wellFormed

theorem emptyAt_run (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (emptyAt before.length) (inspectSteps before)
      ⟨(emptyAt before.length).startState, atBoundary before bits after outside slack⟩ =
    some ⟨(if bits.isEmpty then (emptyAt before.length).acceptState else (emptyAt before.length).rejectState),
      atBoundary before bits after outside slack⟩ := by
  cases bits with
  | nil =>
      exact inspect_accept_run isEmpty isEmpty_wellFormed before [] after outside slack
        (isEmpty_run [] (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside))
          (after.map Cell.symbol ++ tail slack))
  | cons bit rest =>
      exact inspect_reject_run isEmpty isEmpty_wellFormed before (bit :: rest) after outside slack
        (isEmpty_run (bit :: rest) (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside))
          (after.map Cell.symbol ++ tail slack))

theorem headAt_run (before : List BitString) (bit : Bool) (rest : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (headAt before.length) (inspectSteps before)
      ⟨(headAt before.length).startState, atBoundary before (bit :: rest) after outside slack⟩ =
    some ⟨(if bit then (headAt before.length).acceptState else (headAt before.length).rejectState),
      atBoundary before (bit :: rest) after outside slack⟩ := by
  cases bit with
  | false =>
      exact inspect_reject_run headBit headBit_wellFormed before (false :: rest) after outside slack
        (headBit_run false rest (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside))
          (after.map Cell.symbol ++ tail slack))
  | true =>
      exact inspect_accept_run headBit headBit_wellFormed before (true :: rest) after outside slack
        (headBit_run true rest (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside))
          (after.map Cell.symbol ++ tail slack))

theorem inspectSteps_le (before : List BitString) (bits : BitString) (after : List Cell) :
    inspectSteps before ≤ 3 * bankSpan before bits after := by
  have h := fieldCells_length_ge before
  simp only [inspectSteps, bankSpan]
  omega

end Operation

namespace Store

def inspectSteps {count : Nat} (store : Store count) (index : Fin count) : Nat :=
  Operation.inspectSteps (store.beforeFields index)

theorem empty_run {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (emptyAt index.val) (store.inspectSteps index)
      ⟨(emptyAt index.val).startState, store.tape outside slack⟩ =
    some ⟨(if (store.get index).isEmpty then (emptyAt index.val).acceptState else (emptyAt index.val).rejectState),
      store.tape outside slack⟩ := by
  simpa only [inspectSteps, tape_boundary store index outside slack, beforeFields_length] using
    emptyAt_run (store.beforeFields index) (store.get index) (fieldCells (store.afterFields index)) outside slack

theorem head_run {count : Nat} (store : Store count) (index : Fin count) (bit : Bool)
    (rest : BitString) (head : store.get index = bit :: rest)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (headAt index.val) (store.inspectSteps index)
      ⟨(headAt index.val).startState, store.tape outside slack⟩ =
    some ⟨(if bit then (headAt index.val).acceptState else (headAt index.val).rejectState),
      store.tape outside slack⟩ := by
  simpa only [inspectSteps, tape_boundary store index outside slack, head, beforeFields_length] using
    headAt_run (store.beforeFields index) bit rest (fieldCells (store.afterFields index)) outside slack

theorem empty_raw_run {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (emptyAt index.val)) (6 * store.inspectSteps index)
      (encodeWorkConfiguration ⟨(emptyAt index.val).startState, store.tape outside slack⟩) =
    encodeWorkConfiguration
      ⟨(if (store.get index).isEmpty then (emptyAt index.val).acceptState else (emptyAt index.val).rejectState),
        store.tape outside slack⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (empty_run store index outside slack)

theorem head_raw_run {count : Nat} (store : Store count) (index : Fin count) (bit : Bool)
    (rest : BitString) (head : store.get index = bit :: rest)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (headAt index.val)) (6 * store.inspectSteps index)
      (encodeWorkConfiguration ⟨(headAt index.val).startState, store.tape outside slack⟩) =
    encodeWorkConfiguration
      ⟨(if bit then (headAt index.val).acceptState else (headAt index.val).rejectState),
        store.tape outside slack⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (head_run store index bit rest head outside slack)

theorem inspectSteps_le {count : Nat} (store : Store count) (index : Fin count) :
    store.inspectSteps index ≤ 3 * (store.span + 2) := by
  have h := Operation.inspectSteps_le (store.beforeFields index) (store.get index)
    (fieldCells (store.afterFields index))
  rw [bankSpan_selected] at h
  exact h

end Store
end PNP.Concrete.BitRegister
