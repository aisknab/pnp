/-
Copyright (c) 2026 PNP Labs.

Finite trace-row reading for parent selection. The node tag and index are
saved before its optional predecessor metadata is skipped. The resulting
cursor is the next row, and a nonempty raw cursor strictly decreases.
-/

import PNP.Concrete.NormalizerParentRoot

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

open BitRegister Occurrence

def beginNode : Block 21 :=
  .seq (.action (.copy 0 16)) (.seq (.action (.copy 14 0)) (.action (.pop 0)))
def nodeStarted (r : State) : State :=
  {r with graph := {r.graph with first := r.pending, core := {r.graph.core with core := {r.registers with input := r.pending.tail}}}}
theorem beginNode_exec (r : State) : Exec beginNode r.store 3 (nodeStarted r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def saveNode : Block 21 := .seq (.action (.copy 20 1)) (.action (.copy 9 1))
def nodeSaved (r : State) : State :=
  {r with currentIndex := r.registers.target, graph := {r.graph with core := {r.graph.core with target := r.registers.target}}}
theorem saveNode_exec (r : State) : Exec saveNode r.store 2 (nodeSaved r).store :=
  Exec.seq (.action _ _) (.action _ _)

def dropParentTags : Block 21 := .seq (.action (.pop 0)) (.action (.pop 0))
def parentDropped (r : State) : State := r.withRegisters {r.registers with input := r.registers.input.tail.tail}
theorem dropParentTags_exec (r : State) : Exec dropParentTags r.store 2 (parentDropped r).store :=
  Exec.seq (.action _ _) (.action _ _)

def skipParent : Block 21 :=
  .branch 0 .skip (.action (.pop 0)) (.seq dropParentTags readHeader)
def parentSkipped (r : State) : State :=
  r.withRegisters (if ForwardEdge.present r.registers.input then (TableInit.readCount r.registers.input.tail.tail).state
    else {r.registers with input := r.registers.input.tail})
def skipFuel (r : State) : Nat :=
  if ForwardEdge.present r.registers.input then 11 + TableInit.headerFuel r.registers.input.tail.tail else 2

theorem skipParent_exec (r : State) : Exec skipParent r.store (skipFuel r) (parentSkipped r).store := by
  cases input : r.registers.input with
  | nil =>
      have same : r.withRegisters {r.registers with input := []} = r := by
        rw [← input]
        rfl
      simp only [skipParent, parentSkipped, skipFuel, ForwardEdge.present, input, List.headD, List.tail_nil, Bool.false_eq_true, ite_false, same]
      exact Exec.empty (source := (0 : Fin 21)) (before := r.store) input (.skip _)
  | cons bit rest =>
      cases bit with
      | false =>
          have pop : Exec (.action (.pop 0)) r.store 1
              (r.withRegisters {r.registers with input := r.registers.input.tail}).store := .action _ _
          have tail : r.registers.input.tail = rest := by rw [input]; rfl
          rw [tail] at pop
          simp only [skipParent, parentSkipped, skipFuel, ForwardEdge.present, input, List.headD, List.tail_cons, Bool.false_eq_true, ite_false]
          exact Exec.zero (source := (0 : Fin 21)) (before := r.store) input pop
      | true =>
          have checked := Exec.one (source := (0 : Fin 21)) (before := r.store)
            (empty := .skip) (zero := .action (.pop 0)) input
            (Exec.seq (dropParentTags_exec r) (readHeader_exec (parentDropped r)))
          change Exec skipParent r.store
            (1 + (2 + (8 + TableInit.headerFuel r.registers.input.tail.tail)))
            (r.withRegisters (TableInit.readCount r.registers.input.tail.tail).state).store at checked
          have cost : 11 + TableInit.headerFuel rest.tail = 1 + (2 + (8 + TableInit.headerFuel rest.tail)) := by omega
          simpa only [skipParent, parentSkipped, skipFuel, ForwardEdge.present, input, List.headD,
            List.tail_cons, ite_true, cost] using checked

theorem parentSkipped_input (r : State) :
    (parentSkipped r).registers.input = TraceData.skipParent r.registers.input := by
  cases tag : ForwardEdge.present r.registers.input <;>
    simp only [parentSkipped, TraceData.skipParent, ForwardEdge.present] at tag ⊢
  · rw [tag]
    rfl
  · rw [tag]
    rfl

theorem skipFuel_bound (r : State) : skipFuel r ≤ 4 * r.registers.input.length + 17 := by
  have header := TableInit.headerFuel_bound r.registers.input.tail.tail
  have length := EdgeKinds.tail_length_le r.registers.input
  cases tag : ForwardEdge.present r.registers.input <;>
    simp only [skipFuel, tag, Bool.false_eq_true, ite_false, ite_true] <;> omega

def finishNode : Block 21 :=
  .seq (.action (.copy 16 0)) <| .seq (.action (.copy 9 20)) <|
    .seq (.action (.copy 10 17)) (.action (.copy 15 18))
def nodeFinished (r : State) : State :=
  {r with pending := r.registers.input, graph := {r.graph with second := r.targetTag, core := {r.graph.core with target := r.currentIndex, index := r.targetIndex}}}
theorem finishNode_exec (r : State) : Exec finishNode r.store 4 (nodeFinished r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def readNode : Block 21 := .seq beginNode (.seq readHeader (.seq saveNode (.seq skipParent finishNode)))
def nodeResult (r : State) : State := nodeFinished (parentSkipped (nodeSaved (headerResult (nodeStarted r))))
def nodeFuel (r : State) : Nat :=
  3 + (headerFuel (nodeStarted r) + (2 + (skipFuel (nodeSaved (headerResult (nodeStarted r))) + 4)))

theorem readNode_exec (r : State) : Exec readNode r.store (nodeFuel r) (nodeResult r).store :=
  Exec.seq (beginNode_exec r) (Exec.seq (readHeader_exec (nodeStarted r))
    (Exec.seq (saveNode_exec (headerResult (nodeStarted r)))
      (Exec.seq (skipParent_exec (nodeSaved (headerResult (nodeStarted r))))
        (finishNode_exec (parentSkipped (nodeSaved (headerResult (nodeStarted r))))))))

theorem node_fields (r : State) :
    (nodeResult r).pending = TraceData.next r.pending ∧
      (nodeResult r).currentIndex = TraceData.nodeIndex r.pending ∧
        (nodeResult r).graph.core.target = TraceData.nodeIndex r.pending ∧
          (nodeResult r).graph.core.index = r.targetIndex ∧
            (nodeResult r).graph.first = r.pending ∧ (nodeResult r).graph.second = r.targetTag := by
  have cursor := parentSkipped_input (nodeSaved (headerResult (nodeStarted r)))
  exact ⟨cursor, rfl, rfl, rfl, rfl, rfl⟩

theorem node_preserves (r : State) :
    (nodeResult r).targetIndex = r.targetIndex ∧ (nodeResult r).targetTag = r.targetTag ∧
      (nodeResult r).graph.core.formula = r.graph.core.formula ∧
        (nodeResult r).graph.core.matching = r.graph.core.matching ∧ (nodeResult r).output = r.output :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nodeFuel_bound (r : State) : nodeFuel r ≤ 8 * r.pending.length + 40 := by
  have tail : r.pending.tail.length ≤ r.pending.length := by
    cases r.pending <;> simp only [List.tail_nil, List.tail_cons, List.length_nil, List.length_cons] <;> omega
  have header := TableInit.headerFuel_bound r.pending.tail
  have cursor := Occurrence.header_input_bound r.pending.tail (TableInit.seeded r.pending.tail)
  change (TableInit.readCount r.pending.tail).state.input.length ≤ r.pending.tail.length at cursor
  have skipped := skipFuel_bound (nodeSaved (headerResult (nodeStarted r)))
  change skipFuel (nodeSaved (headerResult (nodeStarted r))) ≤
    4 * (TableInit.readCount r.pending.tail).state.input.length + 17 at skipped
  change 3 + ((8 + TableInit.headerFuel r.pending.tail) +
    (2 + (skipFuel (nodeSaved (headerResult (nodeStarted r))) + 4))) ≤ _
  omega

theorem node_shorter (r : State) (nonempty : r.pending ≠ []) :
    (nodeResult r).pending.length < r.pending.length := by
  rw [(node_fields r).1]
  exact TraceData.next_shorter r.pending nonempty

end PNP.Concrete.NormalizerBlocks.ParentQuery
