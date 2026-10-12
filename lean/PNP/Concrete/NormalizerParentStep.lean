/-
Copyright (c) 2026 PNP Labs.

One internally computed parent-search step. Read one full trace row, query
its actual directed edge to the fixed target, and stop on the first match.
The returned predecessor retains the original node index even when the
edge controller swaps its query indices internally.
-/

import PNP.Concrete.NormalizerParentNode

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

open BitRegister

def queryEdge : Block 21 := Frame.block 5 EdgeKinds.dispatch
def edgeResult (r : State) : State := {r with graph := EdgeKinds.dispatchResult r.graph}
def edgeFuel (r : State) : Nat := EdgeKinds.dispatchFuel r.graph
theorem queryEdge_exec (r : State) : Exec queryEdge r.store (edgeFuel r) (edgeResult r).store :=
  Frame.execution (EdgeKinds.dispatch_exec r.graph) r.frame

theorem edge_data (r : State) :
    (edgeResult r).graph.first = r.graph.first ∧
      (edgeResult r).graph.core.formula = r.graph.core.formula ∧
        (edgeResult r).graph.core.matching = r.graph.core.matching := by
  cases first : ForwardEdge.present r.graph.first <;> cases second : ForwardEdge.present r.graph.second <;>
    simp only [edgeResult, EdgeKinds.dispatchResult, first, second, Bool.false_eq_true, ite_false, ite_true] <;>
      exact ⟨rfl, rfl, rfl⟩

def answerTag : Block 21 :=
  .branch 14 (.action (.push 19 false)) (.action (.push 19 false)) (.action (.push 19 true))
def answerTagged (r : State) : State := {r with output := ForwardEdge.present r.graph.first :: r.output}
theorem answerTag_exec (r : State) : Exec answerTag r.store 2 (answerTagged r).store := by
  cases tag : r.graph.first with
  | nil =>
      simp only [answerTagged, ForwardEdge.present, tag, List.headD]
      exact Exec.empty (source := (14 : Fin 21)) (before := r.store) tag (.action _ _)
  | cons bit rest =>
      cases bit with
      | false =>
          simp only [answerTagged, ForwardEdge.present, tag, List.headD]
          exact Exec.zero (source := (14 : Fin 21)) (before := r.store) tag (.action _ _)
      | true =>
          simp only [answerTagged, ForwardEdge.present, tag, List.headD]
          exact Exec.one (source := (14 : Fin 21)) (before := r.store) tag (.action _ _)

def sealAnswer : Block 21 :=
  .seq (.action (.push 19 true)) (.seq (.action (.push 19 true)) (.action (.clear 16)))
def answerSealed (r : State) : State := {r with pending := [], output := true :: true :: r.output}
theorem sealAnswer_exec (r : State) : Exec sealAnswer r.store 3 (answerSealed r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))

def acceptParent : Block 21 := .seq (.action (.copy 19 20)) (.seq answerTag sealAnswer)
def accepted (r : State) : State :=
  {r with pending := [], output := true :: true :: ForwardEdge.present r.graph.first :: r.currentIndex}
theorem acceptParent_exec (r : State) : Exec acceptParent r.store 6 (accepted r).store := by
  have copied : Exec (.action (.copy 19 20)) r.store 1 ({r with output := r.currentIndex}).store := .action _ _
  exact Exec.seq copied (Exec.seq (answerTag_exec {r with output := r.currentIndex})
    (sealAnswer_exec (answerTagged {r with output := r.currentIndex})))

def selectParent : Block 21 := .branch 8 .skip .skip acceptParent
def selected (r : State) : State := if ForwardEdge.present r.registers.output then accepted r else r
def selectFuel (r : State) : Nat := if ForwardEdge.present r.registers.output then 7 else 2

theorem selectParent_exec (r : State) : Exec selectParent r.store (selectFuel r) (selected r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 21) r.store .skip acceptParent 1 6 r.store (accepted r).store
    (Exec.skip r.store) (acceptParent_exec r)
  change Exec selectParent r.store
    (1 + if ForwardEdge.present r.registers.output then 6 else 1)
    (if ForwardEdge.present r.registers.output then (accepted r).store else r.store) at checked
  cases found : ForwardEdge.present r.registers.output <;>
    simpa only [selected, selectFuel, found, Bool.false_eq_true, ite_false, ite_true] using checked

theorem selectFuel_bound (r : State) : selectFuel r ≤ 7 := by
  unfold selectFuel
  cases ForwardEdge.present r.registers.output <;> decide

theorem selected_preserves (r : State) :
    (selected r).targetIndex = r.targetIndex ∧ (selected r).targetTag = r.targetTag ∧
      (selected r).graph.core.formula = r.graph.core.formula ∧
        (selected r).graph.core.matching = r.graph.core.matching := by
  cases found : ForwardEdge.present r.registers.output <;>
    simp only [selected, found, Bool.false_eq_true, ite_false, ite_true, accepted] <;> trivial

theorem selected_pending (r : State) : (selected r).pending = [] ∨ (selected r).pending = r.pending := by
  cases found : ForwardEdge.present r.registers.output
  · apply Or.inr
    simp only [selected, found, Bool.false_eq_true, ite_false]
  · apply Or.inl
    simp only [selected, found, ite_true, accepted]

def body : Block 21 := .seq readNode (.seq queryEdge selectParent)
def bodyResult (r : State) : State := selected (edgeResult (nodeResult r))
def bodyFuel (r : State) : Nat := nodeFuel r + (edgeFuel (nodeResult r) + selectFuel (edgeResult (nodeResult r)))
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (readNode_exec r) (Exec.seq (queryEdge_exec (nodeResult r)) (selectParent_exec (edgeResult (nodeResult r))))

def stepBound (r : State) : Nat :=
  188 * r.graph.core.formula.length + 188 * r.graph.core.matching.length +
    208 * r.pending.length + 40 * r.targetIndex.length + 893

theorem bodyFuel_bound (r : State) : bodyFuel r ≤ stepBound r := by
  have parse := nodeFuel_bound r
  have index := TraceData.nodeIndex_length r.pending
  have query := EdgeKinds.dispatchFuel_bound (nodeResult r).graph
  change edgeFuel (nodeResult r) ≤
    188 * r.graph.core.formula.length + 188 * r.graph.core.matching.length +
      40 * (TraceData.nodeIndex r.pending).length + 40 * r.targetIndex.length + 606 at query
  have choose := selectFuel_bound (edgeResult (nodeResult r))
  simp only [bodyFuel, stepBound]
  omega

theorem body_preserves (r : State) :
    (bodyResult r).targetIndex = r.targetIndex ∧ (bodyResult r).targetTag = r.targetTag ∧
      (bodyResult r).graph.core.formula = r.graph.core.formula ∧
        (bodyResult r).graph.core.matching = r.graph.core.matching := by
  have parse := node_preserves r
  have query := edge_data (nodeResult r)
  have choose := selected_preserves (edgeResult (nodeResult r))
  exact ⟨choose.1.trans parse.1, choose.2.1.trans parse.2.1,
    choose.2.2.1.trans (query.2.1.trans parse.2.2.1),
    choose.2.2.2.trans (query.2.2.trans parse.2.2.2.1)⟩

theorem body_progress (r : State) (nonempty : r.pending ≠ []) :
    (bodyResult r).pending = [] ∨ (bodyResult r).pending.length < r.pending.length := by
  cases selected_pending (edgeResult (nodeResult r)) with
  | inl stopped => exact Or.inl stopped
  | inr next =>
      apply Or.inr
      change (selected (edgeResult (nodeResult r))).pending.length < _
      rw [next]
      exact node_shorter r nonempty

theorem body_size (r : State) (nonempty : r.pending ≠ []) : (bodyResult r).pending.length ≤ r.pending.length := by
  cases body_progress r nonempty with
  | inl stopped => rw [stopped]; exact Nat.zero_le _
  | inr smaller => exact Nat.le_of_lt smaller

theorem stepBound_mono (r : State) (nonempty : r.pending ≠ []) : stepBound (bodyResult r) ≤ stepBound r := by
  have stable := body_preserves r
  have size := body_size r nonempty
  simp only [stepBound, stable.1, stable.2.2.1, stable.2.2.2]
  omega

end PNP.Concrete.NormalizerBlocks.ParentQuery
