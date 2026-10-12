/-
Copyright (c) 2026 PNP Labs.

Exact canonical row transitions for the suffix-based path machine.
Success is available only after reaching a root in the retained suffix.
-/
import PNP.Concrete.NormalizerPathScan

namespace PNP.Concrete.NormalizerBlocks.TracePath

theorem body_on_row (r : State) (target : CNFLiteral) (entry : TraceData.Row) (suffix : BitString)
    (indexRead : r.core.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.core.targetTag = target.positive)
    (traceRead : r.core.pending = TraceData.row entry suffix) :
    bodyResult r = if TraceMember.same entry.1 target then nodeAccepted (probed r) else probed r := by
  unfold bodyResult nodeDecided
  rw [(probed_canonical r target entry suffix indexRead tagRead traceRead).1]
  rfl

theorem accepted_root (r : State) (root : ForwardEdge.present r.parentBytes = false) :
    nodeAccepted r = rootFinished (nodeAppended r) := by
  unfold nodeAccepted predecessorChosen
  rw [(nodeAppended_preserves r).2.2.2.2.1, root]
  rfl

theorem accepted_parent (r : State) (parent : ForwardEdge.present r.parentBytes = true) :
    nodeAccepted r = parentFollowed (nodeAppended r) := by
  unfold nodeAccepted predecessorChosen
  rw [(nodeAppended_preserves r).2.2.2.2.1, parent]
  rfl

theorem body_row_root (r : State) (target : CNFLiteral) (suffix : BitString)
    (indexRead : r.core.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.core.targetTag = target.positive)
    (traceRead : r.core.pending = TraceData.row (target, none) suffix) :
    (bodyResult r).core.pending = [] ∧ (bodyResult r).core.output = [true] ∧
      (bodyResult r).buffer = (TraceData.vertex target []).reverse ++ r.buffer := by
  have row := probed_canonical r target (target, none) suffix indexRead tagRead traceRead
  have found : TraceMember.same target target = true := (TraceMember.same_true_iff _ _).2 rfl
  have root : ForwardEdge.present (probed r).parentBytes = false := by rw [row.2.2.1]; rfl
  rw [body_on_row r target (target, none) suffix indexRead tagRead traceRead]
  simp only [found, ite_true]
  rw [accepted_root _ root]
  refine ⟨rfl, rfl, ?_⟩
  change (nodeAppended (probed r)).buffer = _
  rw [nodeAppended_canonical _ target row.2.2.2.1 row.2.2.2.2, (probed_preserves r).2.2.2.2.2]

theorem body_row_parent (r : State) (target parent : CNFLiteral) (suffix : BitString)
    (indexRead : r.core.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.core.targetTag = target.positive)
    (traceRead : r.core.pending = TraceData.row (target, some parent) suffix) :
    (bodyResult r).core.pending = suffix ∧
      (bodyResult r).core.targetIndex = List.replicate parent.variableIndex true ∧
        ForwardEdge.present (bodyResult r).core.targetTag = parent.positive ∧
          (bodyResult r).core.output = r.core.output ∧
            (bodyResult r).buffer = (TraceData.vertex target []).reverse ++ r.buffer := by
  have row := probed_canonical r target (target, some parent) suffix indexRead tagRead traceRead
  have found : TraceMember.same target target = true := (TraceMember.same_true_iff _ _).2 rfl
  have saved : (nodeAppended (probed r)).parentBytes = TraceData.predecessor (some parent) suffix :=
    (nodeAppended_preserves _).2.2.2.2.1.trans row.2.2.1
  have parentTag : ForwardEdge.present (probed r).parentBytes = true := by rw [row.2.2.1]; rfl
  have targetRead := parentFollowed_canonical (nodeAppended (probed r)) parent suffix saved
  have preserved := parentFollowed_preserves (nodeAppended (probed r))
  have appended := nodeAppended_preserves (probed r)
  have probing := probed_preserves r
  rw [body_on_row r target (target, some parent) suffix indexRead tagRead traceRead]
  simp only [found, ite_true]
  rw [accepted_parent _ parentTag]
  refine ⟨preserved.1.trans (appended.1.trans row.2.1), targetRead.1, targetRead.2,
    preserved.2.1.trans (appended.2.2.2.1.trans probing.2.2.1), ?_⟩
  rw [preserved.2.2.1, nodeAppended_canonical _ target row.2.2.2.1 row.2.2.2.2, probing.2.2.2.2.2]

theorem append_accumulator (target : CNFLiteral) (prior : List CNFLiteral) :
    (TraceData.vertex target []).reverse ++ (PathData.encode prior).reverse =
      (PathData.encode (prior ++ [target])).reverse := by
  rw [PathData.encode_append, List.reverse_append]
  rfl

def observation (r : State) : BitString :=
  if ForwardEdge.present r.core.output then true :: r.buffer.reverse else [false]

end PNP.Concrete.NormalizerBlocks.TracePath
