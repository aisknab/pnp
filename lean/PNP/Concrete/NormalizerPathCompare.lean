/-
Copyright (c) 2026 PNP Labs.

Compare the current path target with the actual row node, retaining both
the following suffix and optional predecessor. The comparison does not
consume or replace the saved path, target, parent bytes or success flag.
-/

import PNP.Concrete.NormalizerPathNode

namespace PNP.Concrete.NormalizerBlocks.TraceMember

theorem comparison_nodes (r : State) :
    (compared r).currentIndex = r.currentIndex ∧ (compared r).graph.first = r.graph.first := by
  have stable (state : State) :
      (filtered state).currentIndex = state.currentIndex ∧ (filtered state).graph.first = state.graph.first := by
    cases first : ForwardEdge.present state.graph.first <;> cases second : ForwardEdge.present state.targetTag <;>
      simp only [filtered, first, second, Bool.false_eq_true, ite_false, ite_true] <;> constructor <;> trivial
  exact stable (counted r)

end PNP.Concrete.NormalizerBlocks.TraceMember

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister

def compareNode : Block 23 := lift TraceMember.comparison
def nodeCompared (r : State) : State := r.withCore (TraceMember.compared r.core)
theorem compareNode_exec (r : State) :
    Exec compareNode r.store (TraceMember.comparisonFuel r.core) (nodeCompared r).store :=
  lift_exec _ r _ _ (TraceMember.comparison_exec r.core)

def probe : Block 23 := .seq readNode compareNode
def probed (r : State) : State := nodeCompared (nodeRead r)
def probeFuel (r : State) : Nat := nodeFuel r + TraceMember.comparisonFuel (nodeRead r).core
theorem probe_exec (r : State) : Exec probe r.store (probeFuel r) (probed r).store :=
  Exec.seq (readNode_exec r) (compareNode_exec (nodeRead r))

theorem probed_pending (r : State) : (probed r).core.pending = TraceData.next r.core.pending :=
  (TraceMember.comparison_preserves (nodeRead r).core).1.trans (ParentQuery.node_fields r.core).1

theorem probed_preserves (r : State) :
    (probed r).core.targetIndex = r.core.targetIndex ∧
      (probed r).core.targetTag = r.core.targetTag ∧
        (probed r).core.output = r.core.output ∧
          (probed r).core.graph.core.formula = r.core.graph.core.formula ∧
            (probed r).core.graph.core.matching = r.core.graph.core.matching ∧
              (probed r).buffer = r.buffer := by
  have compare := TraceMember.comparison_preserves (nodeRead r).core
  have read := ParentQuery.node_preserves r.core
  exact ⟨compare.2.1.trans read.1, compare.2.2.1.trans read.2.1,
    compare.2.2.2.2.2.trans read.2.2.2.2, compare.2.2.2.1.trans read.2.2.1,
    compare.2.2.2.2.1.trans read.2.2.2.1, rfl⟩

theorem probed_nodes (r : State) :
    (probed r).core.currentIndex = TraceData.nodeIndex r.core.pending ∧
      (probed r).core.graph.first = r.core.pending ∧
        (probed r).parentBytes = (TableInit.readCount r.core.pending.tail).state.input := by
  have compare := TraceMember.comparison_nodes (nodeRead r).core
  have read := ParentQuery.node_fields r.core
  exact ⟨compare.1.trans read.2.1, compare.2.trans read.2.2.2.2.1, rfl⟩

theorem probeFuel_bound (r : State) : probeFuel r ≤ 28 * r.core.pending.length + 77 := by
  have read := nodeFuel_bound r
  have index := TraceData.nodeIndex_length r.core.pending
  have compare := TraceMember.comparisonFuel_bound (nodeRead r).core
  rw [(nodeRead_fields r).1, (ParentQuery.node_fields r.core).2.1] at compare
  unfold probeFuel
  rw [(nodeRead_fields r).1]
  omega

theorem probed_canonical (r : State) (target : CNFLiteral) (entry : TraceData.Row) (suffix : BitString)
    (indexRead : r.core.targetIndex = List.replicate target.variableIndex true)
    (tagRead : ForwardEdge.present r.core.targetTag = target.positive)
    (traceRead : r.core.pending = TraceData.row entry suffix) :
    (probed r).registers.output = [TraceMember.same entry.1 target] ∧
      (probed r).core.pending = suffix ∧
        (probed r).parentBytes = TraceData.predecessor entry.2 suffix ∧
          (probed r).core.currentIndex = List.replicate entry.1.variableIndex true ∧
            ForwardEdge.present (probed r).core.graph.first = entry.1.positive := by
  have compare := TraceMember.row_comparison r.core target entry suffix indexRead tagRead traceRead
  have node := nodeRead_canonical r entry suffix traceRead
  have saved := probed_nodes r
  refine ⟨compare, ?_, node.2.1, ?_, ?_⟩
  · rw [probed_pending, traceRead, TraceData.next_canonical]
  · rw [saved.1, traceRead, TraceData.nodeIndex_canonical]
  · rw [saved.2.1, traceRead]
    rfl

end PNP.Concrete.NormalizerBlocks.TracePath
