/-
Copyright (c) 2026 PNP Labs.

One path reconstruction step: inspect a row, append it only on an exact
signed-node match, then follow its predecessor in the already-advanced
suffix or finish at a root. Every raw nonempty cursor strictly decreases.
-/
import PNP.Concrete.NormalizerPathFollow

namespace PNP.Concrete.NormalizerBlocks.TracePath
open BitRegister

def acceptNode : Block 23 := .seq appendNode choosePredecessor
def nodeAccepted (r : State) : State := predecessorChosen (nodeAppended r)
def acceptFuel (r : State) : Nat := appendFuel r + predecessorFuel (nodeAppended r)
theorem acceptNode_exec (r : State) : Exec acceptNode r.store (acceptFuel r) (nodeAccepted r).store :=
  Exec.seq (appendNode_exec r) (choosePredecessor_exec (nodeAppended r))

def decideNode : Block 23 := .branch 8 .skip .skip acceptNode
def nodeDecided (r : State) : State := if ForwardEdge.present r.registers.output then nodeAccepted r else r
def decideFuel (r : State) : Nat := 1 + if ForwardEdge.present r.registers.output then acceptFuel r else 1
theorem decideNode_exec (r : State) : Exec decideNode r.store (decideFuel r) (nodeDecided r).store := by
  have checked := EdgeKinds.branch_head (8 : Fin 23) r.store .skip acceptNode 1 (acceptFuel r)
    r.store (nodeAccepted r).store (.skip _) (acceptNode_exec r)
  change Exec decideNode r.store (decideFuel r)
    (if ForwardEdge.present r.registers.output then (nodeAccepted r).store else r.store) at checked
  cases tag : ForwardEdge.present r.registers.output <;>
    simpa only [nodeDecided, tag, Bool.false_eq_true, ite_false, ite_true] using checked

def body : Block 23 := .seq probe decideNode
def bodyResult (r : State) : State := nodeDecided (probed r)
def bodyFuel (r : State) : Nat := probeFuel r + decideFuel (probed r)
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store :=
  Exec.seq (probe_exec r) (decideNode_exec (probed r))

theorem accepted_pending (r : State) :
    (nodeAccepted r).core.pending = if ForwardEdge.present r.parentBytes then r.core.pending else [] := by
  unfold nodeAccepted predecessorChosen
  rw [(nodeAppended_preserves r).2.2.2.2.1]
  cases tag : ForwardEdge.present r.parentBytes <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · rfl
  · exact (parentFollowed_preserves (nodeAppended r)).1.trans (nodeAppended_preserves r).1

theorem body_progress (r : State) (nonempty : r.core.pending ≠ []) :
    (bodyResult r).core.pending = [] ∨ (bodyResult r).core.pending.length < r.core.pending.length := by
  have shorter : (probed r).core.pending.length < r.core.pending.length := by
    rw [probed_pending]
    exact TraceData.next_shorter _ nonempty
  unfold bodyResult nodeDecided
  cases found : ForwardEdge.present (probed r).registers.output <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact Or.inr shorter
  · rw [accepted_pending]
    cases parent : ForwardEdge.present (probed r).parentBytes <;>
      simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact Or.inl (by trivial)
    · exact Or.inr shorter

def stepBound (r : State) : Nat := 47 * r.core.pending.length + 124
theorem bodyFuel_bound (r : State) : bodyFuel r ≤ stepBound r := by
  have probing := probeFuel_bound r
  have index := TraceData.nodeIndex_length r.core.pending
  have parent := parentBytes_bound r
  have predecessor := predecessorFuel_bound (nodeAppended (probed r))
  rw [(nodeAppended_preserves (probed r)).2.2.2.2.1] at predecessor
  change predecessorFuel (nodeAppended (probed r)) ≤ 4 * (nodeRead r).parentBytes.length + 20 at predecessor
  have node := (probed_nodes r).1
  unfold bodyFuel decideFuel acceptFuel appendFuel stepBound
  rw [node]
  cases found : ForwardEdge.present (probed r).registers.output <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem stepBound_mono (r : State) (nonempty : r.core.pending ≠ []) :
    stepBound (bodyResult r) ≤ stepBound r := by
  have progress := body_progress r nonempty
  unfold stepBound
  cases progress with
  | inl stopped => rw [stopped]; simp only [List.length_nil]; omega
  | inr shorter => omega

theorem accepted_preserves (r : State) :
    (nodeAccepted r).core.graph.core.formula = r.core.graph.core.formula ∧
      (nodeAccepted r).core.graph.core.matching = r.core.graph.core.matching := by
  have append := nodeAppended_preserves r
  unfold nodeAccepted predecessorChosen
  cases parent : ForwardEdge.present (nodeAppended r).parentBytes <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨append.2.2.2.2.2.1, append.2.2.2.2.2.2⟩
  · have follow := parentFollowed_preserves (nodeAppended r)
    exact ⟨follow.2.2.2.2.1.trans append.2.2.2.2.2.1, follow.2.2.2.2.2.trans append.2.2.2.2.2.2⟩

theorem body_preserves (r : State) :
    (bodyResult r).core.graph.core.formula = r.core.graph.core.formula ∧
      (bodyResult r).core.graph.core.matching = r.core.graph.core.matching := by
  have probe := probed_preserves r
  unfold bodyResult nodeDecided
  cases found : ForwardEdge.present (probed r).registers.output <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨probe.2.2.2.1, probe.2.2.2.2.1⟩
  · have accept := accepted_preserves (probed r)
    exact ⟨accept.1.trans probe.2.2.2.1, accept.2.trans probe.2.2.2.2.1⟩

end PNP.Concrete.NormalizerBlocks.TracePath
