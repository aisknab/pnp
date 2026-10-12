/-
Copyright (c) 2026 PNP Labs.

One complete cut-selection step queries the stored trace, conditionally emits
the current index, and advances the finite range. The queried index and vertex
kind survive the membership call; predecessor metadata cannot supply a match.
-/
import PNP.Concrete.NormalizerCutSelectionState

namespace PNP.Concrete.NormalizerBlocks.CutSelection
open BitRegister Occurrence

theorem chosen_frame (tag : Bool) (r : State) :
    (chosen tag r).trace = r.trace ∧ (chosen tag r).remaining = r.remaining ∧
      (chosen tag r).core.targetIndex = r.core.targetIndex ∧
        (chosen tag r).core.targetTag = r.core.targetTag := by
  cases found : ForwardEdge.present r.core.output with
  | false =>
    simp only [chosen, found, Bool.false_eq_true, ite_false]
    trivial
  | true =>
    simpa only [chosen, found, ite_true] using emitted_frame tag r

theorem chooseFuel_bound (r : State) : chooseFuel r ≤ 4 * r.core.targetIndex.length + 14 := by
  cases found : ForwardEdge.present r.core.output <;>
    simp only [chooseFuel, emitFuel, found, Bool.false_eq_true, ite_false, ite_true] <;> omega

def advance : Block 24 := .seq (.action (.pop 22)) (.action (.push 17 true))
def advanced (r : State) : State :=
  {r with remaining := r.remaining.tail, core := {r.core with targetIndex := true :: r.core.targetIndex}}
theorem advance_exec (r : State) : Exec advance r.store 2 (advanced r).store :=
  Exec.seq (.action _ _) (.action _ _)

def step (tag : Bool) : Block 24 := .seq query (.seq (choose tag) advance)
def stepped (tag : Bool) (r : State) : State := advanced (chosen tag (queried r))
def stepFuel (r : State) : Nat := queryFuel r + (chooseFuel (queried r) + 2)
theorem step_exec (tag : Bool) (r : State) :
    Exec (step tag) r.store (stepFuel r) (stepped tag r).store :=
  Exec.seq (query_exec r) (Exec.seq (choose_exec tag (queried r)) (advance_exec _))

theorem stepped_frame (tag : Bool) (r : State) :
    (stepped tag r).trace = r.trace ∧
      (stepped tag r).remaining = r.remaining.tail ∧
      (stepped tag r).core.targetIndex = true :: r.core.targetIndex ∧
      (stepped tag r).core.targetTag = r.core.targetTag := by
  have q := queried_frame r
  have c := chosen_frame tag (queried r)
  refine ⟨c.1.trans q.1, ?_, ?_, c.2.2.2.trans q.2.2.2.2⟩
  · change (chosen tag (queried r)).remaining.tail = r.remaining.tail
    rw [c.2.1, q.2.1]
  · change true :: (chosen tag (queried r)).core.targetIndex = true :: r.core.targetIndex
    rw [c.2.2.1, q.2.2.2.1]

def stepBound (traceSize indexSize : Nat) : Nat :=
  (28 * traceSize + 81) * (traceSize + 1) + 4 * indexSize + 20
theorem stepFuel_bound (r : State) :
    stepFuel r ≤ stepBound r.trace.length r.core.targetIndex.length := by
  have queryBound := queryFuel_bound r
  have emission := chooseFuel_bound (queried r)
  rw [(queried_frame r).2.2.2.1] at emission
  unfold stepFuel stepBound
  omega

theorem query_canonical (r : State) (tag : Bool) (index : Nat) (trace : List TraceData.Row)
    (indexRead : r.core.targetIndex = List.replicate index true)
    (tagRead : ForwardEdge.present r.core.targetTag = tag)
    (traceRead : r.trace = TraceData.encode trace) :
    (queried r).core.output = [TraceMember.value ⟨tag,index⟩ trace] :=
  TraceMember.phase_canonical (traceLoaded r).core ⟨tag,index⟩ trace indexRead tagRead traceRead

theorem stepped_buffer (r : State) (tag : Bool) (index : Nat) (trace : List TraceData.Row)
    (indexRead : r.core.targetIndex = List.replicate index true)
    (tagRead : ForwardEdge.present r.core.targetTag = tag)
    (traceRead : r.trace = TraceData.encode trace) :
    (stepped tag r).buffer =
      if TraceMember.value ⟨tag,index⟩ trace then
        (SearchVertices.entryBits tag index).reverse ++ r.buffer else r.buffer := by
  have answer := query_canonical r tag index trace indexRead tagRead traceRead
  have found : ForwardEdge.present (queried r).core.output =
      TraceMember.value ⟨tag,index⟩ trace := by
    rw [answer]
    rfl
  change (chosen tag (queried r)).buffer = _
  cases member : TraceMember.value ⟨tag,index⟩ trace with
  | false =>
    simp only [chosen, found, member, Bool.false_eq_true, ite_false]
    exact (queried_frame r).2.2.1
  | true =>
    simp only [chosen, found, member, ite_true]
    rw [emitted_buffer, (queried_frame r).2.2.2.1, indexRead,
      List.length_replicate, (queried_frame r).2.2.1]

end PNP.Concrete.NormalizerBlocks.CutSelection
