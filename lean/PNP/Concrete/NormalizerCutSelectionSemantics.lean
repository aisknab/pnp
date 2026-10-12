/-
Copyright (c) 2026 PNP Labs.

Exact source-order filtering for the whole finite range. Trace row order,
duplicate rows and predecessor-only appearances cannot reorder or add indices.
The result is proved for arbitrary counts and offsets, not a fixed fixture.
-/
import PNP.Concrete.NormalizerCutSelectionRange

namespace PNP.Concrete.NormalizerBlocks.CutSelection

def selected (tag : Bool) (trace : List TraceData.Row) (count index : Nat) : List CNFLiteral :=
  (SearchVertices.rangeData tag count index).filter (fun vertex => TraceMember.value vertex trace)
def selectedBits (tag : Bool) (trace : List TraceData.Row) (count index : Nat) : BitString :=
  UnseenData.prefixBits (selected tag trace count index)

theorem selectedBits_zero (tag : Bool) (trace : List TraceData.Row) (index : Nat) :
    selectedBits tag trace 0 index = [] := rfl
theorem selectedBits_succ (tag : Bool) (trace : List TraceData.Row) (count index : Nat) :
    selectedBits tag trace (count + 1) index =
      if TraceMember.value ⟨tag,index⟩ trace then
        SearchVertices.entryBits tag index ++ selectedBits tag trace count (index + 1)
      else selectedBits tag trace count (index + 1) := by
  cases member : TraceMember.value ⟨tag,index⟩ trace <;>
    simp only [selectedBits, selected, SearchVertices.rangeData, List.filter_cons, member,
      Bool.false_eq_true, ite_false, ite_true, UnseenData.prefixBits, UnseenData.entry]

theorem selected_finRange (tag : Bool) (trace : List TraceData.Row) (count index : Nat) :
    selected tag trace count index =
      ((List.finRange count).filter (fun i => TraceMember.value ⟨tag,index + i.val⟩ trace)).map
        (fun i => (⟨tag,index + i.val⟩ : CNFLiteral)) := by
  rw [selected, SearchVertices.rangeData_finRange, List.filter_map]
  rfl

theorem selected_length (tag : Bool) (trace : List TraceData.Row) (count index : Nat) :
    (selected tag trace count index).length ≤ count := by
  have bound := List.length_filter_le (fun vertex => TraceMember.value vertex trace)
    (SearchVertices.rangeData tag count index)
  rw [SearchVertices.rangeData_length] at bound
  exact bound

theorem run_buffer (tag : Bool) (word : BitString) (r : State)
    (index : Nat) (trace : List TraceData.Row)
    (indexRead : r.core.targetIndex = List.replicate index true)
    (tagRead : ForwardEdge.present r.core.targetTag = tag)
    (traceRead : r.trace = TraceData.encode trace) :
    (run tag word r).state.buffer =
      (selectedBits tag trace word.length index).reverse ++ r.buffer := by
  induction word generalizing r index with
  | nil => rfl
  | cons bit rest ih =>
    let before : State := {r with remaining := bit :: rest}
    let next := stepped tag before
    have frame := stepped_frame tag before
    have nextIndex : next.core.targetIndex = List.replicate (index + 1) true := by
      rw [frame.2.2.1, indexRead, List.replicate_succ]
    have nextTag : ForwardEdge.present next.core.targetTag = tag := by
      rw [frame.2.2.2]
      exact tagRead
    have nextTrace : next.trace = TraceData.encode trace := frame.1.trans traceRead
    have tail := ih next (index + 1) nextIndex nextTag nextTrace
    have head := stepped_buffer before tag index trace indexRead tagRead traceRead
    change (run tag rest next).state.buffer = _
    rw [tail]
    change (selectedBits tag trace rest.length (index + 1)).reverse ++ (stepped tag before).buffer = _
    rw [head]
    change (selectedBits tag trace rest.length (index + 1)).reverse ++
      (if TraceMember.value ⟨tag,index⟩ trace then
        (SearchVertices.entryBits tag index).reverse ++ r.buffer else r.buffer) = _
    rw [List.length_cons, selectedBits_succ]
    cases member : TraceMember.value ⟨tag,index⟩ trace <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, List.reverse_append, List.append_assoc]

theorem whole_buffer (tag : Bool) (r : State) (index : Nat) (trace : List TraceData.Row)
    (indexRead : r.core.targetIndex = List.replicate index true)
    (tagRead : ForwardEdge.present r.core.targetTag = tag)
    (traceRead : r.trace = TraceData.encode trace) :
    (whole tag r).state.buffer =
      (selectedBits tag trace r.remaining.length index).reverse ++ r.buffer :=
  run_buffer tag r.remaining r index trace indexRead tagRead traceRead

end PNP.Concrete.NormalizerBlocks.CutSelection
