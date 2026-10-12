/-
Copyright (c) 2026 PNP Labs.

Structural extraction invariants with arbitrary raw graph data. A successful
extraction removes one actual unseen vertex, preserves the remaining byte
layout, and returns either no predecessor or an actual previous trace node.
These facts supply the whole exploration size bound independently of the
stronger canonical graph semantics proved for the extractor.
-/

import PNP.Concrete.NormalizerExplorationData

namespace PNP.Concrete.NormalizerBlocks.Extraction

structure Layout (r : State) (unseen skipped : List CNFLiteral) (trace : List TraceData.Row) : Prop where
  pendingRead : r.pending = SearchVertices.encodeVertices unseen
  skippedRead : r.skipped = (UnseenData.prefixBits skipped).reverse
  traceRead : r.trace = TraceData.encode trace
  activeRead : r.active = [true]
  initialAnswer : r.parent.output = [false]

def ParentWithin (trace : List TraceData.Row) (parent : Option CNFLiteral) : Prop :=
  ∀ vertex, parent = some vertex → ∃ entry, entry ∈ trace ∧ entry.1 = vertex

structure Selected (r : State) (vertex : CNFLiteral) (parent : Option CNFLiteral) (remaining : List CNFLiteral) : Prop where
  indexRead : r.parent.targetIndex = List.replicate vertex.variableIndex true
  tagRead : ForwardEdge.present r.parent.targetTag = vertex.positive
  parentRead : r.parent.output = ParentQuery.answer (some parent)
  remainingRead : r.skipped.reverse ++ r.pending = SearchVertices.encodeVertices remaining
  activeRead : r.active = []

def SelectionFrom (unseen : List CNFLiteral) (trace : List TraceData.Row) (r : State) : Prop :=
  r.parent.output = [false] ∨ ∃ vertex parent remaining,
    Selected r vertex parent remaining ∧ ExplorationData.Removes vertex unseen remaining ∧ ParentWithin trace parent

structure QueryLayout (r : State) (vertex : CNFLiteral) (rest skipped : List CNFLiteral)
    (trace : List TraceData.Row) : Prop where
  indexRead : r.parent.targetIndex = List.replicate vertex.variableIndex true
  tagRead : ForwardEdge.present r.parent.targetTag = vertex.positive
  allowed : ParentQuery.AnswerFrom trace r.parent.output
  pendingRead : r.pending = SearchVertices.encodeVertices rest
  skippedRead : r.skipped = (UnseenData.prefixBits skipped).reverse
  traceRead : r.trace = TraceData.encode trace
  activeRead : r.active = [true]

theorem query_layout (r : State) (vertex : CNFLiteral) (rest skipped : List CNFLiteral)
    (trace : List TraceData.Row) (data : Layout r (vertex :: rest) skipped trace) :
    QueryLayout (queried (vertexRead r)) vertex rest skipped trace := by
  have parsed := read_canonical r vertex rest data.pendingRead
  have fields := query_fields (vertexRead r)
  exact ⟨fields.1.trans parsed.1, by rw [fields.2.1]; exact parsed.2.1,
    query_from (vertexRead r) trace data.traceRead,
    fields.2.2.2.2.1.trans parsed.2.2, fields.2.2.2.2.2.1.trans data.skippedRead,
    fields.2.2.2.2.2.2.1.trans data.traceRead, fields.2.2.2.2.2.2.2.trans data.activeRead⟩

theorem body_missing_layout (r : State) (vertex : CNFLiteral) (rest skipped : List CNFLiteral)
    (trace : List TraceData.Row) (data : Layout r (vertex :: rest) skipped trace)
    (missing : ForwardEdge.present (queried (vertexRead r)).parent.output = false) :
    Layout (bodyResult r) rest (skipped ++ [vertex]) trace := by
  have checked := query_layout r vertex rest skipped trace data
  have output := checked.allowed.unavailable_eq _ _ missing
  have same : bodyResult r = appended (queried (vertexRead r)) := by
    rw [body_cons r vertex rest data.pendingRead]
    unfold visited chosen
    rw [missing]
    rfl
  rw [same]
  have stable := append_fields (queried (vertexRead r))
  constructor
  · exact stable.2.2.2.2.2.1.trans checked.pendingRead
  · rw [append_canonical _ vertex checked.indexRead checked.tagRead, checked.skippedRead]
    simp only [UnseenData.prefix_append, UnseenData.prefixBits, List.append_nil, List.reverse_append]
  · exact stable.2.2.2.2.2.2.1.trans checked.traceRead
  · exact stable.2.2.2.2.2.2.2.1.trans checked.activeRead
  · exact stable.2.2.1.trans output

theorem joined_vertices (skipped rest : List CNFLiteral) :
    UnseenData.prefixBits skipped ++ SearchVertices.encodeVertices rest = SearchVertices.encodeVertices (skipped ++ rest) := by
  rw [UnseenData.encoded_prefix, UnseenData.encoded_prefix, UnseenData.prefix_append, List.append_assoc]

theorem body_selected_layout (r : State) (vertex : CNFLiteral) (rest skipped : List CNFLiteral)
    (trace : List TraceData.Row) (data : Layout r (vertex :: rest) skipped trace)
    (found : ForwardEdge.present (queried (vertexRead r)).parent.output = true) :
    ∃ parent, Selected (bodyResult r) vertex parent (skipped ++ rest) ∧ ParentWithin trace parent := by
  have checked := query_layout r vertex rest skipped trace data
  obtain ⟨parent, output, origin⟩ := checked.allowed.available _ _ found
  have same : bodyResult r = stopped (queried (vertexRead r)) := by
    rw [body_cons r vertex rest data.pendingRead]
    unfold visited chosen
    rw [found]
    rfl
  rw [same]
  refine ⟨parent, ⟨checked.indexRead, checked.tagRead, output, ?_, rfl⟩, origin⟩
  change (queried (vertexRead r)).skipped.reverse ++ (queried (vertexRead r)).pending = _
  rw [checked.skippedRead, List.reverse_reverse, checked.pendingRead, joined_vertices]

theorem layout_active (r : State) (unseen skipped : List CNFLiteral) (trace : List TraceData.Row)
    (data : Layout r unseen skipped trace) : r.active ≠ [] := by
  rw [data.activeRead]
  intro h
  cases h

theorem scan_range (fuel : Nat) (r : State) (unseen skipped : List CNFLiteral) (trace : List TraceData.Row)
    (data : Layout r unseen skipped trace) (enough : r.pending.length < fuel) :
    SelectionFrom (skipped ++ unseen) trace (scan fuel r).state := by
  induction unseen generalizing fuel r skipped with
  | nil =>
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          rw [scan_step fuel r (layout_active r [] skipped trace data)]
          have pending : r.pending = [true, false] := data.pendingRead
          have stop : bodyResult r = stopped r := by simp only [bodyResult, pending]
          rw [stop, scan_empty fuel (stopped r) rfl]
          exact Or.inl data.initialAnswer
  | cons vertex rest ih =>
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          rw [scan_step fuel r (layout_active r (vertex :: rest) skipped trace data)]
          cases found : ForwardEdge.present (queried (vertexRead r)).parent.output with
          | false =>
              have nextData := body_missing_layout r vertex rest skipped trace data found
              have nonempty : r.pending ≠ [] := by
                rw [data.pendingRead, UnseenData.encoded_cons, UnseenData.entry_shape]
                intro h
                cases h
              have smaller : (bodyResult r).pending.length < r.pending.length := by
                rw [body_cons r vertex rest data.pendingRead, (visit_fields r).2.2.2]
                exact UnseenData.next_shorter _ nonempty
              have nextEnough : (bodyResult r).pending.length < fuel := by omega
              have checked := ih fuel (bodyResult r) (skipped ++ [vertex]) nextData nextEnough
              simpa only [List.append_assoc, List.cons_append, List.nil_append] using checked
          | true =>
              obtain ⟨parent, selected, origin⟩ := body_selected_layout r vertex rest skipped trace data found
              rw [scan_empty fuel (bodyResult r) selected.activeRead]
              exact Or.inr ⟨vertex, parent, skipped ++ rest, selected,
                (ExplorationData.Removes.head rest).prefixed skipped, origin⟩

theorem whole_range (r : State) (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (data : Layout r unseen [] trace) : SelectionFrom unseen trace (whole r).state := by
  exact scan_range _ r unseen [] trace data (Nat.lt_succ_self _)

theorem Selected.observation {r : State} {vertex : CNFLiteral} {parent : Option CNFLiteral}
    {remaining : List CNFLiteral} (selected : Selected r vertex parent remaining) :
    observation r = answer (some ((vertex, parent), remaining)) := by
  have present : ForwardEdge.present (ParentQuery.answer (some parent)) = true := by cases parent <;> rfl
  unfold Extraction.observation
  rw [selected.parentRead, present, if_pos rfl, selected.indexRead, List.length_replicate,
    selected.tagRead, selected.remainingRead, parentBytes_canonical]
  rfl

theorem Selected.sizes {r : State} {vertex : CNFLiteral} {parent : Option CNFLiteral}
    {remaining : List CNFLiteral} (selected : Selected r vertex parent remaining) :
    r.skipped.length ≤ (SearchVertices.encodeVertices remaining).length ∧
      r.pending.length ≤ (SearchVertices.encodeVertices remaining).length := by
  have size := congrArg List.length selected.remainingRead
  simp only [List.length_append, List.length_reverse] at size
  exact ⟨by omega, by omega⟩

end PNP.Concrete.NormalizerBlocks.Extraction
