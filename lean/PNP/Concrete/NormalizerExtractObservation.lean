/-
Copyright (c) 2026 PNP Labs.

Byte-level observation of an extracted vertex and optional computed parent.
Canonical invariants bind only the actual formula, matching, full trace and
ordered vertex list. They never assume an eligibility answer.
-/

import PNP.Concrete.NormalizerExtractScan

namespace PNP.Concrete.NormalizerBlocks.Extraction

def parentBytes (word suffix : BitString) : BitString :=
  if ForwardEdge.present word.tail then
    true :: ForwardEdge.present word.tail.tail ::
      (List.replicate word.tail.tail.tail.length true ++ false :: suffix)
  else false :: suffix

def observation (r : State) : BitString :=
  if ForwardEdge.present r.parent.output then
    true :: TraceData.vertex ⟨ForwardEdge.present r.parent.targetTag, r.parent.targetIndex.length⟩
      (parentBytes r.parent.output (r.skipped.reverse ++ r.pending))
  else [false]

theorem parentBytes_canonical (parent : Option CNFLiteral) (suffix : BitString) :
    parentBytes (ParentQuery.answer (some parent)) suffix = TraceData.predecessor parent suffix := by
  cases parent with
  | none => rfl
  | some vertex =>
      simp only [parentBytes, ParentQuery.answer, ForwardEdge.present, List.tail_cons, List.headD,
        ite_true, List.length_replicate, TraceData.predecessor, TraceData.vertex, TableInit.encodeCount]

theorem observation_none (r : State) (unavailable : r.parent.output = [false]) :
    observation r = answer none := by
  unfold observation
  rw [unavailable]
  rfl

theorem observation_some (r : State) (vertex : CNFLiteral) (parent : Option CNFLiteral)
    (skipped rest : List CNFLiteral)
    (indexRead : r.parent.targetIndex = List.replicate vertex.variableIndex true)
    (tagRead : ForwardEdge.present r.parent.targetTag = vertex.positive)
    (parentRead : r.parent.output = ParentQuery.answer (some parent))
    (skippedRead : r.skipped = (UnseenData.prefixBits skipped).reverse)
    (pendingRead : r.pending = SearchVertices.encodeVertices rest) :
    observation r = answer (some ((vertex, parent), skipped ++ rest)) := by
  have present : ForwardEdge.present (ParentQuery.answer (some parent)) = true := by cases parent <;> rfl
  unfold observation
  rw [parentRead, present, if_pos rfl, indexRead, List.length_replicate, tagRead,
    skippedRead, List.reverse_reverse, pendingRead, parentBytes_canonical]
  have joined : UnseenData.prefixBits skipped ++ SearchVertices.encodeVertices rest =
      SearchVertices.encodeVertices (skipped ++ rest) := by
    rw [UnseenData.encoded_prefix, UnseenData.encoded_prefix, UnseenData.prefix_append, List.append_assoc]
  rw [joined]
  rfl

structure Canonical (r : State) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) (unseen skipped : List CNFLiteral) : Prop where
  formulaRead : r.parent.graph.core.formula = GraphQuery.clauseData clauses
  matchingRead : r.parent.graph.core.matching = MatchingTable.encode entries
  traceRead : r.trace = TraceData.encode trace
  pendingRead : r.pending = SearchVertices.encodeVertices unseen
  skippedRead : r.skipped = (UnseenData.prefixBits skipped).reverse
  activeRead : r.active = [true]
  initialAnswer : r.parent.output = [false]

structure QueriedVertex (r : State) (vertex : CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) (rest skipped : List CNFLiteral) : Prop where
  data : ParentQuery.Canonical r.parent vertex clauses entries
  answerRead : r.parent.output = ParentQuery.answer (Eligibility.value vertex clauses entries trace)
  pendingRead : r.pending = SearchVertices.encodeVertices rest
  skippedRead : r.skipped = (UnseenData.prefixBits skipped).reverse
  traceRead : r.trace = TraceData.encode trace
  activeRead : r.active = [true]

theorem query_after_read (r : State) (vertex : CNFLiteral) (rest skipped : List CNFLiteral)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : Canonical r clauses entries trace (vertex :: rest) skipped) :
    QueriedVertex (queried (vertexRead r)) vertex clauses entries trace rest skipped := by
  have parsed := read_canonical r vertex rest data.pendingRead
  have read := read_fields r
  have query := query_fields (vertexRead r)
  have parsedData : ParentQuery.Canonical (vertexRead r).parent vertex clauses entries :=
    ⟨parsed.1, parsed.2.1, read.2.2.2.1.trans data.formulaRead,
      read.2.2.2.2.1.trans data.matchingRead⟩
  exact ⟨⟨query.1.trans parsed.1, by rw [query.2.1]; exact parsed.2.1,
      query.2.2.1.trans parsedData.formulaRead, query.2.2.2.1.trans parsedData.matchingRead⟩,
    query_canonical _ vertex clauses entries trace parsedData data.traceRead,
    query.2.2.2.2.1.trans parsed.2.2, query.2.2.2.2.2.1.trans data.skippedRead,
    query.2.2.2.2.2.2.1.trans data.traceRead, query.2.2.2.2.2.2.2.trans data.activeRead⟩

theorem body_cons (r : State) (vertex : CNFLiteral) (rest : List CNFLiteral)
    (pending : r.pending = SearchVertices.encodeVertices (vertex :: rest)) :
    bodyResult r = visited r := by
  simp only [bodyResult, pending, UnseenData.encoded_cons, UnseenData.entry_shape]

theorem body_missing (r : State) (vertex : CNFLiteral) (rest skipped : List CNFLiteral)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : Canonical r clauses entries trace (vertex :: rest) skipped)
    (missing : Eligibility.value vertex clauses entries trace = none) :
    Canonical (bodyResult r) clauses entries trace rest (skipped ++ [vertex]) := by
  have checked := query_after_read r vertex rest skipped clauses entries trace data
  have output : (queried (vertexRead r)).parent.output = [false] := by
    rw [checked.answerRead, missing]
    rfl
  have same : bodyResult r = appended (queried (vertexRead r)) := by
    rw [body_cons r vertex rest data.pendingRead]
    unfold visited chosen
    rw [output]
    rfl
  rw [same]
  have stable := append_fields (queried (vertexRead r))
  constructor
  · exact stable.2.2.2.1.trans checked.data.formulaRead
  · exact stable.2.2.2.2.1.trans checked.data.matchingRead
  · exact stable.2.2.2.2.2.2.1.trans checked.traceRead
  · exact stable.2.2.2.2.2.1.trans checked.pendingRead
  · rw [append_canonical _ vertex checked.data.indexRead checked.data.tagRead, checked.skippedRead]
    simp only [UnseenData.prefix_append, UnseenData.prefixBits, List.append_nil, List.reverse_append]
  · exact stable.2.2.2.2.2.2.2.1.trans checked.activeRead
  · exact stable.2.2.1.trans output

theorem body_found (r : State) (vertex : CNFLiteral) (parent : Option CNFLiteral)
    (rest skipped : List CNFLiteral) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : Canonical r clauses entries trace (vertex :: rest) skipped)
    (found : Eligibility.value vertex clauses entries trace = some parent) :
    (bodyResult r).active = [] ∧ observation (bodyResult r) = answer (some ((vertex, parent), skipped ++ rest)) := by
  have checked := query_after_read r vertex rest skipped clauses entries trace data
  have output : (queried (vertexRead r)).parent.output = ParentQuery.answer (some parent) :=
    checked.answerRead.trans (congrArg ParentQuery.answer found)
  have present : ForwardEdge.present (queried (vertexRead r)).parent.output = true := by
    rw [output]
    cases parent <;> rfl
  have same : bodyResult r = stopped (queried (vertexRead r)) := by
    rw [body_cons r vertex rest data.pendingRead]
    unfold visited chosen
    rw [present]
    rfl
  rw [same]
  exact ⟨rfl, observation_some _ vertex parent skipped rest checked.data.indexRead
    checked.data.tagRead output checked.skippedRead checked.pendingRead⟩

end PNP.Concrete.NormalizerBlocks.Extraction
