/-
Copyright (c) 2026 PNP Labs.

A canonical observation view links the extractor's byte theorem back to
its live registers. The remaining list is compared by its actual encoded
bytes; no separate list-decoding assumption is needed by the trace caller.
-/

import PNP.Concrete.NormalizerExtractRange

namespace PNP.Concrete.NormalizerBlocks.Extraction

def readParent (input : BitString) : Option CNFLiteral :=
  if ForwardEdge.present input then some (TraceData.node input.tail) else none

theorem readParent_canonical (parent : Option CNFLiteral) (suffix : BitString) :
    readParent (TraceData.predecessor parent suffix) = parent := by
  cases parent with
  | none => rfl
  | some vertex =>
      cases vertex with
      | mk tag index =>
          simp only [readParent, TraceData.predecessor, TraceData.vertex, ForwardEdge.present,
            List.headD, List.tail_cons, ite_true, TraceData.node, TraceData.nodeIndex,
            BatchPacket.header_canonical, TableInit.canonicalHeader, List.length_replicate]

def view (input : BitString) : Option (TraceData.Row × BitString) :=
  if ForwardEdge.present input then
    some ((TraceData.node input.tail,
      readParent (TableInit.readCount input.tail.tail).state.input), TraceData.next input.tail)
  else none

theorem view_answer (result : Option Found) :
    view (answer result) = result.map (fun found => (found.1, SearchVertices.encodeVertices found.2)) := by
  cases result with
  | none => rfl
  | some found =>
      simp only [view, answer, ForwardEdge.present, List.headD, List.tail_cons, ite_true,
        TraceData.node_canonical, TraceData.next_canonical, Option.map_some]
      change some ((found.1.1, readParent
        (TableInit.readCount (TraceData.row found.1 (SearchVertices.encodeVertices found.2)).tail).state.input),
          SearchVertices.encodeVertices found.2) = _
      simp only [TraceData.row, TraceData.vertex, List.tail_cons, BatchPacket.header_canonical,
        TableInit.canonicalHeader, readParent_canonical]

def OutputMatches (r : State) : Option Found → Prop
  | none => r.parent.output = [false]
  | some found => Selected r found.1.1 found.1.2 found.2

theorem selection_matching (r : State) (unseen : List CNFLiteral) (trace : List TraceData.Row) (result : Option Found)
    (range : SelectionFrom unseen trace r) (observed : observation r = answer result) : OutputMatches r result := by
  cases range with
  | inl unavailable =>
      cases result with
      | none => exact unavailable
      | some found =>
          have noneRead := observation_none r unavailable
          have impossible : ([false] : BitString) = answer (some found) := noneRead.symm.trans observed
          cases impossible
  | inr available =>
      obtain ⟨vertex, parent, remaining, selected, _, _⟩ := available
      have exactBytes : answer (some ((vertex, parent), remaining)) = answer result :=
        selected.observation.symm.trans observed
      cases result with
      | none => cases exactBytes
      | some found =>
          have decoded := congrArg view exactBytes
          rw [view_answer, view_answer] at decoded
          have fields := Option.some.inj decoded
          have row : (vertex, parent) = found.1 := congrArg Prod.fst fields
          have rest : SearchVertices.encodeVertices remaining = SearchVertices.encodeVertices found.2 := congrArg Prod.snd fields
          have node : vertex = found.1.1 := congrArg Prod.fst row
          have predecessor : parent = found.1.2 := congrArg Prod.snd row
          constructor
          · rw [selected.indexRead, node]
          · rw [selected.tagRead, node]
          · rw [selected.parentRead, predecessor]
          · exact selected.remainingRead.trans rest
          · exact selected.activeRead

theorem whole_outcome (r : State) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) (unseen : List CNFLiteral)
    (data : Canonical r clauses entries trace unseen []) :
    OutputMatches (whole r).state (value clauses entries trace unseen) := by
  have layout : Layout r unseen [] trace :=
    ⟨data.pendingRead, data.skippedRead, data.traceRead, data.activeRead, data.initialAnswer⟩
  exact selection_matching _ unseen trace _ (whole_range r unseen trace layout)
    (whole_canonical r clauses entries trace unseen data)

end PNP.Concrete.NormalizerBlocks.Extraction
