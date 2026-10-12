/-
Copyright (c) 2026 PNP Labs.

Canonical meaning of ordered parent scanning. The invariant fixes only
encoded source data, never a supplied edge answer or a correctness oracle.
The returned predecessor is the first matching node in the original trace.
-/

import PNP.Concrete.NormalizerParentScan

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

structure Canonical (r : State) (target : CNFLiteral)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) : Prop where
  indexRead : r.targetIndex = List.replicate target.variableIndex true
  tagRead : ForwardEdge.present r.targetTag = target.positive
  formulaRead : r.graph.core.formula = GraphQuery.clauseData clauses
  matchingRead : r.graph.core.matching = MatchingTable.encode entries

theorem canonical_body (r : State) (target : CNFLiteral)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (data : Canonical r target clauses entries) : Canonical (bodyResult r) target clauses entries := by
  have stable := body_preserves r
  exact ⟨stable.1.trans data.indexRead, by rw [stable.2.1]; exact data.tagRead,
    stable.2.2.1.trans data.formulaRead, stable.2.2.2.trans data.matchingRead⟩

theorem edge_canonical (r : State) (source target : CNFLiteral)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (firstRead : ForwardEdge.present r.graph.first = source.positive)
    (secondRead : ForwardEdge.present r.graph.second = target.positive)
    (sourceRead : r.graph.core.target = List.replicate source.variableIndex true)
    (targetRead : r.graph.core.index = List.replicate target.variableIndex true)
    (formulaRead : r.graph.core.formula = GraphQuery.clauseData clauses)
    (matchingRead : r.graph.core.matching = MatchingTable.encode entries) :
    (edgeResult r).registers.output = [EdgeKinds.value source target clauses entries] := by
  change (EdgeKinds.dispatchResult r.graph).core.core.output = _
  rw [EdgeKinds.dispatch_output, firstRead, secondRead]
  cases first : source.positive <;> cases second : target.positive
  · simp only [EdgeKinds.value, first, second, Bool.false_eq_true, ite_false]
  · simp only [EdgeKinds.value, first, second, Bool.false_eq_true, ite_false, ite_true]
    exact EdgeKinds.reverse_canonical _ _ _ entries sourceRead targetRead matchingRead
  · simp only [EdgeKinds.value, first, second, Bool.false_eq_true, ite_false, ite_true]
    exact EdgeKinds.forward_canonical _ _ _ clauses entries sourceRead targetRead formulaRead matchingRead
  · simp only [EdgeKinds.value, first, second, ite_true]

theorem row_edge (r : State) (target : CNFLiteral)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (entry : TraceData.Row) (suffix : BitString)
    (data : Canonical r target clauses entries) (traceRead : r.pending = TraceData.row entry suffix) :
    (edgeResult (nodeResult r)).registers.output = [EdgeKinds.value entry.1 target clauses entries] := by
  have fields := node_fields r
  have stable := node_preserves r
  apply edge_canonical _ entry.1 target clauses entries
  · rw [fields.2.2.2.2.1, traceRead]
    rfl
  · rw [fields.2.2.2.2.2]
    exact data.tagRead
  · rw [fields.2.2.1, traceRead, TraceData.nodeIndex_canonical]
  · exact fields.2.2.2.1.trans data.indexRead
  · exact stable.2.2.1.trans data.formulaRead
  · exact stable.2.2.2.1.trans data.matchingRead

theorem body_row (r : State) (target : CNFLiteral)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (entry : TraceData.Row) (suffix : BitString)
    (data : Canonical r target clauses entries) (traceRead : r.pending = TraceData.row entry suffix) :
    (bodyResult r).pending = (if EdgeKinds.value entry.1 target clauses entries then [] else suffix) ∧
      (bodyResult r).output = (if EdgeKinds.value entry.1 target clauses entries
        then answer (some (some entry.1)) else r.output) := by
  have query := row_edge r target clauses entries entry suffix data traceRead
  have found : ForwardEdge.present (edgeResult (nodeResult r)).registers.output =
      EdgeKinds.value entry.1 target clauses entries := by rw [query]; rfl
  have next : (edgeResult (nodeResult r)).pending = suffix := by
    change (nodeResult r).pending = suffix
    rw [(node_fields r).1, traceRead, TraceData.next_canonical]
  have index : (edgeResult (nodeResult r)).currentIndex = List.replicate entry.1.variableIndex true := by
    change (nodeResult r).currentIndex = _
    rw [(node_fields r).2.1, traceRead, TraceData.nodeIndex_canonical]
  have tag : ForwardEdge.present (edgeResult (nodeResult r)).graph.first = entry.1.positive := by
    rw [(edge_data (nodeResult r)).1, (node_fields r).2.2.2.2.1, traceRead]
    rfl
  cases edge : EdgeKinds.value entry.1 target clauses entries with
  | false =>
      have selectedEq : bodyResult r = edgeResult (nodeResult r) := by
        unfold bodyResult selected
        rw [found, edge]
        rfl
      rw [selectedEq]
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨next, rfl⟩
  | true =>
      have selectedEq : bodyResult r = accepted (edgeResult (nodeResult r)) := by
        unfold bodyResult selected
        rw [found, edge]
        rfl
      rw [selectedEq]
      simp only [ite_true]
      constructor
      · rfl
      · change true :: true :: ForwardEdge.present (edgeResult (nodeResult r)).graph.first ::
          (edgeResult (nodeResult r)).currentIndex = _
        rw [tag, index]
        rfl

theorem scan_canonical (fuel : Nat) (r : State) (target : CNFLiteral)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : Canonical r target clauses entries) (traceRead : r.pending = TraceData.encode trace)
    (initialAnswer : r.output = answer none) (enough : r.pending.length < fuel) :
    (scan fuel r).state.output =
      answer ((trace.find? (fun entry => EdgeKinds.value entry.1 target clauses entries)).map (fun entry => some entry.1)) := by
  induction trace generalizing fuel r with
  | nil =>
      rw [scan_empty fuel r traceRead]
      exact initialAnswer
  | cons entry rest ih =>
      have nonempty : r.pending ≠ [] := by
        rw [traceRead]
        change (entry.1.positive :: _) ≠ []
        intro h
        cases h
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          rw [scan_step fuel r nonempty]
          have row := body_row r target clauses entries entry (TraceData.encode rest) data traceRead
          cases found : EdgeKinds.value entry.1 target clauses entries with
          | false =>
              have next : (bodyResult r).pending = TraceData.encode rest := by
                simpa only [found, Bool.false_eq_true, ite_false] using row.1
              have answerRead : (bodyResult r).output = answer none := by
                have same : (bodyResult r).output = r.output := by
                  simpa only [found, Bool.false_eq_true, ite_false] using row.2
                exact same.trans initialAnswer
              have shorter : (bodyResult r).pending.length < r.pending.length := by
                rw [next, ← TraceData.next_canonical entry (TraceData.encode rest)]
                change (TraceData.next (TraceData.encode (entry :: rest))).length < _
                rw [← traceRead]
                exact TraceData.next_shorter _ nonempty
              have remaining : (bodyResult r).pending.length < fuel := by omega
              have checked := ih fuel (bodyResult r) (canonical_body r target clauses entries data) next answerRead remaining
              simpa only [List.find?_cons, found, Bool.false_eq_true, ite_false] using checked
          | true =>
              have stopped : (bodyResult r).pending = [] := by simpa only [found, ite_true] using row.1
              rw [scan_empty fuel (bodyResult r) stopped]
              simpa only [List.find?_cons, found, ite_true, Option.map_some] using row.2

theorem whole_canonical (r : State) (target : CNFLiteral)
    (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (data : Canonical r target clauses entries) (traceRead : r.pending = TraceData.encode trace)
    (initialAnswer : r.output = answer none) :
    (whole r).state.output =
      answer ((trace.find? (fun entry => EdgeKinds.value entry.1 target clauses entries)).map (fun entry => some entry.1)) :=
  scan_canonical _ r target clauses entries trace data traceRead initialAnswer (Nat.lt_succ_self _)

end PNP.Concrete.NormalizerBlocks.ParentQuery
