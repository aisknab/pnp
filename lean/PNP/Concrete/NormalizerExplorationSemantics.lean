/-
Copyright (c) 2026 PNP Labs.

Exact all-finite trace semantics of the concrete exploration loop. Each
iteration uses the source extractor on the current trace, retains its
ordered remainder, and prepends the computed vertex/parent pair.
-/

import PNP.Concrete.NormalizerExplorationScan

namespace PNP.Concrete.NormalizerBlocks.Exploration

def value (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries) :
    Nat → List CNFLiteral → List TraceData.Row → List TraceData.Row
  | 0, _, trace => trace
  | fuel + 1, unseen, trace =>
      match Extraction.value clauses entries trace unseen with
      | none => trace
      | some (entry, rest) => value clauses entries fuel rest (entry :: trace)

theorem scan_value (fuel : Nat) (r : State) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (formulaRead : r.core.parent.graph.core.formula = GraphQuery.clauseData clauses)
    (matchingRead : r.core.parent.graph.core.matching = MatchingTable.encode entries)
    (pendingRead : r.core.pending = SearchVertices.encodeVertices unseen)
    (traceRead : r.core.trace = TraceData.encode trace)
    (enough : r.remaining.length < fuel) :
    (scan fuel r).state.core.trace = TraceData.encode (value clauses entries r.remaining.length unseen trace) := by
  induction fuel generalizing r unseen trace with
  | zero => exact False.elim (Nat.not_lt_zero _ enough)
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil =>
          simp only [scan, remaining, List.length_nil, value]
          exact traceRead
      | cons bit tail =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro h; cases h
          rw [scan_step fuel r nonempty]
          change (scan fuel (bodyResult r)).state.core.trace = _
          rw [List.length_cons, value]
          cases selected : Extraction.value clauses entries trace unseen with
          | none =>
              have stopped := body_none r clauses entries unseen trace formulaRead matchingRead pendingRead traceRead selected
              rw [scan_empty fuel (bodyResult r) stopped.1]
              exact stopped.2
          | some found =>
              obtain ⟨⟨vertex, parent⟩, rest⟩ := found
              have step := body_some r clauses entries unseen trace vertex parent rest
                formulaRead matchingRead pendingRead traceRead selected
              have enoughNext : (bodyResult r).remaining.length < fuel := by
                rw [step.1, remaining]
                simp only [List.tail_cons]
                rw [remaining, List.length_cons] at enough
                omega
              have stable := body_preserves r
              have next := ih (bodyResult r) rest ((vertex, parent) :: trace)
                (stable.1.trans formulaRead) (stable.2.trans matchingRead) step.2.1 step.2.2 enoughNext
              simpa only [step.1, remaining, List.tail_cons] using next

theorem whole_value (r : State) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (unseen : List CNFLiteral) (trace : List TraceData.Row)
    (formulaRead : r.core.parent.graph.core.formula = GraphQuery.clauseData clauses)
    (matchingRead : r.core.parent.graph.core.matching = MatchingTable.encode entries)
    (pendingRead : r.core.pending = SearchVertices.encodeVertices unseen)
    (traceRead : r.core.trace = TraceData.encode trace) :
    (whole r).state.core.trace = TraceData.encode (value clauses entries r.remaining.length unseen trace) :=
  scan_value _ r clauses entries unseen trace formulaRead matchingRead pendingRead traceRead (Nat.lt_succ_self _)

end PNP.Concrete.NormalizerBlocks.Exploration
