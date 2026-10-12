/-
Copyright (c) 2026 PNP Labs.

Complete first-eligible extraction semantics for arbitrary finite lists.
Skipped vertices are retained in their original order, while the selected
vertex is removed exactly once. Eligibility uses actual formula, matching
and trace data rather than a supplied decision certificate.
-/

import PNP.Concrete.NormalizerExtractObservation

namespace PNP.Concrete.NormalizerBlocks.Extraction

def retain (skipped : List CNFLiteral) (result : Option Found) : Option Found :=
  result.map (fun found => (found.1, skipped ++ found.2))

theorem retain_nil (result : Option Found) : retain [] result = result := by
  cases result <;> rfl

theorem retain_cons (skipped : List CNFLiteral) (vertex : CNFLiteral) (result : Option Found) :
    retain skipped (result.map (fun found => (found.1, vertex :: found.2))) =
      retain (skipped ++ [vertex]) result := by
  cases result <;>
    simp only [retain, Option.map_none, Option.map_some, List.append_assoc, List.cons_append, List.nil_append]

theorem canonical_active (r : State) (clauses : List (List CNFLiteral)) (entries : MatchingTable.Entries)
    (trace : List TraceData.Row) (unseen skipped : List CNFLiteral)
    (data : Canonical r clauses entries trace unseen skipped) : r.active ≠ [] := by
  rw [data.activeRead]
  intro h
  cases h

theorem scan_canonical (fuel : Nat) (r : State) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) (unseen skipped : List CNFLiteral)
    (data : Canonical r clauses entries trace unseen skipped) (enough : r.pending.length < fuel) :
    observation (scan fuel r).state = answer (retain skipped (value clauses entries trace unseen)) := by
  induction unseen generalizing fuel r skipped with
  | nil =>
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          rw [scan_step fuel r (canonical_active r clauses entries trace [] skipped data)]
          have pending : r.pending = [true, false] := data.pendingRead
          have stop : bodyResult r = stopped r := by
            simp only [bodyResult, pending]
          rw [stop, scan_empty fuel (stopped r) rfl]
          exact observation_none (stopped r) data.initialAnswer
  | cons vertex rest ih =>
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          rw [scan_step fuel r (canonical_active r clauses entries trace (vertex :: rest) skipped data)]
          cases found : Eligibility.value vertex clauses entries trace with
          | none =>
              have nextData := body_missing r vertex rest skipped clauses entries trace data found
              have nonempty : r.pending ≠ [] := by
                rw [data.pendingRead, UnseenData.encoded_cons, UnseenData.entry_shape]
                intro h
                cases h
              have smaller : (bodyResult r).pending.length < r.pending.length := by
                rw [body_cons r vertex rest data.pendingRead, (visit_fields r).2.2.2]
                exact UnseenData.next_shorter _ nonempty
              have nextEnough : (bodyResult r).pending.length < fuel := by omega
              have checked := ih fuel (bodyResult r) (skipped ++ [vertex]) nextData nextEnough
              simpa only [value, found, retain_cons] using checked
          | some parent =>
              have checked := body_found r vertex parent rest skipped clauses entries trace data found
              rw [scan_empty fuel (bodyResult r) checked.1]
              simpa only [value, found, retain, Option.map_some] using checked.2

theorem whole_canonical (r : State) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) (trace : List TraceData.Row) (unseen : List CNFLiteral)
    (data : Canonical r clauses entries trace unseen []) :
    observation (whole r).state = answer (value clauses entries trace unseen) := by
  have checked := scan_canonical (r.pending.length + 1) r clauses entries trace unseen [] data (Nat.lt_succ_self _)
  simpa only [whole, retain_nil] using checked

end PNP.Concrete.NormalizerBlocks.Extraction
