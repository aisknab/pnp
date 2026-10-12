/-
Copyright (c) 2026 PNP Labs.

Exact one-step candidate behavior on encoded matching and trace-node tables.
Both lookups are machine executions. These contracts do not claim that the
enclosing search has already constructed the trace.
-/

import PNP.Concrete.NormalizerCandidateLoop

namespace PNP.Concrete.NormalizerBlocks.Candidate

theorem result_canonical (r : State) (index : Nat) (matching seen : MatchingTable.Entries)
    (target : r.core.target = List.replicate index true)
    (matchedTable : r.matching = MatchingTable.encode matching)
    (seenTable : r.seen = MatchingTable.encode seen) :
    result r =
      match TableOwner.owner matching index with
      | some _ => advanced (matchingResult r)
      | none =>
          match TableOwner.owner seen index with
          | none => advanced (seenResult (matchingResult r))
          | some _ => chosen (seenResult (matchingResult r)) := by
  have matched := matching_canonical r index matching target matchedTable
  have traced := seen_canonical (matchingResult r) index seen
    ((matching_target r).trans target) seenTable
  cases owned : TableOwner.owner matching index with
  | none =>
      simp only [owned, TableOwner.answer] at matched
      simp only [result, decisionResult, matched]
      cases visited : TableOwner.owner seen index with
      | none =>
          simp only [visited, TableOwner.answer] at traced
          simp only [finishResult, traced]
      | some first =>
          simp only [visited, TableOwner.answer] at traced
          simp only [finishResult, traced]
  | some first =>
      simp only [owned, TableOwner.answer] at matched
      simp only [result, decisionResult, matched]

theorem advanced_matching_target (r : State) (index : Nat)
    (target : r.core.target = List.replicate index true) :
    (advanced (matchingResult r)).core.target = List.replicate (index + 1) true := by
  change true :: (matchingResult r).core.target = _
  rw [matching_target, target, List.replicate_succ]

theorem advanced_seen_target (r : State) (index : Nat)
    (target : r.core.target = List.replicate index true) :
    (advanced (seenResult (matchingResult r))).core.target = List.replicate (index + 1) true := by
  change true :: (seenResult (matchingResult r)).core.target = _
  rw [seen_target, matching_target, target, List.replicate_succ]

theorem chosen_output (r : State) (index : Nat)
    (target : r.core.target = List.replicate index true) :
    (chosen (seenResult (matchingResult r))).output = TableOwner.answer (some index) := by
  change true :: (seenResult (matchingResult r)).core.target = _
  rw [seen_target, matching_target, target]
  rfl

end PNP.Concrete.NormalizerBlocks.Candidate
