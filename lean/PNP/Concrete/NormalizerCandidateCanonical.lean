/-
Copyright (c) 2026 PNP Labs.

Exact increasing-index candidate selection for arbitrary finite tables.
The loop tests ownership before reachability membership and stops at the
first free seen index. This contract does not replace trace construction.
-/

import PNP.Concrete.NormalizerCandidateCanonicalBody

namespace PNP.Concrete.NormalizerBlocks.Candidate

def selectFrom (matching seen : MatchingTable.Entries) : Nat → Nat → Option Nat
  | 0, _ => none
  | count + 1, index =>
      match TableOwner.owner matching index with
      | some _ => selectFrom matching seen count (index + 1)
      | none =>
          match TableOwner.owner seen index with
          | none => selectFrom matching seen count (index + 1)
          | some _ => some index

theorem run_empty (fuel : Nat) (r : State) (empty : r.remaining = []) : run fuel r = ⟨1,r⟩ := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [run, empty]

theorem run_canonical (count index fuel : Nat) (r : State) (matching seen : MatchingTable.Entries)
    (counter : r.remaining = List.replicate count true)
    (target : r.core.target = List.replicate index true)
    (matchedTable : r.matching = MatchingTable.encode matching)
    (seenTable : r.seen = MatchingTable.encode seen)
    (unselected : r.output = [false]) (enough : count < fuel) :
    (run fuel r).state.output = TableOwner.answer (selectFrom matching seen count index) := by
  induction count generalizing index fuel r with
  | zero =>
      have empty : r.remaining = [] := counter
      rw [run_empty fuel r empty]
      exact unselected
  | succ count ih =>
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ enough)
      | succ fuel =>
          have nextEnough : count < fuel := Nat.lt_of_succ_lt_succ enough
          have pending : r.remaining = true :: List.replicate count true := by
            rw [counter, List.replicate_succ]
          have step := result_canonical r index matching seen target matchedTable seenTable
          simp only [run, pending]
          cases owned : TableOwner.owner matching index with
          | none =>
              cases visited : TableOwner.owner seen index with
              | none =>
                  simp only [owned, visited] at step
                  rw [step]
                  simp only [selectFrom, owned, visited]
                  apply ih (index + 1) fuel (advanced (seenResult (matchingResult r)))
                  · change r.remaining.tail = List.replicate count true
                    rw [counter, List.replicate_succ, List.tail_cons]
                  · exact advanced_seen_target r index target
                  · exact matchedTable
                  · exact seenTable
                  · exact unselected
                  · exact nextEnough
              | some first =>
                  simp only [owned, visited] at step
                  rw [step, run_empty fuel _ rfl]
                  simpa only [selectFrom, owned, visited] using chosen_output r index target
          | some first =>
              simp only [owned] at step
              rw [step]
              simp only [selectFrom, owned]
              apply ih (index + 1) fuel (advanced (matchingResult r))
              · change r.remaining.tail = List.replicate count true
                rw [counter, List.replicate_succ, List.tail_cons]
              · exact advanced_matching_target r index target
              · exact matchedTable
              · exact seenTable
              · exact unselected
              · exact nextEnough

def initial (count : Nat) (matching seen : BitString) : State :=
  ⟨Occurrence.initialRegisters [], matching, seen, List.replicate count true, [false]⟩

theorem whole_canonical (count : Nat) (matching seen : MatchingTable.Entries) :
    (whole (initial count (MatchingTable.encode matching) (MatchingTable.encode seen))).state.output =
      TableOwner.answer (selectFrom matching seen count 0) :=
  run_canonical count 0 _ _ matching seen rfl rfl rfl rfl rfl
    (by simp only [initial, List.length_replicate]; exact Nat.lt_succ_self _)

end PNP.Concrete.NormalizerBlocks.Candidate
