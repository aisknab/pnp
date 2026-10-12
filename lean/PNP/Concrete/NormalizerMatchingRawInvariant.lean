/-
Copyright (c) 2026 PNP Labs.

Fixed whole-loop size invariant, including arbitrary malformed raw input.
All rounds preserve the input-derived width and formula, table row count,
and finite index bound. No expanding previous-round bound is iterated.
-/
import PNP.Concrete.NormalizerMatchingRawRange

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver

structure Within (bound : Nat) (r : State) : Prop where
  width : r.width.length ≤ bound
  formula : r.formula.length ≤ bound
  indexRange : ClauseCount.count r.formula + r.width.length ≤ bound
  table : ∃ entries, r.table = MatchingTable.encode entries ∧
    entries.length ≤ bound ∧ MatchingLoop.EntriesBound bound entries

theorem Within.table_bytes {bound : Nat} {r : State} (data : Within bound r) :
    r.table.length ≤ MatchingLoop.tableBytes bound bound := by
  obtain ⟨entries, read, count, indices⟩ := data.table
  rw [read]
  exact Nat.le_trans (MatchingLoop.table_bytes bound entries indices)
    (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * bound + 8) count) 2)

theorem body_table_within (bound : Nat) (r : State) (data : Within bound r) :
    ∃ entries, (bodyResult r).table = MatchingTable.encode entries ∧
      entries.length ≤ bound ∧ MatchingLoop.EntriesBound bound entries := by
  obtain ⟨entries, tableRead, count, indices⟩ := data.table
  obtain ⟨answer, answerRead, shape⟩ := search_raw_shape r.width r.formula entries
  have output : (searchResult r).registers.output = Search.answer answer := by
    rw [searchResult_output, tableRead]
    exact answerRead
  have searchFrame := searchResult_frame r
  cases answer with
  | terminal trace =>
      have tag : ForwardEdge.present (searchResult r).registers.output = false := by rw [output]; rfl
      simp only [bodyResult, chosen, tag, Bool.false_eq_true, ite_false]
      exact ⟨entries, (stopped_frame _).2.2.1.trans (searchFrame.2.2.1.trans tableRead), count, indices⟩
  | augment index path =>
      have pathBound : ExplorationData.VerticesBound bound path := fun vertex member =>
        Nat.le_trans (shape.1 vertex member) data.indexRange
      have nextIndices := MatchingLoop.writeAll_bound bound entries (PathPairs.value path) indices
        (MatchingLoop.pairs_range bound path pathBound)
      have nextCount : (MatchingTable.writeAll entries (PathPairs.value path)).length ≤ bound := by
        rw [MatchingTable.writeAll_length]
        exact count
      have updated := advanced_canonical (searchResult r) entries index path
        (searchFrame.2.2.1.trans tableRead) output
      have tag : ForwardEdge.present (searchResult r).registers.output = true := by rw [output]; rfl
      simp only [bodyResult, chosen, tag, ite_true]
      exact ⟨MatchingTable.writeAll entries (PathPairs.value path),
        (continued_frame _).2.2.2.trans updated, nextCount, nextIndices⟩

theorem Within.body {bound : Nat} {r : State} (data : Within bound r) : Within bound (bodyResult r) := by
  have frame := body_frame r
  refine ⟨?_, ?_, ?_, body_table_within bound r data⟩
  · rw [frame.1]; exact data.width
  · rw [frame.2]; exact data.formula
  · rw [frame.1, frame.2]; exact data.indexRange

theorem initialized_within (input : BitString) : Within (6 * input.length + 6) (initialized input) := by
  have fields := initialized_fields input
  have sizes := Exploration.source_sizes input
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fields.1]
    have width := sizes.1
    omega
  · rw [fields.2.1]
    have formula := sizes.2.1
    omega
  · rw [fields.1, fields.2.1]
    change Exploration.sourceCount input + (Exploration.sourceWidth input).length ≤ _
    have width := sizes.1
    have count := sizes.2.2.2
    omega
  · refine ⟨List.replicate (Exploration.sourceCount input) none, fields.2.2.1, ?_,
      MatchingLoop.empty_bound _ _⟩
    rw [List.length_replicate]
    have count := sizes.2.2.2
    omega

theorem scan_within (fuel bound : Nat) (r : State) (data : Within bound r) :
    Within bound (scan fuel r).state := by
  induction fuel generalizing r with
  | zero => exact data
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil => simpa only [scan, remaining] using data
      | cons bit rest => simpa only [scan, remaining] using ih (bodyResult r) data.body

theorem whole_within (bound : Nat) (r : State) (data : Within bound r) :
    Within bound (whole r).state := scan_within _ bound r data

theorem result_table_bound (input : BitString) :
    (result input).registers.output.length ≤ MatchingLoop.tableBytes (6 * input.length + 6) (6 * input.length + 6) := by
  rw [result, finished_output]
  exact (whole_within _ (initialized input) (initialized_within input)).table_bytes

end PNP.Concrete.NormalizerBlocks.MatchingDriver
