/-
Copyright (c) 2026 PNP Labs.

Raw-input search shape required by the complete matching runtime proof.
Even malformed formula bytes produce a trace and path from the internally
generated finite vertex universe. The bound is independent of table size.
-/
import PNP.Concrete.NormalizerMatchingExecution

namespace PNP.Concrete.NormalizerBlocks.Exploration
open ExplorationData

theorem scan_trace_range (fuel limit : Nat) (r : State) (unseen : List CNFLiteral)
    (trace : List TraceData.Row) (data : Within limit unseen trace r) :
    ∃ result, (scan fuel r).state.core.trace = TraceData.encode result ∧
      TraceBound limit result ∧ result.length ≤ limit := by
  induction fuel generalizing r unseen trace with
  | zero =>
      exact ⟨trace, data.traceRead, data.predecessors,
        Nat.le_trans (Nat.le_add_right _ _) data.traceBudget⟩
  | succ fuel ih =>
      cases remaining : r.remaining with
      | nil =>
          rw [scan_empty (fuel + 1) r remaining]
          exact ⟨trace, data.traceRead, data.predecessors,
            Nat.le_trans (Nat.le_add_right _ _) data.traceBudget⟩
      | cons bit tail =>
          have nonempty : r.remaining ≠ [] := by rw [remaining]; intro h; cases h
          rw [scan_step fuel r nonempty]
          cases body_range r unseen trace data.pendingRead data.traceRead with
          | inl stopped =>
              rw [scan_empty fuel (bodyResult r) stopped.1]
              exact ⟨trace, stopped.2, data.predecessors,
                Nat.le_trans (Nat.le_add_right _ _) data.traceBudget⟩
          | inr discovery =>
              obtain ⟨vertex, parent, rest, nextRemaining, nextUnseen, nextTrace, removed, origin⟩ := discovery
              have nextData : Within limit rest ((vertex,parent) :: trace) (bodyResult r) := by
                refine ⟨nextUnseen, nextTrace, (removed.bounds limit data.vertices).2,
                  trace_cons_bound data.vertices data.predecessors removed origin, ?_, ?_⟩
                · have shorter := removed.length
                  have size := data.unseenCount
                  omega
                · rw [List.length_cons, nextRemaining, remaining, List.tail_cons]
                  have budget := data.traceBudget
                  rw [remaining, List.length_cons] at budget
                  omega
              exact ih (bodyResult r) rest ((vertex,parent) :: trace) nextData

theorem initialized_exact_within (input : BitString) :
    Within (sourceLimit input) (sourceVertices input) [] (initialized input) := by
  have fields := initialized_fields input
  refine ⟨fields.2.2.2.1, fields.2.2.1,
    range_vertices_bound (sourceCount input) (sourceWidth input).length, ?_, ?_, ?_⟩
  · intro row member; cases member
  · rw [sourceVertices, SearchVertices.vertices_length]
    exact Nat.le_refl _
  · rw [fields.2.2.2.2, List.length_replicate, List.length_nil, Nat.zero_add]
    exact Nat.le_refl _
theorem finished_trace (r : State) : (finished r).core.trace = r.core.trace := rfl

end PNP.Concrete.NormalizerBlocks.Exploration

namespace PNP.Concrete.NormalizerBlocks.Search
open ExplorationData

theorem explored_raw_range (input : BitString) :
    ∃ trace, (explored input).core.core.trace = TraceData.encode trace ∧
      TraceBound (Exploration.sourceLimit input) trace ∧ trace.length ≤ Exploration.sourceLimit input := by
  obtain ⟨trace, read, rows, size⟩ := Exploration.scan_trace_range
    ((Exploration.initialized input).remaining.length + 1) (Exploration.sourceLimit input)
    (Exploration.initialized input) (Exploration.sourceVertices input) []
    (Exploration.initialized_exact_within input)
  refine ⟨trace, ?_, rows, size⟩
  dsimp only [explored, Exploration.result]
  rw [Exploration.finished_trace]
  exact read

def OutputBound (limit : Nat) : Output → Prop
  | .terminal trace => TraceBound limit trace ∧ trace.length ≤ limit
  | .augment _ path => VerticesBound limit path ∧ path.length ≤ limit

end PNP.Concrete.NormalizerBlocks.Search

namespace PNP.Concrete.NormalizerBlocks.MatchingDriver
open ExplorationData

theorem searchPacket_fields (width formula table : BitString) :
    Exploration.sourceWidth (searchPacket width formula table) = List.replicate width.length true ∧
      Exploration.sourceFormula (searchPacket width formula table) = formula ∧
        Exploration.sourceMatching (searchPacket width formula table) = table ∧
          Exploration.sourceLimit (searchPacket width formula table) = ClauseCount.count formula + width.length := by
  have finalTable := BatchPacket.core_canonical table []
  rw [List.append_nil] at finalTable
  simp only [Exploration.sourceWidth, Exploration.sourceFormula, Exploration.sourceMatching,
    Exploration.sourceTail, Exploration.sourceLimit, Exploration.sourceCount, searchPacket,
    BatchPacket.header_canonical, TableInit.canonicalHeader, BatchPacket.core_canonical,
    finalTable, List.length_replicate]
  repeat constructor

theorem search_raw_shape (width formula : BitString) (entries : MatchingTable.Entries) :
    ∃ answer, (Search.result (searchPacket width formula (MatchingTable.encode entries))).registers.output =
      Search.answer answer ∧ Search.OutputBound (ClauseCount.count formula + width.length) answer := by
  let input := searchPacket width formula (MatchingTable.encode entries)
  have fields := searchPacket_fields width formula (MatchingTable.encode entries)
  obtain ⟨trace, read, rows, size⟩ := Search.explored_raw_range input
  change ExplorationData.TraceBound (Exploration.sourceLimit (searchPacket width formula (MatchingTable.encode entries))) trace at rows
  change trace.length ≤ Exploration.sourceLimit (searchPacket width formula (MatchingTable.encode entries)) at size
  rw [fields.2.2.2] at rows size
  have seen := Search.seenDerived_canonical (Search.explored input) trace read
  have seenFrame := Search.seenDerived_frame (Search.explored input)
  have matching : (Search.seenDerived (Search.explored input)).parent.graph.core.matching =
      MatchingTable.encode entries :=
    seenFrame.2.2.trans ((Search.explored_matching_raw input).trans fields.2.2.1)
  have originalWidth : (TableInit.readCount (Search.seenDerived (Search.explored input)).original).state.target =
      List.replicate width.length true := by
    rw [seenFrame.2.1]
    exact fields.1
  have selected := Search.selected_canonical (Search.seenDerived (Search.explored input))
    width.length entries (SeenTrace.value trace) originalWidth matching seen
  have kept := (Search.selected_frame (Search.seenDerived (Search.explored input))).1.trans
    (seenFrame.1.trans read)
  cases candidate : Candidate.selectFrom entries (SeenTrace.value trace) width.length 0 with
  | none =>
      rw [candidate] at selected
      have output := Search.decided_canonical (Search.selected (Search.seenDerived (Search.explored input)))
        none trace selected kept
      exact ⟨.terminal trace, output, rows, size⟩
  | some index =>
      rw [candidate] at selected
      have output := Search.decided_canonical (Search.selected (Search.seenDerived (Search.explored input)))
        (some index) trace selected kept
      have path := MatchingLoop.path_default_range (ClauseCount.count formula + width.length) trace rows ⟨false,index⟩
      exact ⟨.augment index ((TracePath.value trace ⟨false,index⟩).getD []), output, path.1,
        Nat.le_trans path.2 size⟩

end PNP.Concrete.NormalizerBlocks.MatchingDriver
