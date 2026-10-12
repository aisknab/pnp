/-
Copyright (c) 2026 PNP Labs.

Structural predecessor range independent of formula or matching validity.
A parent query can report unavailable, root, or an actual node from its
input trace. This closes the size invariant needed when queries repeat
inside a whole trace-building machine, including on malformed graph data.
-/

import PNP.Concrete.NormalizerExtractPolynomial

namespace PNP.Concrete.NormalizerBlocks.ParentQuery

inductive AnswerFrom (trace : List TraceData.Row) : BitString → Prop
  | unavailable : AnswerFrom trace (answer none)
  | root : AnswerFrom trace (answer (some none))
  | predecessor (entry : TraceData.Row) (member : entry ∈ trace) :
      AnswerFrom trace (answer (some (some entry.1)))

theorem body_from (r : State) (entry : TraceData.Row) (suffix : BitString)
    (read : r.pending = TraceData.row entry suffix) :
    ((bodyResult r).pending = suffix ∧ (bodyResult r).output = r.output) ∨
      ((bodyResult r).pending = [] ∧ (bodyResult r).output = answer (some (some entry.1))) := by
  have next : (edgeResult (nodeResult r)).pending = suffix := by
    change (nodeResult r).pending = _
    rw [(node_fields r).1, read, TraceData.next_canonical]
  have index : (edgeResult (nodeResult r)).currentIndex = List.replicate entry.1.variableIndex true := by
    change (nodeResult r).currentIndex = _
    rw [(node_fields r).2.1, read, TraceData.nodeIndex_canonical]
  have tag : ForwardEdge.present (edgeResult (nodeResult r)).graph.first = entry.1.positive := by
    rw [(edge_data (nodeResult r)).1, (node_fields r).2.2.2.2.1, read]
    rfl
  cases found : ForwardEdge.present (edgeResult (nodeResult r)).registers.output with
  | false =>
      have same : bodyResult r = edgeResult (nodeResult r) := by
        unfold bodyResult selected
        rw [found]
        rfl
      rw [same]
      exact Or.inl ⟨next, rfl⟩
  | true =>
      have same : bodyResult r = accepted (edgeResult (nodeResult r)) := by
        unfold bodyResult selected
        rw [found]
        rfl
      rw [same]
      apply Or.inr
      constructor
      · rfl
      · change true :: true :: ForwardEdge.present (edgeResult (nodeResult r)).graph.first ::
          (edgeResult (nodeResult r)).currentIndex = _
        rw [tag, index]
        rfl

theorem scan_from (fuel : Nat) (r : State) (remaining pool : List TraceData.Row)
    (read : r.pending = TraceData.encode remaining)
    (included : ∀ entry, entry ∈ remaining → entry ∈ pool)
    (previous : AnswerFrom pool r.output) :
    AnswerFrom pool (scan fuel r).state.output := by
  induction fuel generalizing r remaining with
  | zero => exact previous
  | succ fuel ih =>
      cases remaining with
      | nil =>
          rw [scan_empty (fuel + 1) r read]
          exact previous
      | cons entry rest =>
          have nonempty : r.pending ≠ [] := by
            rw [read]
            change (entry.1.positive :: _) ≠ []
            intro h
            cases h
          rw [scan_step fuel r nonempty]
          cases body_from r entry (TraceData.encode rest) read with
          | inl continuing =>
              have kept : AnswerFrom pool (bodyResult r).output := by rw [continuing.2]; exact previous
              exact ih (bodyResult r) rest continuing.1
                (fun item member => included item (List.mem_cons_of_mem entry member)) kept
          | inr found =>
              rw [scan_empty fuel (bodyResult r) found.1, found.2]
              exact .predecessor entry (included entry (List.mem_cons_self))

theorem phase_from (r : State) (trace : List TraceData.Row) (read : r.pending = TraceData.encode trace) :
    AnswerFrom trace (phaseResult r).output := by
  cases root : ForwardEdge.present (rootResult (defaulted r)).registers.output with
  | false =>
      have first : firstResult r = rootResult (defaulted r) := by
        unfold firstResult rootSelected
        rw [root]
        rfl
      have pending : (firstResult r).pending = TraceData.encode trace := by rw [first]; exact read
      have initial : AnswerFrom trace (firstResult r).output := by rw [first]; exact .unavailable
      exact scan_from _ (firstResult r) trace trace pending (fun _ member => member) initial
  | true =>
      have first : firstResult r = rootAccepted (rootResult (defaulted r)) := by
        unfold firstResult rootSelected
        rw [root]
        rfl
      have stopped : (firstResult r).pending = [] := by rw [first]; rfl
      change AnswerFrom trace (scan _ (firstResult r)).state.output
      rw [scan_empty _ (firstResult r) stopped, first]
      exact .root

theorem AnswerFrom.available (trace : List TraceData.Row) (output : BitString)
    (allowed : AnswerFrom trace output) (present : ForwardEdge.present output = true) :
    ∃ parent : Option CNFLiteral, output = answer (some parent) ∧
      (∀ vertex, parent = some vertex → ∃ entry, entry ∈ trace ∧ entry.1 = vertex) := by
  cases allowed with
  | unavailable => cases present
  | root =>
      refine ⟨none, rfl, ?_⟩
      intro vertex impossible
      cases impossible
  | predecessor entry member =>
      refine ⟨some entry.1, rfl, ?_⟩
      intro vertex equal
      exact ⟨entry, member, Option.some.inj equal⟩

theorem AnswerFrom.unavailable_eq (trace : List TraceData.Row) (output : BitString)
    (allowed : AnswerFrom trace output) (present : ForwardEdge.present output = false) : output = [false] := by
  cases allowed with
  | unavailable => rfl
  | root => cases present
  | predecessor entry member => cases present

end PNP.Concrete.NormalizerBlocks.ParentQuery

namespace PNP.Concrete.NormalizerBlocks.Eligibility
theorem phase_from (r : State) (trace : List TraceData.Row) (read : r.core.pending = TraceData.encode trace) :
    ParentQuery.AnswerFrom trace (phaseResult r).core.output := by
  cases seen : ForwardEdge.present (memberResult (saved r)).core.output with
  | true =>
      simp only [phaseResult, dispatchResult, seen, ite_true, rejected, ParentQuery.defaulted]
      exact .unavailable
  | false =>
      have restored := (restored_fields r).2.2.2.2.trans read
      simp only [phaseResult, dispatchResult, seen, Bool.false_eq_true, ite_false, parentResult]
      exact ParentQuery.phase_from _ trace restored
end PNP.Concrete.NormalizerBlocks.Eligibility

namespace PNP.Concrete.NormalizerBlocks.Extraction
theorem query_from (r : State) (trace : List TraceData.Row) (read : r.trace = TraceData.encode trace) :
    ParentQuery.AnswerFrom trace (queried r).parent.output :=
  Eligibility.phase_from (traceRestored r).core trace read
end PNP.Concrete.NormalizerBlocks.Extraction
