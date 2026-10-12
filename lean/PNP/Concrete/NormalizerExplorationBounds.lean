/-
Copyright (c) 2026 PNP Labs.

Uniform size invariant for the complete exploration. Unseen vertices and
predecessor rows stay within one fixed index range, and trace length plus
the remaining countdown never exceeds the initial total budget. These
facts do not assume that the formula or matching bytes are well formed.
-/

import PNP.Concrete.NormalizerExplorationSemantics

namespace PNP.Concrete.NormalizerBlocks.Exploration
open ExplorationData

structure Within (limit : Nat) (unseen : List CNFLiteral) (trace : List TraceData.Row) (r : State) : Prop where
  pendingRead : r.core.pending = SearchVertices.encodeVertices unseen
  traceRead : r.core.trace = TraceData.encode trace
  vertices : VerticesBound limit unseen
  predecessors : TraceBound limit trace
  unseenCount : unseen.length ≤ limit
  traceBudget : trace.length + r.remaining.length ≤ limit

def unseenBytes (limit : Nat) : Nat := (2 * limit + 8) * limit + 2
def traceBytes (limit : Nat) : Nat := (2 * limit + 5) * limit

theorem Within.bytes {limit : Nat} {unseen : List CNFLiteral} {trace : List TraceData.Row} {r : State}
    (data : Within limit unseen trace r) :
    r.core.pending.length ≤ unseenBytes limit ∧ r.core.trace.length ≤ traceBytes limit := by
  constructor
  · rw [data.pendingRead]
    exact Nat.le_trans (vertices_length limit unseen data.vertices)
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ data.unseenCount) 2)
  · rw [data.traceRead]
    exact Nat.le_trans (trace_length limit trace data.predecessors)
      (Nat.mul_le_mul_left _ (by have h := data.traceBudget; omega))

theorem parent_index {limit : Nat} {trace : List TraceData.Row} {parent : Option CNFLiteral}
    (bound : TraceBound limit trace) (within : Extraction.ParentWithin trace parent)
    (vertex : CNFLiteral) (same : parent = some vertex) : vertex.variableIndex ≤ limit := by
  obtain ⟨entry, member, equals⟩ := within vertex same
  have found := (bound entry member).1
  rw [equals] at found
  exact found

theorem parent_answer_length {limit : Nat} {trace : List TraceData.Row} {parent : Option CNFLiteral}
    (bound : TraceBound limit trace) (within : Extraction.ParentWithin trace parent) :
    (ParentQuery.answer (some parent)).length ≤ limit + 3 := by
  cases parent with
  | none =>
      change 2 ≤ limit + 3
      omega
  | some vertex =>
      have size := parent_index bound within vertex rfl
      change (true :: true :: vertex.positive :: List.replicate vertex.variableIndex true).length ≤ limit + 3
      simp only [List.length_cons, List.length_replicate]
      omega

theorem trace_cons_bound {limit : Nat} {unseen : List CNFLiteral} {trace : List TraceData.Row}
    {vertex : CNFLiteral} {parent : Option CNFLiteral} {rest : List CNFLiteral}
    (vertices : VerticesBound limit unseen) (predecessors : TraceBound limit trace)
    (removed : Removes vertex unseen rest) (within : Extraction.ParentWithin trace parent) :
    TraceBound limit ((vertex, parent) :: trace) := by
  intro entry member
  cases List.mem_cons.mp member with
  | inl same =>
      rw [same]
      exact ⟨(removed.bounds limit vertices).1, parent_index predecessors within⟩
  | inr tail => exact predecessors entry tail

theorem within_step (limit : Nat) (unseen : List CNFLiteral) (trace : List TraceData.Row) (r : State)
    (data : Within limit unseen trace r) (nonempty : r.remaining ≠ []) :
    (bodyResult r).remaining = [] ∨ ∃ rest next, Within limit rest next (bodyResult r) := by
  cases body_range r unseen trace data.pendingRead data.traceRead with
  | inl stopped => exact Or.inl stopped.1
  | inr selected =>
      obtain ⟨vertex, parent, rest, remaining, pendingRead, traceRead, removed, parentRange⟩ := selected
      apply Or.inr
      refine ⟨rest, (vertex, parent) :: trace, pendingRead, traceRead,
        (removed.bounds limit data.vertices).2,
        trace_cons_bound data.vertices data.predecessors removed parentRange, ?_, ?_⟩
      · have shorter := removed.length
        have initial := data.unseenCount
        omega
      · rw [List.length_cons, remaining, List.length_tail]
        have positive := List.length_pos_iff.mpr nonempty
        have initial := data.traceBudget
        omega

def extractionBound (formula matching limit : Nat) : Nat :=
  349 * unseenBytes limit + 339 * matching + 1375 +
    (188 * formula + 188 * matching + 236 * traceBytes limit +
      40 * unseenBytes limit + 975) * (traceBytes limit + 1)

theorem extraction_bound (formula matching limit : Nat)
    (unseen : List CNFLiteral) (trace : List TraceData.Row) (r : State)
    (data : Within limit unseen trace r)
    (formulaSize : r.core.parent.graph.core.formula.length ≤ formula)
    (matchingSize : r.core.parent.graph.core.matching.length ≤ matching) :
    Extraction.stepBound r.core ≤ extractionBound formula matching limit := by
  have pendingSize := data.bytes.1
  have traceSize := data.bytes.2
  have coefficient :
      188 * r.core.parent.graph.core.formula.length + 188 * r.core.parent.graph.core.matching.length +
        236 * r.core.trace.length + 40 * r.core.pending.length + 975 ≤
      188 * formula + 188 * matching + 236 * traceBytes limit + 40 * unseenBytes limit + 975 := by omega
  have constant :
      349 * r.core.pending.length + 339 * r.core.parent.graph.core.matching.length + 1375 ≤
      349 * unseenBytes limit + 339 * matching + 1375 := by omega
  exact Nat.add_le_add constant (Nat.mul_le_mul coefficient (Nat.add_le_add_right traceSize 1))

theorem choose_bound (limit : Nat) (unseen : List CNFLiteral) (trace : List TraceData.Row) (r : State)
    (data : Within limit unseen trace r) :
    chooseFuel (begun r) ≤ 4 * unseenBytes limit + 6 * limit + 39 := by
  have range := begun_range r unseen trace data.pendingRead data.traceRead
  cases found : ForwardEdge.present (begun r).core.parent.output with
  | false =>
      simp only [chooseFuel, found, Bool.false_eq_true, ite_false]
      omega
  | true =>
      cases range with
      | inl unavailable =>
          rw [unavailable] at found
          cases found
      | inr available =>
          obtain ⟨vertex, parent, rest, selected, removed, within⟩ := available
          have indices := removed.bounds limit data.vertices
          have restCount : rest.length ≤ limit := by
            have length := removed.length
            have initial := data.unseenCount
            omega
          have restSize : (SearchVertices.encodeVertices rest).length ≤ unseenBytes limit :=
            Nat.le_trans (vertices_length limit rest indices.2)
              (Nat.add_le_add_right (Nat.mul_le_mul_left _ restCount) 2)
          have skippedSize := Nat.le_trans selected.sizes.1 restSize
          have parentSize := parent_answer_length data.predecessors within
          rw [← selected.parentRead] at parentSize
          have indexSize : (begun r).core.parent.targetIndex.length ≤ limit := by
            rw [selected.indexRead, List.length_replicate]
            exact indices.1
          have work := acceptFuel_bound (begun r)
          simp only [chooseFuel, found, ite_true]
          omega

def workBound (formula matching limit : Nat) : Nat :=
  (extractionBound formula matching limit + 1) * (unseenBytes limit + 1) +
    4 * unseenBytes limit + 6 * limit + 45

theorem bodyFuel_bound (formula matching limit : Nat)
    (unseen : List CNFLiteral) (trace : List TraceData.Row) (r : State)
    (data : Within limit unseen trace r)
    (formulaSize : r.core.parent.graph.core.formula.length ≤ formula)
    (matchingSize : r.core.parent.graph.core.matching.length ≤ matching) :
    bodyFuel r ≤ workBound formula matching limit := by
  have beginBound := beginFuel_bound r
  have selectBound := extraction_bound formula matching limit unseen trace r data formulaSize matchingSize
  have fixed := Nat.mul_le_mul (Nat.add_le_add_right selectBound 1) (Nat.add_le_add_right data.bytes.1 1)
  have chooseBound := choose_bound limit unseen trace r data
  unfold bodyFuel workBound
  omega

end PNP.Concrete.NormalizerBlocks.Exploration
