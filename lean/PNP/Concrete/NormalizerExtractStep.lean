/-
Copyright (c) 2026 PNP Labs.

One ordered extraction iteration: parse a vertex, compute eligibility,
stop on the first available parent, otherwise preserve the skipped vertex.
The raw cursor strictly decreases on every continuing iteration.
-/

import PNP.Concrete.NormalizerExtractQuery

namespace PNP.Concrete.NormalizerBlocks.Extraction
open BitRegister

def stop : Block 27 := .action (.clear 25)
def stopped (r : State) : State := {r with active := []}
theorem stop_exec (r : State) : Exec stop r.store 1 (stopped r).store := .action _ _

def choose : Block 27 := .branch 19 appendSkipped appendSkipped stop
def chosen (r : State) : State := if ForwardEdge.present r.parent.output then stopped r else appended r
def chooseFuel (r : State) : Nat :=
  1 + if ForwardEdge.present r.parent.output then 1 else appendFuel r
theorem choose_exec (r : State) : Exec choose r.store (chooseFuel r) (chosen r).store := by
  have checked := EdgeKinds.branch_head (19 : Fin 27) r.store appendSkipped stop
    (appendFuel r) 1 (appended r).store (stopped r).store (appendSkipped_exec r) (stop_exec r)
  change Exec choose r.store (chooseFuel r)
    (if ForwardEdge.present r.parent.output then (stopped r).store else (appended r).store) at checked
  cases found : ForwardEdge.present r.parent.output <;>
    simpa only [chosen, found, Bool.false_eq_true, ite_false, ite_true] using checked

theorem chooseFuel_bound (r : State) : chooseFuel r ≤ 4 * r.parent.targetIndex.length + 15 := by
  cases found : ForwardEdge.present r.parent.output <;>
    simp only [chooseFuel, appendFuel, found, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem chosen_fields (r : State) :
    (chosen r).parent.targetIndex = r.parent.targetIndex ∧
      (chosen r).parent.targetTag = r.parent.targetTag ∧
        (chosen r).parent.output = r.parent.output ∧
          (chosen r).parent.graph.core.formula = r.parent.graph.core.formula ∧
            (chosen r).parent.graph.core.matching = r.parent.graph.core.matching ∧
              (chosen r).pending = r.pending ∧ (chosen r).trace = r.trace := by
  cases found : ForwardEdge.present r.parent.output <;>
    simp only [chosen, found, Bool.false_eq_true, ite_false, ite_true]
  · have stable := append_fields r
    exact ⟨stable.1, stable.2.1, stable.2.2.1, stable.2.2.2.1,
      stable.2.2.2.2.1, stable.2.2.2.2.2.1, stable.2.2.2.2.2.2.1⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem queryFuel_bound (r : State) :
    queryFuel r ≤ 342 * r.parent.targetIndex.length + 339 * r.parent.graph.core.matching.length + 1332 +
      (188 * r.parent.graph.core.formula.length + 188 * r.parent.graph.core.matching.length +
        236 * r.trace.length + 40 * r.parent.targetIndex.length + 975) * (r.trace.length + 1) := by
  have bound := Eligibility.phaseFuel_bound (traceRestored r).core
  change Eligibility.phaseFuel (traceRestored r).core ≤
    342 * r.parent.targetIndex.length + 339 * r.parent.graph.core.matching.length + 1331 +
      (188 * r.parent.graph.core.formula.length + 188 * r.parent.graph.core.matching.length +
        208 * r.trace.length + 40 * r.parent.targetIndex.length + 893 + 1) * (r.trace.length + 1) +
      (28 * r.trace.length + 81) * (r.trace.length + 1) at bound
  have joined :
      (188 * r.parent.graph.core.formula.length + 188 * r.parent.graph.core.matching.length +
        208 * r.trace.length + 40 * r.parent.targetIndex.length + 893 + 1) * (r.trace.length + 1) +
      (28 * r.trace.length + 81) * (r.trace.length + 1) =
      (188 * r.parent.graph.core.formula.length + 188 * r.parent.graph.core.matching.length +
        236 * r.trace.length + 40 * r.parent.targetIndex.length + 975) * (r.trace.length + 1) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  unfold queryFuel
  omega

def visit : Block 27 := .seq readVertex (.seq query choose)
def visited (r : State) : State := chosen (queried (vertexRead r))
def visitFuel (r : State) : Nat := readFuel r + (queryFuel (vertexRead r) + chooseFuel (queried (vertexRead r)))
theorem visit_exec (r : State) : Exec visit r.store (visitFuel r) (visited r).store :=
  Exec.seq (readVertex_exec r) (Exec.seq (query_exec (vertexRead r)) (choose_exec (queried (vertexRead r))))

def body : Block 27 := .branch 22 stop visit stop
def bodyResult (r : State) : State :=
  match r.pending with
  | false :: _ => visited r
  | _ => stopped r
def bodyFuel (r : State) : Nat :=
  match r.pending with
  | false :: _ => 1 + visitFuel r
  | _ => 2
theorem body_exec (r : State) : Exec body r.store (bodyFuel r) (bodyResult r).store := by
  cases pending : r.pending with
  | nil =>
      simp only [bodyFuel, bodyResult, pending]
      exact Exec.empty (source := (22 : Fin 27)) (before := r.store) pending (stop_exec r)
  | cons bit rest =>
      cases bit with
      | false =>
          simp only [bodyFuel, bodyResult, pending]
          exact Exec.zero (source := (22 : Fin 27)) (before := r.store) pending (visit_exec r)
      | true =>
          simp only [bodyFuel, bodyResult, pending]
          exact Exec.one (source := (22 : Fin 27)) (before := r.store) pending (stop_exec r)

def stepBound (r : State) : Nat :=
  349 * r.pending.length + 339 * r.parent.graph.core.matching.length + 1375 +
    (188 * r.parent.graph.core.formula.length + 188 * r.parent.graph.core.matching.length +
      236 * r.trace.length + 40 * r.pending.length + 975) * (r.trace.length + 1)

theorem visitFuel_bound (r : State) : visitFuel r + 1 ≤ stepBound r := by
  have read := readFuel_bound r
  have sizes := read_index_bound r
  have fields := read_fields r
  have query := queryFuel_bound (vertexRead r)
  rw [fields.2.2.2.1, fields.2.2.2.2.1, fields.2.2.2.2.2.1] at query
  have choose := chooseFuel_bound (queried (vertexRead r))
  rw [(query_fields (vertexRead r)).1] at choose
  have coefficient :
      188 * r.parent.graph.core.formula.length + 188 * r.parent.graph.core.matching.length +
        236 * r.trace.length + 40 * (vertexRead r).parent.targetIndex.length + 975 ≤
      188 * r.parent.graph.core.formula.length + 188 * r.parent.graph.core.matching.length +
        236 * r.trace.length + 40 * r.pending.length + 975 := by omega
  have product := Nat.mul_le_mul_right (r.trace.length + 1) coefficient
  unfold visitFuel stepBound
  omega

theorem bodyFuel_bound (r : State) : bodyFuel r ≤ stepBound r := by
  have bound := visitFuel_bound r
  cases pending : r.pending with
  | nil => simp only [bodyFuel, pending]; unfold stepBound; omega
  | cons bit rest =>
      cases bit <;> simp only [bodyFuel, pending]
      · omega
      · unfold stepBound; omega

theorem visit_fields (r : State) :
    (visited r).parent.graph.core.formula = r.parent.graph.core.formula ∧
      (visited r).parent.graph.core.matching = r.parent.graph.core.matching ∧
        (visited r).trace = r.trace ∧ (visited r).pending = UnseenData.next r.pending := by
  have read := read_fields r
  have query := query_fields (vertexRead r)
  have pick := chosen_fields (queried (vertexRead r))
  exact ⟨pick.2.2.2.1.trans (query.2.2.1.trans read.2.2.2.1),
    pick.2.2.2.2.1.trans (query.2.2.2.1.trans read.2.2.2.2.1),
    pick.2.2.2.2.2.2.trans (query.2.2.2.2.2.2.1.trans read.2.2.2.2.2.1),
    pick.2.2.2.2.2.1.trans (query.2.2.2.2.1.trans read.2.2.1)⟩

theorem body_preserves (r : State) :
    (bodyResult r).parent.graph.core.formula = r.parent.graph.core.formula ∧
      (bodyResult r).parent.graph.core.matching = r.parent.graph.core.matching ∧
        (bodyResult r).trace = r.trace := by
  cases pending : r.pending with
  | nil => simp only [bodyResult, pending]; exact ⟨rfl, rfl, rfl⟩
  | cons bit rest =>
      cases bit with
      | false =>
          simp only [bodyResult, pending]
          have stable := visit_fields r
          exact ⟨stable.1, stable.2.1, stable.2.2.1⟩
      | true => simp only [bodyResult, pending]; exact ⟨rfl, rfl, rfl⟩

theorem body_progress (r : State) :
    (bodyResult r).active = [] ∨ (bodyResult r).pending.length < r.pending.length := by
  cases pending : r.pending with
  | nil => simp only [bodyResult, pending]; exact Or.inl rfl
  | cons bit rest =>
      cases bit with
      | true => simp only [bodyResult, pending]; exact Or.inl rfl
      | false =>
          apply Or.inr
          simp only [bodyResult, pending]
          rw [(visit_fields r).2.2.2]
          simpa only [pending] using UnseenData.next_shorter r.pending (by rw [pending]; intro h; cases h)

theorem body_size (r : State) : (bodyResult r).pending.length ≤ r.pending.length := by
  cases pending : r.pending with
  | nil => simp only [bodyResult, pending, stopped]; exact Nat.le_refl _
  | cons bit rest =>
      cases bit with
      | true => simp only [bodyResult, pending, stopped]; exact Nat.le_refl _
      | false =>
          simp only [bodyResult, pending]
          rw [(visit_fields r).2.2.2]
          simpa only [pending] using Nat.le_of_lt (UnseenData.next_shorter r.pending (by rw [pending]; intro h; cases h))

private theorem bound_mono (p q f m t : Nat) (size : p ≤ q) :
    349 * p + 339 * m + 1375 + (188 * f + 188 * m + 236 * t + 40 * p + 975) * (t + 1) ≤
    349 * q + 339 * m + 1375 + (188 * f + 188 * m + 236 * t + 40 * q + 975) * (t + 1) := by
  have coefficient : 188 * f + 188 * m + 236 * t + 40 * p + 975 ≤
      188 * f + 188 * m + 236 * t + 40 * q + 975 := by omega
  have product := Nat.mul_le_mul_right (t + 1) coefficient
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 349 size) (339 * m)) 1375) product

theorem stepBound_mono (r : State) : stepBound (bodyResult r) ≤ stepBound r := by
  have stable := body_preserves r
  unfold stepBound
  rw [stable.1, stable.2.1, stable.2.2]
  exact bound_mono _ _ _ _ _ (body_size r)

end PNP.Concrete.NormalizerBlocks.Extraction
