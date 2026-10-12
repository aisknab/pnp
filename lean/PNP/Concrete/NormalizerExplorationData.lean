/-
Copyright (c) 2026 PNP Labs.

Finite deletion and encoded-size facts for repeated trace construction.
Removing one selected vertex preserves every other occurrence and cannot
increase the unseen list. Bounded node indices give explicit byte bounds
for both the ordered vertex list and its predecessor trace.
-/

import PNP.Concrete.NormalizerParentRange

namespace PNP.Concrete.NormalizerBlocks.ExplorationData

inductive Removes (vertex : CNFLiteral) : List CNFLiteral → List CNFLiteral → Prop
  | head (rest : List CNFLiteral) : Removes vertex (vertex :: rest) rest
  | skip (first : CNFLiteral) {before after : List CNFLiteral} :
      Removes vertex before after → Removes vertex (first :: before) (first :: after)

theorem Removes.member {vertex : CNFLiteral} {before after : List CNFLiteral}
    (removed : Removes vertex before after) : vertex ∈ before := by
  induction removed with
  | head rest => exact List.mem_cons_self
  | skip first previous ih => exact List.mem_cons_of_mem first ih

theorem Removes.subset {vertex : CNFLiteral} {before after : List CNFLiteral}
    (removed : Removes vertex before after) : ∀ value, value ∈ after → value ∈ before := by
  induction removed with
  | head rest => intro value member; exact List.mem_cons_of_mem vertex member
  | skip first previous ih =>
      intro value member
      cases List.mem_cons.mp member with
      | inl same => exact List.mem_cons.mpr (Or.inl same)
      | inr tail => exact List.mem_cons_of_mem first (ih value tail)

theorem Removes.length {vertex : CNFLiteral} {before after : List CNFLiteral}
    (removed : Removes vertex before after) : after.length + 1 = before.length := by
  induction removed with
  | head rest => rfl
  | skip first previous ih => simp only [List.length_cons]; omega

theorem Removes.prefixed {vertex : CNFLiteral} {before after : List CNFLiteral}
    (removed : Removes vertex before after) (skipped : List CNFLiteral) :
    Removes vertex (skipped ++ before) (skipped ++ after) := by
  induction skipped with
  | nil => exact removed
  | cons first rest ih => exact .skip first ih

def VerticesBound (limit : Nat) (vertices : List CNFLiteral) : Prop :=
  ∀ vertex, vertex ∈ vertices → vertex.variableIndex ≤ limit

theorem Removes.bounds {vertex : CNFLiteral} {before after : List CNFLiteral}
    (removed : Removes vertex before after) (limit : Nat) (bound : VerticesBound limit before) :
    vertex.variableIndex ≤ limit ∧ VerticesBound limit after :=
  ⟨bound vertex removed.member, fun value member => bound value (removed.subset value member)⟩

theorem entry_length (vertex : CNFLiteral) : (UnseenData.entry vertex).length = 2 * vertex.variableIndex + 8 := by
  simp only [UnseenData.entry, SearchVertices.entryBits, NANDFrontend.literalBits,
    List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem prefix_length (limit : Nat) (vertices : List CNFLiteral) (bound : VerticesBound limit vertices) :
    (UnseenData.prefixBits vertices).length ≤ (2 * limit + 8) * vertices.length := by
  induction vertices with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      have head := bound first List.mem_cons_self
      have tail := ih (fun vertex member => bound vertex (List.mem_cons_of_mem first member))
      rw [UnseenData.prefixBits, List.length_append, entry_length, List.length_cons, Nat.mul_succ]
      omega

theorem vertices_length (limit : Nat) (vertices : List CNFLiteral) (bound : VerticesBound limit vertices) :
    (SearchVertices.encodeVertices vertices).length ≤ (2 * limit + 8) * vertices.length + 2 := by
  rw [UnseenData.encoded_prefix, List.length_append]
  exact Nat.add_le_add_right (prefix_length limit vertices bound) 2

def RowBound (limit : Nat) (entry : TraceData.Row) : Prop :=
  entry.1.variableIndex ≤ limit ∧ ∀ parent, entry.2 = some parent → parent.variableIndex ≤ limit
def TraceBound (limit : Nat) (trace : List TraceData.Row) : Prop :=
  ∀ entry, entry ∈ trace → RowBound limit entry

theorem vertex_length (vertex : CNFLiteral) (suffix : BitString) :
    (TraceData.vertex vertex suffix).length = vertex.variableIndex + 2 + suffix.length := by
  simp only [TraceData.vertex, TableInit.encodeCount, List.length_cons, List.length_append, List.length_replicate]
  omega

theorem row_length (limit : Nat) (entry : TraceData.Row) (suffix : BitString) (bound : RowBound limit entry) :
    (TraceData.row entry suffix).length ≤ 2 * limit + 5 + suffix.length := by
  rw [TraceData.row, vertex_length]
  cases parent : entry.2 with
  | none =>
      simp only [TraceData.predecessor, List.length_cons]
      have head := bound.1
      omega
  | some value =>
      have head := bound.1
      have ancestor := bound.2 value parent
      simp only [TraceData.predecessor, List.length_cons, vertex_length]
      omega

theorem trace_length (limit : Nat) (trace : List TraceData.Row) (bound : TraceBound limit trace) :
    (TraceData.encode trace).length ≤ (2 * limit + 5) * trace.length := by
  induction trace with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
      have head := row_length limit entry (TraceData.encode rest) (bound entry List.mem_cons_self)
      have tail := ih (fun row member => bound row (List.mem_cons_of_mem entry member))
      change (TraceData.row entry (TraceData.encode rest)).length ≤ _
      rw [List.length_cons, Nat.mul_succ]
      omega

end PNP.Concrete.NormalizerBlocks.ExplorationData
