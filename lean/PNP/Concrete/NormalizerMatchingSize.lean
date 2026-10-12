/-
Copyright (c) 2026 PNP Labs.

A fixed encoded table bound for the entire matching recurrence. The bound
depends on the original clause and variable counts, never on a previous
round's running-time estimate.
-/
import PNP.Concrete.NormalizerMatchingSemantics

namespace PNP.Concrete.NormalizerBlocks.MatchingLoop

theorem unary_token_length (value : Nat) : (encodeUnaryTokens value).length = value + 1 := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp only [encodeUnaryTokens, List.length_cons, ih]

theorem entry_token_bound (limit : Nat) (entry : Option Nat)
    (bounded : ∀ value, entry = some value → value ≤ limit) :
    (encodeClauseTokens (MatchingTable.entryClause entry)).length ≤ limit + 4 := by
  cases entry with
  | none =>
      change 2 ≤ limit + 4
      omega
  | some value =>
      have size := bounded value rfl
      simp only [MatchingTable.entryClause, encodeClauseTokens, encodeLiteralListTokens,
        encodeLiteralTokens, ite_true, List.length_cons, List.length_append, List.length_nil,
        unary_token_length]
      omega

theorem table_token_bound (limit : Nat) (entries : MatchingTable.Entries)
    (bounded : EntriesBound limit entries) :
    (encodeClauseListTokens (MatchingTable.clauses entries)).length ≤ (limit + 4) * entries.length := by
  induction entries with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      have head := entry_token_bound limit first (fun value same =>
        bounded value (List.mem_cons.mpr (Or.inl same.symm)))
      have tail := ih (fun value member => bounded value (List.mem_cons_of_mem first member))
      change (encodeClauseTokens (MatchingTable.entryClause first) ++
        encodeClauseListTokens (MatchingTable.clauses rest)).length ≤ _
      rw [List.length_append, List.length_cons, Nat.mul_succ]
      omega

def tableBytes (count limit : Nat) : Nat := (2 * limit + 8) * count + 2

theorem table_bytes (limit : Nat) (entries : MatchingTable.Entries)
    (bounded : EntriesBound limit entries) :
    (MatchingTable.encode entries).length ≤ tableBytes entries.length limit := by
  rw [MatchingTable.encode, encodeTokenPairs_length, List.length_append]
  change 2 * ((encodeClauseListTokens (MatchingTable.clauses entries)).length + 1) ≤ _
  calc
    _ ≤ 2 * ((limit + 4) * entries.length + 1) :=
      Nat.mul_le_mul_left 2 (Nat.add_le_add_right (table_token_bound limit entries bounded) 1)
    _ = tableBytes entries.length limit := by
      unfold tableBytes
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_add]

theorem finish_bytes (variables : Nat) (clauses : List (List CNFLiteral))
    (fuel : Nat) (entries : MatchingTable.Entries)
    (bounded : EntriesBound (clauses.length + variables) entries) :
    (MatchingTable.encode (finish variables clauses fuel entries)).length ≤
      tableBytes entries.length (clauses.length + variables) := by
  have invariant := finish_invariant variables clauses fuel entries bounded
  have encoded := table_bytes (clauses.length + variables) _ invariant.1
  rw [invariant.2] at encoded
  exact encoded

theorem fullTable_bytes (variables : Nat) (clauses : List (List CNFLiteral)) :
    (MatchingTable.encode (fullTable variables clauses)).length ≤
      tableBytes clauses.length (clauses.length + variables) := by
  have invariant := fullTable_invariant variables clauses
  have encoded := table_bytes (clauses.length + variables) _ invariant.1
  rw [invariant.2] at encoded
  exact encoded

theorem path_bytes (limit : Nat) (path : List CNFLiteral)
    (bounded : ExplorationData.VerticesBound limit path) :
    (PathData.encode path).length ≤ (limit + 2) * path.length := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      have head := bounded first List.mem_cons_self
      have tail := ih (fun vertex member => bounded vertex (List.mem_cons_of_mem first member))
      change (TraceData.vertex first (PathData.encode rest)).length ≤ _
      rw [ExplorationData.vertex_length, List.length_cons, Nat.mul_succ]
      omega

theorem search_packet_length (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) :
    (Exploration.encode variables clauses entries).length =
      variables + 2 * (GraphQuery.clauseData clauses).length + 2 * (MatchingTable.encode entries).length + 3 := by
  simp only [Exploration.encode, TableInit.encodeCount, List.length_append, List.length_cons,
    List.length_replicate, List.length_nil]
  omega

theorem augmentation_packet_length (entries : MatchingTable.Entries) (path : List CNFLiteral) :
    (Augmentation.encode entries path).length =
      2 * (MatchingTable.encode entries).length + (PathData.encode path).length + 1 := by
  simp only [Augmentation.encode, TableInit.encodeCount, List.length_append, List.length_cons,
    List.length_replicate]
  omega

end PNP.Concrete.NormalizerBlocks.MatchingLoop
