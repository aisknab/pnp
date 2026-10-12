/-
Copyright (c) 2026 PNP Labs.

The complete finite matching recurrence, with internally constructed empty
table and clause-derived round count. Early terminal results return the
current table immediately. This is the exact specification for the outer
machine, not by itself a finite-tape runtime theorem.
-/
import PNP.Concrete.NormalizerMatchingInvariant

namespace PNP.Concrete.NormalizerBlocks.MatchingLoop

def finish (variables : Nat) (clauses : List (List CNFLiteral)) :
    Nat → MatchingTable.Entries → MatchingTable.Entries
  | 0, entries => entries
  | fuel + 1, entries =>
      match Search.value variables clauses entries with
      | .terminal _ => entries
      | .augment _ path =>
          finish variables clauses fuel (MatchingTable.writeAll entries (PathPairs.value path))

def fullTable (variables : Nat) (clauses : List (List CNFLiteral)) : MatchingTable.Entries :=
  finish variables clauses (clauses.length + 1) (List.replicate clauses.length none)

theorem finish_zero (variables : Nat) (clauses : List (List CNFLiteral))
    (entries : MatchingTable.Entries) : finish variables clauses 0 entries = entries := rfl

theorem finish_terminal (variables : Nat) (clauses : List (List CNFLiteral))
    (fuel : Nat) (entries : MatchingTable.Entries) (trace : List TraceData.Row)
    (terminal : Search.value variables clauses entries = .terminal trace) :
    finish variables clauses (fuel + 1) entries = entries := by
  rw [finish, terminal]

theorem finish_augment (variables : Nat) (clauses : List (List CNFLiteral))
    (fuel : Nat) (entries : MatchingTable.Entries) (index : Nat) (path : List CNFLiteral)
    (augment : Search.value variables clauses entries = .augment index path) :
    finish variables clauses (fuel + 1) entries =
      finish variables clauses fuel (MatchingTable.writeAll entries (PathPairs.value path)) := by
  rw [finish, augment]

theorem finish_invariant (variables : Nat) (clauses : List (List CNFLiteral))
    (fuel : Nat) (entries : MatchingTable.Entries)
    (bounded : EntriesBound (clauses.length + variables) entries) :
    EntriesBound (clauses.length + variables) (finish variables clauses fuel entries) ∧
      (finish variables clauses fuel entries).length = entries.length := by
  induction fuel generalizing entries with
  | zero => exact ⟨bounded, rfl⟩
  | succ fuel ih =>
      cases search : Search.value variables clauses entries with
      | terminal trace =>
          rw [finish_terminal variables clauses fuel entries trace search]
          exact ⟨bounded, rfl⟩
      | augment index path =>
          have update := search_augmentation_bound variables clauses entries index path bounded search
          have next := ih (MatchingTable.writeAll entries (PathPairs.value path)) update.1
          rw [finish_augment variables clauses fuel entries index path search]
          exact ⟨next.1, next.2.trans update.2.1⟩

theorem fullTable_invariant (variables : Nat) (clauses : List (List CNFLiteral)) :
    EntriesBound (clauses.length + variables) (fullTable variables clauses) ∧
      (fullTable variables clauses).length = clauses.length := by
  have result := finish_invariant variables clauses (clauses.length + 1)
    (List.replicate clauses.length none) (empty_bound clauses.length (clauses.length + variables))
  exact ⟨result.1, result.2.trans (List.length_replicate ..)⟩

end PNP.Concrete.NormalizerBlocks.MatchingLoop
