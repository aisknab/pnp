/-
Copyright (c) 2026 PNP Labs.

Finite matching-table data and exact read/write specifications. An absent
entry is an empty clause; a present natural index is a single positive literal.
The representation reuses the concrete full-clause-list reader. The recursive
write specifications below are not, by themselves, tape-runtime theorems.
-/

import PNP.Concrete.NormalizerFormulaOccurrence

namespace PNP.Concrete.NormalizerBlocks.MatchingTable

abbrev Entries := List (Option Nat)

def entryClause : Option Nat → List CNFLiteral
  | none => []
  | some value => [⟨true, value⟩]

def clauses (entries : Entries) : List (List CNFLiteral) := entries.map entryClause

def encode (entries : Entries) : BitString :=
  encodeTokenPairs (encodeClauseListTokens (clauses entries) ++ [.finish])

def read (entries : Entries) (index : Nat) : Option Nat := entries[index]?.getD none

def write : Entries → Nat → Nat → Entries
  | [], _, _ => []
  | _ :: rest, 0, value => some value :: rest
  | first :: rest, index + 1, value => first :: write rest index value

def writeAll : Entries → List (Nat × Nat) → Entries
  | entries, [] => entries
  | entries, (index, value) :: rest => writeAll (write entries index value) rest

theorem clauses_read (entries : Entries) (index : Nat) :
    (clauses entries)[index]?.getD [] = entryClause (read entries index) := by
  induction entries generalizing index with
  | nil => rfl
  | cons first rest ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

theorem read_query (entries : Entries) (index : Nat) :
    ClauseQuery.polynomial.output (ClauseQuery.encodeQuery 0 index (clauses entries)) =
      Occurrence.encodeQuery 0 (entryClause (read entries index)) := by
  rw [ClauseQuery.polynomial_canonical, clauses_read]

theorem write_length (entries : Entries) (index value : Nat) :
    (write entries index value).length = entries.length := by
  induction entries generalizing index with
  | nil => rfl
  | cons first rest ih =>
      cases index with
      | zero => rfl
      | succ index => exact congrArg Nat.succ (ih index)

theorem write_eq_set (entries : Entries) (index value : Nat) :
    write entries index value = entries.set index (some value) := by
  induction entries generalizing index with
  | nil => rfl
  | cons first rest ih =>
      cases index with
      | zero => rfl
      | succ index => exact congrArg (List.cons first) (ih index)

theorem clauses_write (entries : Entries) (index value : Nat) :
    clauses (write entries index value) = (clauses entries).set index (entryClause (some value)) := by
  rw [write_eq_set]
  induction entries generalizing index with
  | nil => rfl
  | cons first rest ih =>
      cases index with
      | zero => rfl
      | succ index => exact congrArg (List.cons (entryClause first)) (ih index)

theorem write_last_wins (entries : Entries) (index first last : Nat) :
    write (write entries index first) index last = write entries index last := by
  induction entries generalizing index with
  | nil => rfl
  | cons head rest ih =>
      cases index with
      | zero => rfl
      | succ index => exact congrArg (List.cons head) (ih index)

theorem writeAll_length (entries : Entries) (updates : List (Nat × Nat)) :
    (writeAll entries updates).length = entries.length := by
  induction updates generalizing entries with
  | nil => rfl
  | cons update rest ih =>
      rw [writeAll, ih, write_length]

theorem read_write (entries : Entries) (index value position : Nat) (valid : position < entries.length) :
    read (write entries index value) position =
      if position = index then some value else read entries position := by
  induction entries generalizing index position with
  | nil => exact False.elim (Nat.not_lt_zero _ valid)
  | cons first rest ih =>
      cases index with
      | zero =>
          cases position with
          | zero => rw [if_pos rfl]; rfl
          | succ position => rw [if_neg (Nat.succ_ne_zero _)]; rfl
      | succ index =>
          cases position with
          | zero => rw [if_neg (Nat.zero_ne_add_one _)]; rfl
          | succ position =>
              change read (write rest index value) position =
                if position + 1 = index + 1 then some value else read rest position
              simpa only [Nat.succ.injEq] using
                ih index position (Nat.lt_of_succ_lt_succ valid)

end PNP.Concrete.NormalizerBlocks.MatchingTable
