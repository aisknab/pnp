/-
Copyright (c) 2026 PNP Labs.

First-entry semantics for the complete owner scanner. A match stops before
later equal entries; absent entries still count toward the returned index.
The theorem ranges over arbitrary finite tables and target values.
-/

import PNP.Concrete.NormalizerOwnerTokens

namespace PNP.Concrete.NormalizerBlocks.TableOwner

open Occurrence

def ownerFrom (index : Nat) : MatchingTable.Entries → Nat → Option Nat
  | [], _ => none
  | none :: rest, target => ownerFrom (index + 1) rest target
  | some value :: rest, target =>
      if value == target then some index else ownerFrom (index + 1) rest target

def owner (entries : MatchingTable.Entries) (target : Nat) : Option Nat := ownerFrom 0 entries target

def answer : Option Nat → BitString
  | none => [false]
  | some index => true :: List.replicate index true

theorem tokenScan_empty_entry (target index : Nat) (rest : List CNFToken)
    (remaining excess sign : BitString) :
    tokenScan (encodeClauseTokens [] ++ rest)
      (waiting target remaining excess sign (List.replicate index true)) =
      tokenScan rest (waiting target remaining excess sign (List.replicate (index + 1) true)) := by
  simp only [encodeClauseTokens, encodeLiteralListTokens, List.cons_append, List.nil_append,
    tokenScan, tokenResult, waiting, afterEntry, List.replicate_succ]

theorem tokenScan_present_entry (value target index : Nat) (rest : List CNFToken)
    (remaining excess sign : BitString) :
    (tokenScan (encodeClauseTokens [⟨true,value⟩] ++ rest)
      (waiting target remaining excess sign (List.replicate index true))).output =
      if value == target then answer (some index)
      else (tokenScan rest (waiting target (List.replicate (target - value) true)
        (List.replicate (value - target) true) [true] (List.replicate (index + 1) true))).output := by
  simp only [encodeClauseTokens, encodeLiteralListTokens, List.append_nil, List.cons_append,
    List.nil_append, List.append_assoc]
  change (tokenScan (encodeLiteralTokens ⟨true,value⟩ ++ (.finish :: rest))
    (waiting target remaining excess sign (List.replicate index true))).output = _
  rw [tokenScan_literal]
  by_cases same : value = target
  · subst value
    have equal : (target == target) = true := by
      change decide (target = target) = true
      exact decide_eq_true rfl
    simp only [equal, ite_true, Nat.sub_self, counting, List.replicate_zero,
      tokenScan, tokenResult, foundState, answer]
  · have different : (value == target) = false := beq_eq_false_iff_ne.mpr same
    simp only [different, Bool.false_eq_true, ite_false]
    cases left : target - value with
    | zero =>
        cases right : value - target with
        | zero => exact False.elim (same (Nat.le_antisymm
            (Nat.le_of_sub_eq_zero right) (Nat.le_of_sub_eq_zero left)))
        | succ extra =>
            simp only [counting, List.replicate_zero, List.replicate_succ,
              tokenScan, tokenResult, waiting, afterEntry]
    | succ remainingCount =>
        have right : value - target = 0 := by
          apply Nat.sub_eq_zero_of_le
          apply Nat.le_of_lt
          apply Nat.lt_of_sub_pos
          rw [left]
          exact Nat.zero_lt_succ _
        simp only [right, counting, List.replicate_zero, List.replicate_succ,
          tokenScan, tokenResult, waiting, afterEntry]

theorem tokenScan_table_correct (entries : MatchingTable.Entries) (target index : Nat)
    (remaining excess sign : BitString) :
    (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
      (waiting target remaining excess sign (List.replicate index true))).output =
        answer (ownerFrom index entries target) := by
  induction entries generalizing index remaining excess sign with
  | nil => rfl
  | cons cell entries ih =>
      simp only [MatchingTable.clauses, List.map_cons, encodeClauseListTokens, List.append_assoc]
      cases cell with
      | none =>
          rw [show MatchingTable.entryClause none = [] from rfl, tokenScan_empty_entry]
          exact ih (index + 1) remaining excess sign
      | some value =>
          rw [show MatchingTable.entryClause (some value) = [⟨true,value⟩] from rfl,
            tokenScan_present_entry]
          cases found : (value == target)
          · simpa only [ownerFrom, found, Bool.false_eq_true, ite_false, MatchingTable.clauses] using
              ih (index + 1) (List.replicate (target-value) true) (List.replicate (value-target) true) [true]
          · simp only [ownerFrom, found, ite_true]

end PNP.Concrete.NormalizerBlocks.TableOwner
