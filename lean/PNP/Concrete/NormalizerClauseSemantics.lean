/-
Copyright (c) 2026 PNP Labs.

Exact indexed-clause selection over arbitrary encoded clause lists. Earlier
clauses are skipped as data, selected bytes retain their order and duplicates,
and an absent index yields the empty literal stream. No supplied lookup
correctness or graph-incidence premise appears in the complete theorem.
-/

import PNP.Concrete.NormalizerClauseTokens

namespace PNP.Concrete.NormalizerBlocks.ClauseQuery

open Occurrence

def selectionState (index : Nat) (buffer : BitString) (selected : Bool) (r : Registers) : Registers :=
  ⟨[], r.target, List.replicate index true, buffer, r.sign,
    (match selected with | false => [] | true => [true]), [true], r.reserved, r.output⟩

theorem tokenScan_skip_data {values : List CNFToken} (data : DataTokens values)
    (rest : List CNFToken) (index : Nat) (buffer : BitString) (r : Registers) :
    tokenScan (values ++ rest) (selectionState index buffer false r) =
      tokenScan rest (selectionState index buffer false r) := by
  induction data with
  | nil => rfl
  | f _ ih => simpa only [List.cons_append, tokenScan, selectionState, tokenResult] using ih
  | t _ ih => simpa only [List.cons_append, tokenScan, selectionState, tokenResult] using ih

theorem tokenScan_copy_data {values : List CNFToken} (data : DataTokens values)
    (rest : List CNFToken) (index : Nat) (buffer : BitString) (r : Registers) :
    tokenScan (values ++ rest) (selectionState index buffer true r) =
      tokenScan rest (selectionState index ((encodeTokenPairs values).reverse ++ buffer) true r) := by
  induction data generalizing buffer with
  | nil => rfl
  | f _ ih =>
      simpa only [List.cons_append, tokenScan, selectionState, tokenResult, emitted,
        encodeTokenPairs, CNFToken.bits, List.nil_append, List.reverse_cons, List.reverse_nil,
        List.append_assoc] using ih (false :: false :: buffer)
  | t _ ih =>
      simpa only [List.cons_append, tokenScan, selectionState, tokenResult, emitted,
        encodeTokenPairs, CNFToken.bits, List.nil_append, List.reverse_cons, List.reverse_nil,
        List.append_assoc] using ih (true :: true :: buffer)

theorem tokenScan_select_zero (rest : List CNFToken) (buffer : BitString) (r : Registers) :
    tokenScan (.sep :: rest) (selectionState 0 buffer false r) =
      tokenScan rest (selectionState 0 buffer true r) := rfl

theorem tokenScan_select_succ (rest : List CNFToken) (index : Nat) (buffer : BitString) (r : Registers) :
    tokenScan (.sep :: rest) (selectionState (index + 1) buffer false r) =
      tokenScan rest (selectionState index buffer false r) := by
  simp only [tokenScan, selectionState, tokenResult, separated, List.replicate_succ]

theorem tokenScan_finish_buffer (rest : List CNFToken) (index : Nat) (buffer : BitString) (r : Registers) :
    (tokenScan (.finish :: rest) (selectionState index buffer true r)).excess = buffer := by
  change (tokenScan rest {selectionState index buffer true r with active := []}).excess = buffer
  rw [tokenScan_inactive _ _ rfl]
  rfl

theorem tokenScan_skip_finish (rest : List CNFToken) (index : Nat) (buffer : BitString) (r : Registers) :
    tokenScan (.finish :: rest) (selectionState index buffer false r) =
      tokenScan rest (selectionState index buffer false r) := rfl

theorem tokenScan_clauseList (clauses : List (List CNFLiteral)) (index : Nat)
    (buffer : BitString) (r : Registers) :
    (tokenScan (encodeClauseListTokens clauses ++ [.finish]) (selectionState index buffer false r)).excess =
      (encodeTokenPairs (encodeLiteralListTokens (clauses[index]?.getD []))).reverse ++ buffer := by
  induction clauses generalizing index with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [encodeClauseListTokens, encodeClauseTokens, List.cons_append,
        List.append_assoc, List.nil_append]
      cases index with
      | zero =>
          rw [tokenScan_select_zero, tokenScan_copy_data (clause_data clause), tokenScan_finish_buffer]
          rfl
      | succ index =>
          rw [tokenScan_select_succ, tokenScan_skip_data (clause_data clause), tokenScan_skip_finish]
          exact ih index

end PNP.Concrete.NormalizerBlocks.ClauseQuery
