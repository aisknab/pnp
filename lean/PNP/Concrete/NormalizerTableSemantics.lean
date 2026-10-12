/-
Copyright (c) 2026 PNP Labs.

Whole-list correctness of the table writer. This theorem is uniform in the
list, selected index and replacement value, including an out-of-range index.
It does not assume a supplied matching table transition or execution witness.
-/

import PNP.Concrete.NormalizerTableData

namespace PNP.Concrete.NormalizerBlocks.TableWrite

open Occurrence

theorem tokenScan_clauseList (clauses : List (List CNFLiteral)) (index value : Nat)
    (buffer : BitString) (r : Registers) :
    (tokenScan (encodeClauseListTokens clauses ++ [.finish])
      (tableState index value buffer [] r)).excess =
      (encodeTokenPairs (encodeClauseListTokens (clauses.set index [⟨true, value⟩]) ++ [.finish])).reverse ++ buffer := by
  induction clauses generalizing index buffer with
  | nil => rfl
  | cons clause clauses ih =>
      cases index with
      | zero =>
          simp only [encodeClauseListTokens, List.set, encodeClauseTokens,
            List.cons_append, List.append_assoc, List.nil_append]
          rw [tokenScan_select_zero, tokenScan_skip_data (ClauseQuery.clause_data clause),
            tokenScan_finish_selected, tokenScan_done]
          simp only [encodeClauseTokens, NANDFrontend.encodeTokenPairs_append,
            encodeTokenPairs, CNFToken.bits, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
      | succ index =>
          simp only [encodeClauseListTokens, List.set, encodeClauseTokens,
            List.cons_append, List.append_assoc, List.nil_append]
          rw [tokenScan_select_succ, tokenScan_copy_data (ClauseQuery.clause_data clause),
            tokenScan_finish_before, ih]
          simp only [NANDFrontend.encodeTokenPairs_append,
            encodeTokenPairs, CNFToken.bits, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.append_assoc, List.cons_append, List.nil_append, List.append_nil]

theorem tokenScan_table (entries : MatchingTable.Entries) (index value : Nat)
    (buffer : BitString) (r : Registers) :
    (tokenScan (encodeClauseListTokens (MatchingTable.clauses entries) ++ [.finish])
      (tableState index value buffer [] r)).excess =
      (MatchingTable.encode (MatchingTable.write entries index value)).reverse ++ buffer := by
  rw [tokenScan_clauseList]
  simp only [MatchingTable.encode, MatchingTable.clauses_write, MatchingTable.entryClause]

end PNP.Concrete.NormalizerBlocks.TableWrite
