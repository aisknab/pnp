/-
Copyright (c) 2026 PNP Labs.

The internally computed delimiter count is exactly the number of clauses,
for every finite canonical formula. Literal signs and unary indices do not
create separators; empty clauses are counted just like nonempty clauses.
-/

import PNP.Concrete.NormalizerClauseCount

namespace PNP.Concrete.NormalizerBlocks.ClauseCount

theorem count_unary (index : Nat) (suffix : BitString) :
    count (encodeTokenPairs (encodeUnaryTokens index) ++ suffix) = count suffix := by
  induction index with
  | zero => rfl
  | succ index ih =>
      change count (encodeTokenPairs (encodeUnaryTokens index) ++ suffix) = _
      exact ih

theorem count_literal (literal : CNFLiteral) (suffix : BitString) :
    count (encodeTokenPairs (encodeLiteralTokens literal) ++ suffix) = count suffix := by
  unfold encodeLiteralTokens
  cases positive : literal.positive <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals exact count_unary literal.variableIndex suffix

theorem count_literals (literals : List CNFLiteral) (suffix : BitString) :
    count (encodeTokenPairs (encodeLiteralListTokens literals) ++ suffix) = count suffix := by
  induction literals with
  | nil => rfl
  | cons literal rest ih =>
      rw [encodeLiteralListTokens, NANDFrontend.encodeTokenPairs_append, List.append_assoc, count_literal]
      exact ih

theorem count_clause (clause : List CNFLiteral) (suffix : BitString) :
    count (encodeTokenPairs (encodeClauseTokens clause) ++ suffix) = count suffix + 1 := by
  change count (encodeTokenPairs (encodeLiteralListTokens clause ++ [.finish]) ++ suffix) + 1 = _
  rw [NANDFrontend.encodeTokenPairs_append, List.append_assoc, count_literals]
  rfl

theorem count_clauses (clauses : List (List CNFLiteral)) (suffix : BitString) :
    count (encodeTokenPairs (encodeClauseListTokens clauses) ++ suffix) = clauses.length + count suffix := by
  induction clauses with
  | nil => exact (Nat.zero_add _).symm
  | cons clause rest ih =>
      rw [encodeClauseListTokens, NANDFrontend.encodeTokenPairs_append, List.append_assoc, count_clause, ih, List.length_cons]
      omega

theorem count_formula (clauses : List (List CNFLiteral)) :
    count (GraphQuery.clauseData clauses) = clauses.length := by
  rw [GraphQuery.clauseData, NANDFrontend.encodeTokenPairs_append, count_clauses]
  exact Nat.add_zero _

end PNP.Concrete.NormalizerBlocks.ClauseCount
