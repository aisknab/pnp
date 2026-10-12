/-
Copyright (c) 2026 PNP Labs.

Canonical clause semantics of the finite occurrence query. The result uses
the first matching literal in the original list, not a deduplicated set.
The proof covers arbitrary clause lengths and arbitrary variable indices.
-/

import PNP.Concrete.NormalizerOccurrenceTokens

namespace PNP.Concrete.NormalizerBlocks.Occurrence

theorem tokenScan_inactive (values : List CNFToken) (r : Registers) (inactive : r.active = []) :
    tokenScan values r = {r with input := encodeTokenPairs values} := by
  cases values <;> simp only [tokenScan, inactive]

def answer : Option CNFLiteral → BitString
  | none => [false]
  | some literal => [true, literal.positive]

def waiting (target : Nat) (remaining excess sign reserved : BitString) : Registers :=
  ⟨[], List.replicate target true, remaining, excess, sign, [], [true], reserved, [false]⟩

theorem tokenScan_literal (literal : CNFLiteral) (target : Nat) (rest : List CNFToken)
    (remaining excess sign reserved : BitString) :
    tokenScan (encodeLiteralTokens literal ++ rest) (waiting target remaining excess sign reserved) =
      tokenScan (.f :: rest)
        (counting (List.replicate target true) (target - literal.variableIndex)
          (literal.variableIndex - target) [literal.positive] reserved [false]) := by
  cases literal with
  | mk positive index =>
      cases positive
      · change tokenScan (encodeUnaryTokens index ++ rest)
          (counting (List.replicate target true) target 0 [false] reserved [false]) = _
        simpa only [Nat.zero_add] using
          tokenScan_unary index target 0 (List.replicate target true) [false] reserved [false] rest
      · change tokenScan (encodeUnaryTokens index ++ rest)
          (counting (List.replicate target true) target 0 [true] reserved [false]) = _
        simpa only [Nat.zero_add] using
          tokenScan_unary index target 0 (List.replicate target true) [true] reserved [false] rest

theorem tokenScan_clause_correct (clause : List CNFLiteral) (target : Nat)
    (remaining excess sign reserved : BitString) :
    (tokenScan (encodeLiteralListTokens clause ++ [.finish])
      (waiting target remaining excess sign reserved)).output =
        answer (clause.find? (fun literal => literal.variableIndex == target)) := by
  induction clause generalizing remaining excess sign with
  | nil => rfl
  | cons literal rest ih =>
      rw [encodeLiteralListTokens, List.append_assoc, tokenScan_literal]
      cases literal with
      | mk positive index =>
          by_cases same : index = target
          · subst index
            have sameIndex : (target == target) = true := by
              change decide (target = target) = true
              exact decide_eq_true rfl
            simp only [Nat.sub_self, List.find?_cons, sameIndex,
              counting, List.replicate_zero, tokenScan, tokenResult, foundState, answer]
            rw [tokenScan_inactive _ _ rfl]
          · have different : (index == target) = false := beq_eq_false_iff_ne.mpr same
            simp only [List.find?_cons, different]
            cases left : target - index with
            | zero =>
                cases right : index - target with
                | zero => exact False.elim (same (Nat.le_antisymm
                    (Nat.le_of_sub_eq_zero right) (Nat.le_of_sub_eq_zero left)))
                | succ extra =>
                    simpa only [left, right, counting, List.replicate_zero, List.replicate_succ,
                      tokenScan, tokenResult, waiting] using
                      ih [] (List.replicate (extra + 1) true) [positive]
            | succ remaining =>
                have right : index - target = 0 := by
                  apply Nat.sub_eq_zero_of_le
                  apply Nat.le_of_lt
                  apply Nat.lt_of_sub_pos
                  rw [left]
                  exact Nat.zero_lt_succ _
                simpa only [left, right, counting, List.replicate_zero, List.replicate_succ,
                  tokenScan, tokenResult, waiting] using
                  ih (List.replicate (remaining + 1) true) [] [positive]

end PNP.Concrete.NormalizerBlocks.Occurrence
