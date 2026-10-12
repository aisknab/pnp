/-
Copyright (c) 2026 PNP Labs.

The complete strict CNF grammar is canonical on every successful decode.
These inverse laws support a finite decoded-data record with a unary width and
the original, ordered literal/clause token stream. No valid-input premise will
be required by the eventual register decoder.
-/

import PNP.Concrete.CNF

namespace PNP.Concrete.CNFRegisterDecoder

def clausesSuffix (clauses : List (List CNFLiteral)) : List CNFToken :=
  encodeClauseListTokens clauses ++ [.finish]

def clauseSuffix (clause : List CNFLiteral) (clauses : List (List CNFLiteral)) : List CNFToken :=
  encodeLiteralListTokens clause ++ .finish :: clausesSuffix clauses

theorem clausesSuffix_cons (clause : List CNFLiteral) (clauses : List (List CNFLiteral)) :
    clausesSuffix (clause :: clauses) = .sep :: clauseSuffix clause clauses := by
  simp only [clausesSuffix, clauseSuffix, encodeClauseListTokens, encodeClauseTokens,
    List.cons_append, List.append_assoc, List.nil_append]

theorem clauseSuffix_cons (literal : CNFLiteral) (clause : List CNFLiteral)
    (clauses : List (List CNFLiteral)) :
    clauseSuffix (literal :: clause) clauses = encodeLiteralTokens literal ++ clauseSuffix clause clauses := by
  exact List.append_assoc _ _ _

theorem unary_tokens (count : Nat) :
    encodeUnaryTokens count = List.replicate count CNFToken.t ++ [.f] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [encodeUnaryTokens, List.replicate_succ, List.cons_append] using congrArg (List.cons CNFToken.t) ih

theorem replicate_succ_tail (count : Nat) (suffix : List CNFToken) :
    List.replicate (count + 1) CNFToken.t ++ suffix =
      List.replicate count CNFToken.t ++ .t :: suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons CNFToken.t) ih

private theorem suffix_inverse (tokens : List CNFToken) :
    (∀ clauses, decodeFormulaClauses tokens = some clauses → clausesSuffix clauses = tokens) ∧
    (∀ clause clauses, decodeFormulaClause tokens = some (clause, clauses) →
      clauseSuffix clause clauses = tokens) ∧
    (∀ positive index clause clauses,
      decodeFormulaLiteral positive index tokens = some (clause, clauses) →
      clauseSuffix clause clauses =
        (if positive then CNFToken.t else .f) :: (List.replicate index .t ++ tokens)) := by
  induction tokens with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · intro clauses decoded; cases decoded
      · intro clause clauses decoded; cases decoded
      · intro positive index clause clauses decoded; cases decoded
  | cons token rest ih =>
      refine ⟨?_, ?_, ?_⟩
      · intro clauses decoded
        cases token with
        | f => cases decoded
        | t => cases decoded
        | sep =>
            cases tail : decodeFormulaClause rest with
            | none => simp only [decodeFormulaClauses, tail] at decoded; cases decoded
            | some pair =>
                rcases pair with ⟨clause, remaining⟩
                simp only [decodeFormulaClauses, tail] at decoded
                cases decoded
                rw [clausesSuffix_cons, ih.2.1 clause remaining tail]
        | finish =>
            cases rest with
            | nil => cases decoded; rfl
            | cons head more => cases decoded
      · intro clause clauses decoded
        cases token with
        | f => exact ih.2.2 false 0 clause clauses decoded
        | t => exact ih.2.2 true 0 clause clauses decoded
        | sep => cases decoded
        | finish =>
            cases tail : decodeFormulaClauses rest with
            | none => simp only [decodeFormulaClause, tail] at decoded; cases decoded
            | some remaining =>
                simp only [decodeFormulaClause, tail] at decoded
                cases decoded
                change .finish :: clausesSuffix clauses = .finish :: rest
                exact congrArg (List.cons CNFToken.finish) (ih.1 clauses tail)
      · intro positive index clause clauses decoded
        cases token with
        | f =>
            cases tail : decodeFormulaClause rest with
            | none => simp only [decodeFormulaLiteral, tail] at decoded; cases decoded
            | some pair =>
                rcases pair with ⟨remaining, more⟩
                simp only [decodeFormulaLiteral, tail] at decoded
                cases decoded
                rw [clauseSuffix_cons, ih.2.1 remaining clauses tail]
                simp only [encodeLiteralTokens, unary_tokens, List.cons_append,
                  List.append_assoc, List.nil_append]
        | t =>
            have checked := ih.2.2 positive (index + 1) clause clauses decoded
            rw [replicate_succ_tail] at checked
            exact checked
        | sep => cases decoded
        | finish => cases decoded

theorem clauses_of_decode (tokens : List CNFToken) (clauses : List (List CNFLiteral))
    (decoded : decodeFormulaClauses tokens = some clauses) : clausesSuffix clauses = tokens :=
  (suffix_inverse tokens).1 clauses decoded

theorem clause_of_decode (tokens : List CNFToken) (clause : List CNFLiteral)
    (clauses : List (List CNFLiteral)) (decoded : decodeFormulaClause tokens = some (clause, clauses)) :
    clauseSuffix clause clauses = tokens :=
  (suffix_inverse tokens).2.1 clause clauses decoded

theorem header_of_decode (count : Nat) (tokens : List CNFToken) (formula : CNFFormula)
    (decoded : decodeFormulaHeader count tokens = some formula) :
    encodeCNFTokens formula = List.replicate count .t ++ tokens := by
  induction tokens generalizing count formula with
  | nil => cases decoded
  | cons token rest ih =>
      cases token with
      | f =>
          cases tail : decodeFormulaClauses rest with
          | none => simp only [decodeFormulaHeader, tail] at decoded; cases decoded
          | some clauses =>
              simp only [decodeFormulaHeader, tail] at decoded
              cases decoded
              unfold encodeCNFTokens
              rw [List.append_assoc]
              change encodeUnaryTokens count ++ clausesSuffix clauses = _
              rw [unary_tokens, clauses_of_decode rest clauses tail]
              simp only [List.append_assoc, List.cons_append, List.nil_append]
      | t =>
          have checked := ih (count + 1) formula decoded
          rw [replicate_succ_tail] at checked
          exact checked
      | sep => cases decoded
      | finish => cases decoded

theorem tokens_of_decode (tokens : List CNFToken) (formula : CNFFormula)
    (decoded : decodeCNFTokens tokens = some formula) : encodeCNFTokens formula = tokens :=
  header_of_decode 0 tokens formula decoded

theorem token_bits_ofBits (first second : Bool) :
    (CNFToken.ofBits first second).bits = [first, second] := by
  cases first <;> cases second <;> rfl

theorem pairs_of_decode : (bits : BitString) → (tokens : List CNFToken) →
    decodeFormulaTokenPairs bits = some tokens → encodeTokenPairs tokens ++ [false] = bits
  | [], _, decoded => by cases decoded
  | [false], _, decoded => by cases decoded; rfl
  | [true], _, decoded => by cases decoded
  | first :: second :: rest, tokens, decoded => by
      cases tail : decodeFormulaTokenPairs rest with
      | none => simp only [decodeFormulaTokenPairs, tail] at decoded; cases decoded
      | some remaining =>
          simp only [decodeFormulaTokenPairs, tail] at decoded
          cases decoded
          simp only [encodeTokenPairs, token_bits_ofBits, List.cons_append, List.nil_append]
          exact congrArg (fun suffix => first :: second :: suffix) (pairs_of_decode rest remaining tail)

theorem encoded_of_decode (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) : encodeCNF formula = bits := by
  cases tokens : decodeFormulaTokenPairs bits with
  | none => simp only [decodeEncodedCNF, tokens] at decoded; cases decoded
  | some values =>
      have checked : decodeCNFTokens values = some formula := by
        simpa only [decodeEncodedCNF, tokens] using decoded
      unfold encodeCNF
      rw [tokens_of_decode values formula checked]
      exact pairs_of_decode bits values tokens

/-- Finite decoded data: unary width, delimiter, and exact ordered clause data. -/
def formulaData (formula : CNFFormula) : BitString :=
  List.replicate formula.variableCount true ++ false :: encodeTokenPairs (clausesSuffix formula.clauses)

/-- The leading bit distinguishes malformed input from a complete parsed formula. -/
def resultData : Option CNFFormula → BitString
  | none => [false]
  | some formula => true :: formulaData formula

end PNP.Concrete.CNFRegisterDecoder
