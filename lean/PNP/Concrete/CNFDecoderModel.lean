/-
Copyright (c) 2026 PNP Labs.

A complete four-state token transducer for the strict CNF grammar.
The header is materialized as a unary field; clause and literal data retain their
exact ordered token encoding. The value theorem covers the whole grammar.
-/

import PNP.Concrete.CNFDecoderGrammar

namespace PNP.Concrete.CNFRegisterDecoder

inductive Mode where
  | header | clauses | clause | literal
deriving DecidableEq, Repr

inductive Action where
  | invalid | next (mode : Mode) | finish
deriving DecidableEq, Repr

def transition : Mode → CNFToken → Action
  | .header, .f => .next .clauses
  | .header, .t => .next .header
  | .clauses, .sep => .next .clause
  | .clauses, .finish => .finish
  | .clause, .f => .next .literal
  | .clause, .t => .next .literal
  | .clause, .finish => .next .clauses
  | .literal, .f => .next .clause
  | .literal, .t => .next .literal
  | _, _ => .invalid

def emitted : Mode → CNFToken → BitString
  | .header, .f => [false]
  | .header, .t => [true]
  | .header, _ => []
  | _, token => token.bits

theorem emitted_length_le (mode : Mode) (token : CNFToken) : (emitted mode token).length ≤ 2 := by
  cases mode <;> cases token <;> decide

def recognize : Mode → List CNFToken → Bool
  | _, [] => false
  | mode, token :: rest =>
      match transition mode token with
      | .invalid => false
      | .next next => recognize next rest
      | .finish => rest.isEmpty

def parseTokens : Mode → List CNFToken → Option BitString
  | _, [] => none
  | mode, token :: rest =>
      match transition mode token with
      | .invalid => none
      | .next next => (parseTokens next rest).map (fun suffix => emitted mode token ++ suffix)
      | .finish => if rest.isEmpty then some (emitted mode token) else none

private theorem map_isSome {α β : Type} (f : α → β) (value : Option α) :
    (value.map f).isSome = value.isSome := by
  cases value <;> rfl

theorem parseTokens_isSome (mode : Mode) (tokens : List CNFToken) :
    (parseTokens mode tokens).isSome = recognize mode tokens := by
  induction tokens generalizing mode with
  | nil => rfl
  | cons token rest ih =>
      cases action : transition mode token with
      | invalid => simp only [parseTokens, recognize, action]; rfl
      | next next => simpa only [parseTokens, recognize, action, map_isSome] using ih next
      | finish =>
          cases empty : rest.isEmpty <;> simp only [parseTokens, recognize, action, empty] <;> rfl

private theorem suffix_recognize (tokens : List CNFToken) :
    recognize .clauses tokens = (decodeFormulaClauses tokens).isSome ∧
    recognize .clause tokens = (decodeFormulaClause tokens).isSome ∧
    (∀ positive index, recognize .literal tokens = (decodeFormulaLiteral positive index tokens).isSome) := by
  induction tokens with
  | nil => exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | cons token rest ih =>
      refine ⟨?_, ?_, ?_⟩
      · cases token with
        | f => rfl
        | t => rfl
        | sep =>
            change recognize .clause rest = _
            rw [ih.2.1]
            cases decoded : decodeFormulaClause rest <;>
              simp only [decodeFormulaClauses, decoded] <;> rfl
        | finish => cases rest <;> rfl
      · cases token with
        | f => exact ih.2.2 false 0
        | t => exact ih.2.2 true 0
        | sep => rfl
        | finish =>
            change recognize .clauses rest = _
            rw [ih.1]
            cases decoded : decodeFormulaClauses rest <;>
              simp only [decodeFormulaClause, decoded] <;> rfl
      · intro positive index
        cases token with
        | f =>
            change recognize .clause rest = _
            rw [ih.2.1]
            cases decoded : decodeFormulaClause rest <;>
              simp only [decodeFormulaLiteral, decoded] <;> rfl
        | t => exact ih.2.2 positive (index + 1)
        | sep => rfl
        | finish => rfl

theorem recognize_header (count : Nat) (tokens : List CNFToken) :
    recognize .header tokens = (decodeFormulaHeader count tokens).isSome := by
  induction tokens generalizing count with
  | nil => rfl
  | cons token rest ih =>
      cases token with
      | f =>
          change recognize .clauses rest = _
          rw [(suffix_recognize rest).1]
          cases decoded : decodeFormulaClauses rest <;>
            simp only [decodeFormulaHeader, decoded] <;> rfl
      | t => exact ih (count + 1)
      | sep => rfl
      | finish => rfl

private theorem prepend_if (ok : Bool) (front suffix : BitString) :
    (if ok then some suffix else none).map (fun tail => front ++ tail) =
      if ok then some (front ++ suffix) else none := by
  cases ok <;> rfl

private theorem suffix_parse (tokens : List CNFToken) :
    parseTokens .clauses tokens =
      (if recognize .clauses tokens then some (encodeTokenPairs tokens) else none) ∧
    parseTokens .clause tokens =
      (if recognize .clause tokens then some (encodeTokenPairs tokens) else none) ∧
    parseTokens .literal tokens =
      (if recognize .literal tokens then some (encodeTokenPairs tokens) else none) := by
  induction tokens with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons token rest ih =>
      refine ⟨?_, ?_, ?_⟩
      · cases token with
        | f => rfl
        | t => rfl
        | sep =>
            simp only [parseTokens, recognize, transition, emitted, ih.2.1, prepend_if, encodeTokenPairs]
        | finish => cases rest <;> rfl
      · cases token with
        | f =>
            simp only [parseTokens, recognize, transition, emitted, ih.2.2, prepend_if, encodeTokenPairs]
        | t =>
            simp only [parseTokens, recognize, transition, emitted, ih.2.2, prepend_if, encodeTokenPairs]
        | sep => rfl
        | finish =>
            simp only [parseTokens, recognize, transition, emitted, ih.1, prepend_if, encodeTokenPairs]
      · cases token with
        | f =>
            simp only [parseTokens, recognize, transition, emitted, ih.2.1, prepend_if, encodeTokenPairs]
        | t =>
            simp only [parseTokens, recognize, transition, emitted, ih.2.2, prepend_if, encodeTokenPairs]
        | sep => rfl
        | finish => rfl

theorem parseTokens_clauses_canonical (clauses : List (List CNFLiteral)) :
    parseTokens .clauses (clausesSuffix clauses) = some (encodeTokenPairs (clausesSuffix clauses)) := by
  rw [(suffix_parse _).1, (suffix_recognize _).1]
  have canonical := decodeFormulaClauses_canonical clauses
  change decodeFormulaClauses (clausesSuffix clauses) = some clauses at canonical
  rw [canonical]
  rfl

theorem parseTokens_header_unary (count : Nat) (suffix : List CNFToken) :
    parseTokens .header (encodeUnaryTokens count ++ suffix) =
      (parseTokens .clauses suffix).map
        (fun tail => List.replicate count true ++ false :: tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [encodeUnaryTokens, List.cons_append, parseTokens, transition, emitted, ih]
      cases parseTokens .clauses suffix <;>
        simp only [Option.map_none, Option.map_some, List.replicate_succ, List.cons_append, List.nil_append]

theorem parseTokens_canonical (formula : CNFFormula) :
    parseTokens .header (encodeCNFTokens formula) = some (formulaData formula) := by
  have shape : encodeCNFTokens formula =
      encodeUnaryTokens formula.variableCount ++ clausesSuffix formula.clauses :=
    List.append_assoc _ _ _
  rw [shape, parseTokens_header_unary, parseTokens_clauses_canonical]
  rfl

theorem parseTokens_none (tokens : List CNFToken) (decoded : decodeCNFTokens tokens = none) :
    parseTokens .header tokens = none := by
  have recognized := (parseTokens_isSome Mode.header tokens).trans (recognize_header 0 tokens)
  change (parseTokens .header tokens).isSome = (decodeCNFTokens tokens).isSome at recognized
  rw [decoded] at recognized
  cases parsed : parseTokens .header tokens with
  | none => rfl
  | some value => rw [parsed] at recognized; cases recognized

end PNP.Concrete.CNFRegisterDecoder
