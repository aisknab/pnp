/-
Copyright (c) 2026 PNP Labs.

Raw-bit semantics for the strict streaming CNF decoder. A final zero pad is
mandatory, and malformed strings produce an explicit data result.
-/

import PNP.Concrete.CNFDecoderModel

namespace PNP.Concrete.CNFRegisterDecoder

def isPad : BitString → Bool
  | [false] => true
  | _ => false

def parseBits : Mode → BitString → Option BitString
  | _, [] => none
  | _, [_] => none
  | mode, first :: second :: rest =>
      let token := CNFToken.ofBits first second
      match transition mode token with
      | .invalid => none
      | .next next => (parseBits next rest).map (fun suffix => emitted mode token ++ suffix)
      | .finish => if isPad rest then some (emitted mode token) else none

theorem parseBits_pairs (mode : Mode) (bits : BitString) :
    parseBits mode bits =
      match decodeFormulaTokenPairs bits with
      | none => none
      | some tokens => parseTokens mode tokens := by
  match bits with
  | [] => rfl
  | [bit] => cases bit <;> rfl
  | first :: second :: rest =>
      cases action : transition mode (CNFToken.ofBits first second) with
      | invalid =>
          cases pairs : decodeFormulaTokenPairs rest <;>
            simp only [parseBits, action, decodeFormulaTokenPairs, pairs, parseTokens]
      | next next =>
          simp only [parseBits, action, decodeFormulaTokenPairs, parseBits_pairs next rest]
          cases pairs : decodeFormulaTokenPairs rest <;>
            simp only [parseTokens, action, Option.map_none]
      | finish =>
          cases rest with
          | nil => simp only [parseBits, action, isPad, decodeFormulaTokenPairs]; rfl
          | cons bit tail =>
              cases tail with
              | nil => cases bit <;>
                  simp only [parseBits, action, isPad, decodeFormulaTokenPairs, parseTokens] <;> rfl
              | cons bit' tail' =>
                  cases pairs : decodeFormulaTokenPairs tail' <;>
                    simp only [parseBits, action, isPad, decodeFormulaTokenPairs, pairs, parseTokens] <;> rfl
termination_by bits.length

theorem parseBits_canonical (formula : CNFFormula) :
    parseBits .header (encodeCNF formula) = some (formulaData formula) := by
  rw [parseBits_pairs]
  simp only [encodeCNF, decodeFormulaTokenPairs_canonical, parseTokens_canonical]

theorem parseBits_eq (bits : BitString) :
    parseBits .header bits = (decodeEncodedCNF bits).map formulaData := by
  cases decoded : decodeEncodedCNF bits with
  | none =>
      rw [parseBits_pairs]
      cases pairs : decodeFormulaTokenPairs bits with
      | none => rfl
      | some tokens =>
          have failed : decodeCNFTokens tokens = none := by
            simpa only [decodeEncodedCNF, pairs] using decoded
          exact parseTokens_none tokens failed
  | some formula =>
      have canonical := encoded_of_decode bits formula decoded
      rw [← canonical, parseBits_canonical]
      rfl

def decodedData (bits : BitString) : BitString :=
  match parseBits .header bits with
  | none => [false]
  | some payload => true :: payload

theorem decodedData_eq_result (bits : BitString) :
    decodedData bits = resultData (decodeEncodedCNF bits) := by
  unfold decodedData
  rw [parseBits_eq]
  cases decodeEncodedCNF bits <;> rfl

theorem parseBits_length (mode : Mode) (bits payload : BitString)
    (parsed : parseBits mode bits = some payload) : payload.length ≤ bits.length := by
  match bits with
  | [] => cases parsed
  | [_] => cases parsed
  | first :: second :: rest =>
      cases action : transition mode (CNFToken.ofBits first second) with
      | invalid =>
          simp only [parseBits, action] at parsed
          cases parsed
      | next next =>
          cases suffix : parseBits next rest with
          | none =>
              simp only [parseBits, action, suffix, Option.map_none] at parsed
              cases parsed
          | some tail =>
              have equal : emitted mode (CNFToken.ofBits first second) ++ tail = payload := by
                simpa only [parseBits, action, suffix, Option.map_some, Option.some.injEq] using parsed
              have ih := parseBits_length next rest tail suffix
              have short := emitted_length_le mode (CNFToken.ofBits first second)
              rw [← equal, List.length_append]
              simp only [List.length_cons]
              omega
      | finish =>
          cases pad : isPad rest with
          | false =>
              simp only [parseBits, action, pad, Bool.false_eq_true, ↓reduceIte] at parsed
              cases parsed
          | true =>
              have equal : emitted mode (CNFToken.ofBits first second) = payload := by
                simpa only [parseBits, action, pad, ↓reduceIte, Option.some.injEq] using parsed
              rw [← equal]
              have short := emitted_length_le mode (CNFToken.ofBits first second)
              simp only [List.length_cons]
              omega
termination_by bits.length

theorem decodedData_length (bits : BitString) : (decodedData bits).length ≤ bits.length + 1 := by
  unfold decodedData
  cases parsed : parseBits .header bits with
  | none => exact Nat.succ_le_succ (Nat.zero_le _)
  | some payload => exact Nat.succ_le_succ (parseBits_length .header bits payload parsed)

end PNP.Concrete.CNFRegisterDecoder
