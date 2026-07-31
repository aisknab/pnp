/-
Copyright (c) 2026 PNP Labs.

The total source-language contract for the standalone concrete CNF parser.
Successful validation preserves the canonical CNF bytes exactly.  Every
malformed input fails closed to the empty word.
-/

import PNP.Concrete.CNF

namespace PNP.Concrete.CNFSourceParser

/-- The strict concrete CNF source language: the complete encoded word
decodes to one formula, including its required final zero pad bit. -/
def ValidEncodedCNF : Language := fun bits =>
  ∃ formula : CNFFormula, decodeEncodedCNF bits = some formula

/-- Preserve a successfully decoded CNF word verbatim and clear every
malformed word.  The literal parser machine implements this specification. -/
def validatedCNFBytes (bits : BitString) : BitString :=
  match decodeEncodedCNF bits with
  | none => []
  | some _ => bits

theorem valid_of_decoded {bits : BitString} {formula : CNFFormula}
    (decoded : decodeEncodedCNF bits = some formula) :
    ValidEncodedCNF bits :=
  ⟨formula, decoded⟩

theorem not_valid_of_decode_none {bits : BitString}
    (malformed : decodeEncodedCNF bits = none) :
    ¬ ValidEncodedCNF bits := by
  intro valid
  rcases valid with ⟨formula, decoded⟩
  rw [malformed] at decoded
  cases decoded

theorem decode_none_of_not_valid {bits : BitString}
    (invalid : ¬ ValidEncodedCNF bits) :
    decodeEncodedCNF bits = none := by
  cases decoded : decodeEncodedCNF bits with
  | none => rfl
  | some formula =>
      exact (invalid (valid_of_decoded decoded)).elim

theorem valid_iff_decodeEncodedCNF_ne_none (bits : BitString) :
    ValidEncodedCNF bits ↔ decodeEncodedCNF bits ≠ none := by
  constructor
  · intro valid malformed
    exact not_valid_of_decode_none malformed valid
  · intro succeeds
    cases decoded : decodeEncodedCNF bits with
    | none => exact (succeeds decoded).elim
    | some formula => exact valid_of_decoded decoded

theorem validatedCNFBytes_of_decoded
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    validatedCNFBytes bits = bits := by
  simp [validatedCNFBytes, decoded]

theorem validatedCNFBytes_of_decode_none
    (bits : BitString)
    (malformed : decodeEncodedCNF bits = none) :
    validatedCNFBytes bits = [] := by
  simp [validatedCNFBytes, malformed]

theorem validatedCNFBytes_of_valid {bits : BitString}
    (valid : ValidEncodedCNF bits) :
    validatedCNFBytes bits = bits := by
  rcases valid with ⟨formula, decoded⟩
  exact validatedCNFBytes_of_decoded bits formula decoded

theorem validatedCNFBytes_of_not_valid {bits : BitString}
    (invalid : ¬ ValidEncodedCNF bits) :
    validatedCNFBytes bits = [] :=
  validatedCNFBytes_of_decode_none bits
    (decode_none_of_not_valid invalid)

theorem validatedCNFBytes_eq_source_or_empty (bits : BitString) :
    validatedCNFBytes bits = bits ∨ validatedCNFBytes bits = [] := by
  cases decoded : decodeEncodedCNF bits with
  | none =>
      exact Or.inr (validatedCNFBytes_of_decode_none bits decoded)
  | some formula =>
      exact Or.inl (validatedCNFBytes_of_decoded bits formula decoded)

theorem validatedCNFBytes_length_le (bits : BitString) :
    (validatedCNFBytes bits).length ≤ bits.length := by
  rcases validatedCNFBytes_eq_source_or_empty bits with source | empty
  · rw [source]
    exact Nat.le_refl bits.length
  · rw [empty]
    exact Nat.zero_le bits.length

theorem validatedCNFBytes_size_le (bits : BitString) :
    BitString.size (validatedCNFBytes bits) ≤ BitString.size bits :=
  validatedCNFBytes_length_le bits

theorem empty_not_validEncodedCNF :
    ¬ ValidEncodedCNF [] :=
  not_valid_of_decode_none rfl

theorem validatedCNFBytes_empty :
    validatedCNFBytes [] = [] :=
  validatedCNFBytes_of_decode_none [] rfl

theorem validatedCNFBytes_idempotent (bits : BitString) :
    validatedCNFBytes (validatedCNFBytes bits) =
      validatedCNFBytes bits := by
  cases decoded : decodeEncodedCNF bits with
  | none =>
      rw [validatedCNFBytes_of_decode_none bits decoded]
      exact validatedCNFBytes_empty
  | some formula =>
      rw [validatedCNFBytes_of_decoded bits formula decoded]
      exact validatedCNFBytes_of_decoded bits formula decoded

end PNP.Concrete.CNFSourceParser
