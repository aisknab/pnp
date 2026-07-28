/-
Copyright (c) 2026 PNP Labs.

The pure all-input specification for the strict locked-NAND source parser.
Successful validation preserves the source bytes exactly.  Every malformed
input fails closed to the empty word.
-/

import PNP.Concrete.LockedNANDReduction

namespace PNP.Concrete.LockedNAND.SourceParser

/-- The source parser's validity language: decoding and intrinsic elaboration
succeeds for exactly one packed circuit. -/
def ValidEncodedCircuit : Language := fun bits =>
  ∃ packed : PackedCircuit,
    decodeElaboratedCircuit bits = some packed

/-- Preserve every valid encoded source verbatim and clear every malformed
source.  The later work machine implements this total specification. -/
def validatedSourceBytes (bits : BitString) : BitString :=
  match decodeElaboratedCircuit bits with
  | none => []
  | some _ => bits

/-- Any successful elaborated decode witnesses source-language validity. -/
theorem valid_of_decoded {bits : BitString} {packed : PackedCircuit}
    (decoded : decodeElaboratedCircuit bits = some packed) :
    ValidEncodedCircuit bits :=
  ⟨packed, decoded⟩

/-- A failed elaborated decode cannot be a valid encoded source. -/
theorem not_valid_of_decode_none {bits : BitString}
    (malformed : decodeElaboratedCircuit bits = none) :
    ¬ ValidEncodedCircuit bits := by
  intro valid
  rcases valid with ⟨packed, decoded⟩
  rw [malformed] at decoded
  cases decoded

/-- Invalidity determines the decoder's unique failure branch. -/
theorem decode_none_of_not_valid {bits : BitString}
    (invalid : ¬ ValidEncodedCircuit bits) :
    decodeElaboratedCircuit bits = none := by
  cases decoded : decodeElaboratedCircuit bits with
  | none => rfl
  | some packed =>
      exact (invalid (valid_of_decoded decoded)).elim

/-- Validity is equivalently observable as the decoder not returning `none`. -/
theorem valid_iff_decodeElaboratedCircuit_ne_none (bits : BitString) :
    ValidEncodedCircuit bits ↔
      decodeElaboratedCircuit bits ≠ none := by
  constructor
  · intro valid malformed
    exact not_valid_of_decode_none malformed valid
  · intro succeeds
    cases decoded : decodeElaboratedCircuit bits with
    | none => exact (succeeds decoded).elim
    | some packed => exact valid_of_decoded decoded

/-- Exact successful behavior: validation returns the original source bytes. -/
theorem validatedSourceBytes_of_decoded
    (bits : BitString) (packed : PackedCircuit)
    (decoded : decodeElaboratedCircuit bits = some packed) :
    validatedSourceBytes bits = bits := by
  unfold validatedSourceBytes
  rw [decoded]

/-- Exact fail-closed behavior: decoder failure clears the source bytes. -/
theorem validatedSourceBytes_of_decode_none
    (bits : BitString)
    (malformed : decodeElaboratedCircuit bits = none) :
    validatedSourceBytes bits = [] := by
  unfold validatedSourceBytes
  rw [malformed]

/-- Valid inputs are preserved byte-for-byte. -/
theorem validatedSourceBytes_of_valid {bits : BitString}
    (valid : ValidEncodedCircuit bits) :
    validatedSourceBytes bits = bits := by
  rcases valid with ⟨packed, decoded⟩
  exact validatedSourceBytes_of_decoded bits packed decoded

/-- Invalid inputs are cleared rather than normalized or partially retained. -/
theorem validatedSourceBytes_of_not_valid {bits : BitString}
    (invalid : ¬ ValidEncodedCircuit bits) :
    validatedSourceBytes bits = [] :=
  validatedSourceBytes_of_decode_none bits
    (decode_none_of_not_valid invalid)

/-- The total validator has only the exact-success and fail-closed outputs. -/
theorem validatedSourceBytes_eq_source_or_empty (bits : BitString) :
    validatedSourceBytes bits = bits ∨
      validatedSourceBytes bits = [] := by
  cases decoded : decodeElaboratedCircuit bits with
  | none =>
      exact Or.inr
        (validatedSourceBytes_of_decode_none bits decoded)
  | some packed =>
      exact Or.inl
        (validatedSourceBytes_of_decoded bits packed decoded)

/-- Validation never increases the concrete output length. -/
theorem validatedSourceBytes_length_le (bits : BitString) :
    (validatedSourceBytes bits).length ≤ bits.length := by
  cases decoded : decodeElaboratedCircuit bits with
  | none =>
      rw [validatedSourceBytes_of_decode_none bits decoded]
      exact Nat.zero_le bits.length
  | some packed =>
      rw [validatedSourceBytes_of_decoded bits packed decoded]
      exact Nat.le_refl bits.length

/-- The named bit-size interface obeys the same nonexpansion bound. -/
theorem validatedSourceBytes_size_le (bits : BitString) :
    BitString.size (validatedSourceBytes bits) ≤
      BitString.size bits := by
  exact validatedSourceBytes_length_le bits

/-- The empty word is malformed in the strict source grammar. -/
theorem empty_not_validEncodedCircuit :
    ¬ ValidEncodedCircuit [] := by
  exact not_valid_of_decode_none rfl

/-- Empty input therefore follows the explicit fail-closed branch. -/
theorem validatedSourceBytes_empty :
    validatedSourceBytes [] = [] := by
  exact validatedSourceBytes_of_decode_none [] rfl

/-- Revalidating an already validated output is observationally inert. -/
theorem validatedSourceBytes_idempotent (bits : BitString) :
    validatedSourceBytes (validatedSourceBytes bits) =
      validatedSourceBytes bits := by
  cases decoded : decodeElaboratedCircuit bits with
  | none =>
      rw [validatedSourceBytes_of_decode_none bits decoded]
      exact validatedSourceBytes_empty
  | some packed =>
      rw [validatedSourceBytes_of_decoded bits packed decoded]
      exact validatedSourceBytes_of_decoded bits packed decoded

end PNP.Concrete.LockedNAND.SourceParser
