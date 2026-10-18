import PNP.Concrete.ResidualReduction.MatrixStrictHeader

/-! Exact all-input classification of the two unary fields and matrix payload.
Every bit pattern of the required payload length is concrete affine data.
Missing header terminators, truncation, and trailing bytes are rejected by the
same canonical codec used to state the eventual machine output theorem. -/

namespace PNP.Concrete.ResidualReduction.MatrixInputFields
open PNP.Concrete
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixInputEncoding
open PNP.Concrete.ResidualReduction.MatrixStrictHeader

structure Fields where
  dimension : Nat
  rows : Nat
  payload : BitString
  terminated : Bool

def fields (input : BitString) : Fields :=
  let first := scan input
  let second := scan first.rest
  ⟨first.count, second.count, second.rest, second.terminated⟩

theorem scan_failure_rest (input : BitString) (failed : (scan input).terminated = false) :
    (scan input).rest = [] := by
  induction input with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false => cases failed
    | true => exact ih failed

theorem first_terminated (input : BitString) (success : (fields input).terminated = true) :
    (scan input).terminated = true := by
  cases first : (scan input).terminated with
  | false =>
    have empty := scan_failure_rest input first
    change (scan (scan input).rest).terminated = true at success
    rw [empty] at success
    cases success
  | true => rfl

theorem split (input : BitString) (success : (fields input).terminated = true) :
    input = natural (fields input).dimension ++
      (natural (fields input).rows ++ (fields input).payload) := by
  have first := first_terminated input success
  have parsedFirst : BitString.decodeLength input = some ((scan input).count, (scan input).rest) := by
    rw [scan_parse, first]
    rfl
  have parsedSecond : BitString.decodeLength (scan input).rest =
      some ((fields input).rows, (fields input).payload) := by
    rw [scan_parse]
    change (if (fields input).terminated then some ((fields input).rows, (fields input).payload) else none) = _
    rw [success]
    rfl
  have firstBytes := natural_sound input (scan input).count (scan input).rest parsedFirst
  have secondBytes := natural_sound (scan input).rest (fields input).rows (fields input).payload parsedSecond
  exact firstBytes.symm.trans
    (congrArg (fun rest => natural (scan input).count ++ rest) secondBytes.symm)

theorem canonical_fields (n : Nat) (rows : System n) :
    fields (codec.encode ⟨n, rows⟩) = ⟨n, rows.length, matrixBits rows, true⟩ := by
  rw [codec_bits]
  simp only [fields, scan_canonical]

theorem size_bounds (input : BitString) :
    (fields input).dimension ≤ input.length ∧ (fields input).rows ≤ input.length ∧
      (fields input).payload.length ≤ input.length := by
  have first := scan_size input
  have second := scan_size (scan input).rest
  change (scan input).count ≤ input.length ∧ (scan (scan input).rest).count ≤ input.length ∧
    (scan (scan input).rest).rest.length ≤ input.length
  constructor
  · omega
  · constructor <;> omega

theorem decode_none_header (input : BitString) (failed : (fields input).terminated = false) :
    codec.decode input = none := by
  cases parsed : codec.decode input with
  | none => rfl
  | some problem =>
    rcases problem with ⟨n, rows⟩
    have bytes := (canonical input ⟨n, rows⟩).mp parsed
    rw [← bytes, canonical_fields] at failed
    cases failed

theorem decode_none_length (input : BitString)
    (wrong : (fields input).payload.length ≠ ((fields input).dimension + 1) * (fields input).rows) :
    codec.decode input = none := by
  cases parsed : codec.decode input with
  | none => rfl
  | some problem =>
    rcases problem with ⟨n, rows⟩
    have bytes := (canonical input ⟨n, rows⟩).mp parsed
    rw [← bytes, canonical_fields] at wrong
    exact (wrong (matrixBits_length rows)).elim

theorem valid_payload (input : BitString) (success : (fields input).terminated = true)
    (length : (fields input).payload.length = ((fields input).dimension + 1) * (fields input).rows) :
    ∃ rows : System (fields input).dimension,
      rows.length = (fields input).rows ∧ matrixBits rows = (fields input).payload ∧
      codec.encode ⟨(fields input).dimension, rows⟩ = input := by
  obtain ⟨rows, count, bytes⟩ := payload_complete (fields input).dimension (fields input).rows
    (fields input).payload length
  refine ⟨rows, count, bytes, ?_⟩
  rw [codec_bits, count, bytes]
  exact (split input success).symm

end PNP.Concrete.ResidualReduction.MatrixInputFields
