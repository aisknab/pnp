/-
Copyright (c) 2026 PNP Labs.

Observable blank-delimited output and the pure canonical handoff target.

An implicit blank cell and a materialized blank cell are indistinguishable to
the raw transition system.  Output therefore stops at the first blank instead
of using the finite `right`-list boundary as data.  `handoffTarget` specifies
the exact input-form tape required by a later pipeline stage; this module does
not claim that a raw machine constructs that target.
-/

import PNP.Concrete.Machine

namespace PNP.Concrete

namespace Tape

/-- Decode the bit prefix before the first blank cell. -/
def decodeOutputCells : List TapeSymbol → BitString
  | [] => []
  | .blank :: _ => []
  | .zero :: rest => false :: decodeOutputCells rest
  | .one :: rest => true :: decodeOutputCells rest

/-- Canonically encoded bit cells decode exactly. -/
theorem decodeOutputCells_map_ofBool (bits : BitString) :
    decodeOutputCells (bits.map TapeSymbol.ofBool) = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => exact congrArg (List.cons false) ih
      | true => exact congrArg (List.cons true) ih

/-- The first blank terminates output, independently of every later cell. -/
theorem decodeOutputCells_append_blank (bits : BitString)
    (suffix : List TapeSymbol) :
    decodeOutputCells
        (bits.map TapeSymbol.ofBool ++ .blank :: suffix) = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => exact congrArg (List.cons false) ih
      | true => exact congrArg (List.cons true) ih

/-- Read output from the focused cell through the first blank delimiter. -/
def outputBits (tape : Tape) : BitString :=
  decodeOutputCells (tape.head :: tape.right)

/-- A canonical raw input tape exposes exactly its input bits as output. -/
theorem outputBits_ofInput (input : BitString) :
    outputBits (ofInput input) = input := by
  cases input with
  | nil => rfl
  | cons bit rest =>
      cases bit with
      | false =>
          exact congrArg (List.cons false)
            (decodeOutputCells_map_ofBool rest)
      | true =>
          exact congrArg (List.cons true)
            (decodeOutputCells_map_ofBool rest)

/-- Materializing the delimiter and any suffix after a canonical right-hand
bit region cannot change the decoded output. -/
theorem outputBits_right_append_blank (tape : Tape) (bits : BitString)
    (suffix : List TapeSymbol) :
    outputBits
        { tape with right :=
            bits.map TapeSymbol.ofBool ++ .blank :: suffix } =
      outputBits { tape with right := bits.map TapeSymbol.ofBool } := by
  cases tape with
  | mk left head right =>
      cases head with
      | blank => rfl
      | zero =>
          apply congrArg (List.cons false)
          rw [decodeOutputCells_append_blank,
            decodeOutputCells_map_ofBool]
      | one =>
          apply congrArg (List.cons true)
          rw [decodeOutputCells_append_blank,
            decodeOutputCells_map_ofBool]

/-- A blank focused cell denotes empty output regardless of represented
cells on either side. -/
theorem outputBits_blank_head (left right : List TapeSymbol) :
    outputBits { left := left, head := .blank, right := right } = [] := rfl

/-- Cells left of the output focus are not part of the decoded word. -/
theorem outputBits_set_left (tape : Tape) (left : List TapeSymbol) :
    outputBits { tape with left := left } = outputBits tape := by
  cases tape
  rfl

/-- Materializing the implicit blank immediately after a one-bit output does
not create an additional false bit. -/
theorem outputBits_explicit_blank_matches_implicit (bit : Bool) :
    outputBits
        { left := [], head := TapeSymbol.ofBool bit, right := [.blank] } =
      outputBits (ofInput [bit]) := by
  cases bit <;> rfl

/-- A right/left round trip may materialize a blank, but cannot change the
observable output. -/
theorem outputBits_moveRight_moveLeft (tape : Tape) :
    outputBits (tape.moveRight.moveLeft) = outputBits tape := by
  cases tape with
  | mk left head right =>
      cases right with
      | nil => cases head <;> rfl
      | cons first rest => rfl

/-- A left/right round trip may materialize a left blank, which is outside the
observable output region. -/
theorem outputBits_moveLeft_moveRight (tape : Tape) :
    outputBits (tape.moveLeft.moveRight) = outputBits tape := by
  cases tape with
  | mk left head right =>
      cases left <;> rfl

/-- Pure specification of the exact canonical tape expected at the next raw
machine's start state.  This is not an executable machine constructor. -/
def handoffTarget (tape : Tape) : Tape :=
  ofInput (outputBits tape)

/-- Canonicalization preserves the blank-delimited observable output. -/
theorem outputBits_handoffTarget (tape : Tape) :
    outputBits (handoffTarget tape) = outputBits tape := by
  exact outputBits_ofInput (outputBits tape)

/-- The pure canonical handoff target is idempotent. -/
theorem handoffTarget_idempotent (tape : Tape) :
    handoffTarget (handoffTarget tape) = handoffTarget tape := by
  unfold handoffTarget
  rw [outputBits_ofInput]

end Tape

end PNP.Concrete
