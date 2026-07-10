/-
Copyright (c) 2026 PNP Labs.

Executable bit strings, canonical framing, and a small natural-polynomial
language.  These definitions are deliberately independent of a machine model:
later concrete complexity layers can share one encoding and one notion of an
input-size bound.
-/

namespace PNP.Concrete

/-- The concrete alphabet used by the machine and language layers. -/
abbrev BitString := List Bool

namespace BitString

/-- Bit length, kept as a named operation so complexity statements do not rely
on representation-specific projections. -/
def size (bits : BitString) : Nat := bits.length

/-- A canonical self-delimiting frame.  A payload of length `n` is encoded as
`n` one-bits, a zero-bit delimiter, and then the payload itself. -/
def frame (payload : BitString) : BitString :=
  List.replicate payload.length true ++ false :: payload

/-- Parse the unary length header of a frame. -/
def decodeLength : BitString → Option (Nat × BitString)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
      match decodeLength rest with
      | none => none
      | some (n, suffix) => some (n + 1, suffix)

/-- Split exactly `n` bits from a string.  Unlike `List.take`/`List.drop`, this
parser rejects a short input rather than silently truncating it. -/
def splitExact : Nat → BitString → Option (BitString × BitString)
  | 0, bits => some ([], bits)
  | _ + 1, [] => none
  | n + 1, bit :: bits =>
      match splitExact n bits with
      | none => none
      | some (chunk, suffix) => some (bit :: chunk, suffix)

/-- Decode one frame, returning both its payload and the unconsumed suffix. -/
def decodeFrame (bits : BitString) : Option (BitString × BitString) :=
  match decodeLength bits with
  | none => none
  | some (n, rest) => splitExact n rest

/-- Encode an ordered pair as two consecutive canonical frames. -/
def pair (left right : BitString) : BitString := frame left ++ frame right

/-- Decode exactly two frames.  Trailing bits are rejected, making this a
canonical whole-string pair codec. -/
def decodePair (bits : BitString) : Option (BitString × BitString) :=
  match decodeFrame bits with
  | none => none
  | some (left, rest) =>
      match decodeFrame rest with
      | none => none
      | some (right, suffix) =>
          match suffix with
          | [] => some (left, right)
          | _ :: _ => none

/-! The corresponding theorems in the core list library are intentionally
reproved here by constructor recursion. This keeps the codec kernel free of
the `propext` dependency carried by the library's simplifier-oriented proofs. -/

theorem append_assoc_constructive (left middle right : BitString) :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons bit rest ih => exact congrArg (List.cons bit) ih

theorem append_nil_constructive (bits : BitString) : bits ++ [] = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => exact congrArg (List.cons bit) ih

theorem length_append_constructive (left right : BitString) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons _ rest ih =>
      change Nat.succ (rest ++ right).length = Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

theorem length_replicate_constructive (n : Nat) (bit : Bool) :
    (List.replicate n bit).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

theorem decodeLength_frameHeader (n : Nat) (suffix : BitString) :
    decodeLength (List.replicate n true ++ false :: suffix) = some (n, suffix) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      change (match decodeLength (List.replicate n true ++ false :: suffix) with
        | none => none
        | some (value, rest) => some (value + 1, rest)) = some (n + 1, suffix)
      rw [ih]

theorem decodeLength_noDelimiter (n : Nat) :
    decodeLength (List.replicate n true) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      change (match decodeLength (List.replicate n true) with
        | none => none
        | some (value, suffix) => some (value + 1, suffix)) = none
      rw [ih]

theorem splitExact_append (chunk suffix : BitString) :
    splitExact chunk.length (chunk ++ suffix) = some (chunk, suffix) := by
  induction chunk with
  | nil => rfl
  | cons bit tail ih =>
      change (match splitExact tail.length (tail ++ suffix) with
        | none => none
        | some (rest, remaining) => some (bit :: rest, remaining)) =
          some (bit :: tail, suffix)
      rw [ih]

theorem decodeFrame_frame_append (payload suffix : BitString) :
    decodeFrame (frame payload ++ suffix) = some (payload, suffix) := by
  unfold frame decodeFrame
  rw [append_assoc_constructive]
  change (match decodeLength
      (List.replicate payload.length true ++ false :: (payload ++ suffix)) with
    | none => none
    | some (n, rest) => splitExact n rest) = some (payload, suffix)
  rw [decodeLength_frameHeader]
  change splitExact payload.length (payload ++ suffix) = some (payload, suffix)
  rw [splitExact_append]

/-- Framing followed by decoding is an executable round trip. -/
theorem decodeFrame_frame (payload : BitString) :
    decodeFrame (frame payload) = some (payload, []) := by
  have result := decodeFrame_frame_append payload []
  rw [append_nil_constructive] at result
  exact result

/-- Canonical framing is injective. -/
theorem frame_injective : Function.Injective frame := by
  intro left right h
  have hDecoded : decodeFrame (frame left) = decodeFrame (frame right) :=
    congrArg decodeFrame h
  rw [decodeFrame_frame, decodeFrame_frame] at hDecoded
  exact congrArg Prod.fst (Option.some.inj hDecoded)

/-- No complete canonical frame is a proper prefix of another complete frame. -/
theorem frame_prefix_free {left right : BitString}
    (h : frame left <+: frame right) : left = right := by
  rcases h with ⟨suffix, hFrame⟩
  have hDecoded : decodeFrame (frame left ++ suffix) = decodeFrame (frame right) :=
    congrArg decodeFrame hFrame
  rw [decodeFrame_frame_append, decodeFrame_frame] at hDecoded
  have hPayloads : (left, suffix) = (right, []) := Option.some.inj hDecoded
  exact congrArg Prod.fst hPayloads

/-- Pair encoding followed by whole-string decoding is an executable round
trip. -/
theorem decodePair_pair (left right : BitString) :
    decodePair (pair left right) = some (left, right) := by
  unfold pair decodePair
  rw [decodeFrame_frame_append]
  change (match decodeFrame (frame right) with
    | none => none
    | some (decoded, suffix) =>
        match suffix with
        | [] => some (left, decoded)
        | _ :: _ => none) = some (left, right)
  rw [decodeFrame_frame]

/-- Canonical pair encoding is injective in both components. -/
theorem pair_injective {left₁ right₁ left₂ right₂ : BitString}
    (h : pair left₁ right₁ = pair left₂ right₂) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hDecoded : decodePair (pair left₁ right₁) =
      decodePair (pair left₂ right₂) := congrArg decodePair h
  rw [decodePair_pair, decodePair_pair] at hDecoded
  have hPairs : (left₁, right₁) = (left₂, right₂) := Option.some.inj hDecoded
  exact ⟨congrArg Prod.fst hPairs, congrArg Prod.snd hPairs⟩

/-- An empty string is not a frame. -/
theorem decodeFrame_empty : decodeFrame [] = none := rfl

/-- A unary header with no zero delimiter is malformed. -/
theorem decodeFrame_noDelimiter (n : Nat) :
    decodeFrame (List.replicate n true) = none := by
  unfold decodeFrame
  rw [decodeLength_noDelimiter]

/-- A header declaring one payload bit rejects an absent payload. -/
theorem decodeFrame_shortPayload : decodeFrame [true, false] = none := rfl

/-- The whole-string pair decoder rejects trailing data. -/
theorem decodePair_trailing (left right : BitString) (bit : Bool) :
    decodePair (pair left right ++ [bit]) = none := by
  unfold pair decodePair
  rw [append_assoc_constructive]
  rw [decodeFrame_frame_append]
  change (match decodeFrame (frame right ++ [bit]) with
    | none => none
    | some (decoded, suffix) =>
        match suffix with
        | [] => some (left, decoded)
        | _ :: _ => none) = none
  rw [decodeFrame_frame_append]

theorem size_frame (payload : BitString) :
    size (frame payload) = payload.length + 1 + payload.length := by
  unfold size frame
  rw [length_append_constructive]
  rw [length_replicate_constructive]
  rw [List.length_cons]
  exact Nat.add_comm payload.length (payload.length + 1)

theorem size_pair (left right : BitString) :
    size (pair left right) =
      (left.length + 1 + left.length) + (right.length + 1 + right.length) := by
  unfold pair
  change (frame left ++ frame right).length =
    (left.length + 1 + left.length) + (right.length + 1 + right.length)
  rw [length_append_constructive]
  have leftSize : (frame left).length = left.length + 1 + left.length :=
    size_frame left
  have rightSize : (frame right).length = right.length + 1 + right.length :=
    size_frame right
  rw [leftSize, rightSize]

end BitString

/-- Natural-number polynomial expressions with nonnegative coefficients.  The
syntax is intentionally executable and excludes subtraction, so every
expression is monotone on natural inputs. -/
inductive NatPolynomial where
  | constant (value : Nat)
  | variable
  | add (left right : NatPolynomial)
  | mul (left right : NatPolynomial)
  deriving DecidableEq, Repr

namespace NatPolynomial

/-- Evaluate a polynomial expression at a natural input size. -/
def eval : NatPolynomial → Nat → Nat
  | .constant value, _ => value
  | .variable, input => input
  | .add left right, input => eval left input + eval right input
  | .mul left right, input => eval left input * eval right input

/-- A convenient expression for `coefficient * n + offset`. -/
def linear (coefficient offset : Nat) : NatPolynomial :=
  .add (.mul (.constant coefficient) .variable) (.constant offset)

/-- A convenient quadratic expression `coefficient * n * n + offset`. -/
def quadratic (coefficient offset : Nat) : NatPolynomial :=
  .add (.mul (.mul (.constant coefficient) .variable) .variable)
    (.constant offset)

@[simp] theorem eval_constant (value input : Nat) :
    eval (.constant value) input = value := rfl

@[simp] theorem eval_variable (input : Nat) : eval .variable input = input := rfl

@[simp] theorem eval_add (left right : NatPolynomial) (input : Nat) :
    eval (.add left right) input = eval left input + eval right input := rfl

@[simp] theorem eval_mul (left right : NatPolynomial) (input : Nat) :
    eval (.mul left right) input = eval left input * eval right input := rfl

theorem eval_mono (polynomial : NatPolynomial) {smaller larger : Nat}
    (h : smaller ≤ larger) : eval polynomial smaller ≤ eval polynomial larger := by
  induction polynomial with
  | constant value => exact Nat.le_refl value
  | «variable» => exact h
  | add left right leftIH rightIH =>
      exact Nat.add_le_add leftIH rightIH
  | mul left right leftIH rightIH =>
      exact Nat.mul_le_mul leftIH rightIH

/-- Evaluating at an advertised input bound gives a numeric runtime bound for
every smaller input. -/
theorem eval_le_at_bound (polynomial : NatPolynomial) {input bound : Nat}
    (h : input ≤ bound) : eval polynomial input ≤ eval polynomial bound :=
  eval_mono polynomial h

theorem eval_linear (coefficient offset input : Nat) :
    eval (linear coefficient offset) input = coefficient * input + offset := rfl

theorem eval_quadratic (coefficient offset input : Nat) :
    eval (quadratic coefficient offset) input = coefficient * input * input + offset := rfl

/-- A concrete linear evaluation test for the executable syntax. -/
theorem eval_linear_example : eval (linear 3 2) 4 = 14 := rfl

/-- A concrete quadratic evaluation test for the executable syntax. -/
theorem eval_quadratic_example : eval (quadratic 2 1) 3 = 19 := rfl

end NatPolynomial

end PNP.Concrete
