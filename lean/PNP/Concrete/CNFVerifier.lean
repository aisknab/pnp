/-
Copyright (c) 2026 PNP Labs.

The generic final bridge from a concrete raw machine to the bounded-
certificate CNF verifier.  The machine is run directly on
`BitString.pair input certificate`; this file does not use a preprocessor,
an oracle, or a function-valued executable field.
-/

import PNP.Concrete.CNF

namespace PNP.Concrete

private theorem add_one_same_normalize (value : Nat) :
    value + 1 + value = value + value + 1 := by
  rw [Nat.add_assoc]
  rw [Nat.add_comm 1 value]
  rw [← Nat.add_assoc]

private theorem merge_unit_offsets (left right : Nat) :
    (left + 1) + (right + 1) = left + right + 2 := by
  rw [Nat.add_assoc]
  rw [← Nat.add_assoc 1 right 1]
  rw [Nat.add_comm 1 right]
  rw [Nat.add_assoc right 1 1]
  rw [← Nat.add_assoc left right 2]

private theorem pair_size_arithmetic (left right : Nat) :
    (left + 1 + left) + (right + 1 + right) =
      2 * left + 2 * right + 2 := by
  rw [add_one_same_normalize, add_one_same_normalize]
  rw [Nat.two_mul, Nat.two_mul]
  exact merge_unit_offsets (left + left) (right + right)

private theorem shift_constant_blocks (left right : Nat) :
    (left + 2) + (right + 4) + 2 = (left + right + 2) + 6 := by
  have moveTwo : 2 + (right + 4) = right + (2 + 4) := by
    have first : 2 + (right + 4) = (2 + right) + 4 :=
      (Nat.add_assoc 2 right 4).symm
    have second : (2 + right) + 4 = (right + 2) + 4 :=
      congrArg (fun value => value + 4) (Nat.add_comm 2 right)
    have third : (right + 2) + 4 = right + (2 + 4) :=
      Nat.add_assoc right 2 4
    exact first.trans (second.trans third)
  calc
    (left + 2) + (right + 4) + 2 =
        (left + (2 + (right + 4))) + 2 :=
      congrArg (fun value => value + 2) (Nat.add_assoc left 2 (right + 4))
    _ = (left + (right + (2 + 4))) + 2 :=
      congrArg (fun value => (left + value) + 2) moveTwo
    _ = ((left + right) + 6) + 2 :=
      congrArg (fun value => value + 2) (Nat.add_assoc left right 6).symm
    _ = ((left + right) + 2) + 6 := Nat.add_right_comm (left + right) 6 2

private theorem six_bound_arithmetic (value : Nat) :
    2 * value + 2 * (2 * value + 2) + 2 = 6 * value + 6 := by
  induction value with
  | zero => rfl
  | succ value ih =>
      change (2 * value + 2) + 2 * ((2 * value + 2) + 2) + 2 =
        (6 * value + 6) + 6
      calc
        (2 * value + 2) + 2 * ((2 * value + 2) + 2) + 2 =
            (2 * value + 2) +
              (2 * (2 * value + 2) + 2 * 2) + 2 :=
          congrArg (fun middle => (2 * value + 2) + middle + 2)
            (Nat.mul_add 2 (2 * value + 2) 2)
        _ = (2 * value + 2 * (2 * value + 2) + 2) + 6 :=
          shift_constant_blocks (2 * value) (2 * (2 * value + 2))
        _ = (6 * value + 6) + 6 := congrArg (fun result => result + 6) ih

namespace BitString

/-- Closed arithmetic form of the canonical pair length. -/
theorem size_pair_normalized (left right : BitString) :
    size (pair left right) = 2 * size left + 2 * size right + 2 := by
  rw [size_pair]
  exact pair_size_arithmetic left.length right.length

end BitString

/-- Polynomial upper bound for a paired formula/certificate input once the
certificate obeys `cnfCertificateBound`. -/
def cnfPairInputBound : NatPolynomial := NatPolynomial.linear 6 6

theorem cnfPairInputBound_eval (inputSize : Nat) :
    cnfPairInputBound.eval inputSize = 6 * inputSize + 6 := rfl

/-- Explicit arithmetic form of the paired-input bound. -/
theorem size_pair_le_six_mul_add_six (input certificate : BitString)
    (certificateSize :
      BitString.size certificate ≤
        cnfCertificateBound.eval (BitString.size input)) :
    BitString.size (BitString.pair input certificate) ≤
      6 * BitString.size input + 6 := by
  change BitString.size certificate ≤ 2 * BitString.size input + 2 at certificateSize
  rw [BitString.size_pair_normalized]
  have doubled : 2 * BitString.size certificate ≤
      2 * (2 * BitString.size input + 2) :=
    Nat.mul_le_mul_left 2 certificateSize
  have summed :
      2 * BitString.size input + 2 * BitString.size certificate + 2 ≤
        2 * BitString.size input + 2 * (2 * BitString.size input + 2) + 2 :=
    Nat.add_le_add_right
      (Nat.add_le_add_left doubled (2 * BitString.size input)) 2
  exact Nat.le_trans summed (Nat.le_of_eq
    (six_bound_arithmetic (BitString.size input)))

/-- Polynomial-expression form of `size_pair_le_six_mul_add_six`. -/
theorem size_pair_le_cnfCertificateBound (input certificate : BitString)
    (certificateSize :
      BitString.size certificate ≤
        cnfCertificateBound.eval (BitString.size input)) :
    BitString.size (BitString.pair input certificate) ≤
      cnfPairInputBound.eval (BitString.size input) :=
  size_pair_le_six_mul_add_six input certificate certificateSize

/-- Translate a polynomial charged on the paired raw input to a polynomial
charged only on the formula input size. -/
def cnfVerifierRuntimeBound (rawBound : NatPolynomial) : NatPolynomial :=
  NatPolynomial.substitute rawBound cnfPairInputBound

/-- Build a concrete CNF verifier from one finite raw machine.

`rawHalts` is required on every certificate inside the advertised bound.
`rawAccepts` is deliberately required on every pair, including malformed and
oversized certificates.  Both hypotheses concern `boundedDecide` on the
literal `BitString.pair`, whose definition starts at
`startConfig rawMachine (BitString.pair input certificate)` and therefore at
`Tape.ofInput` of that exact string. -/
def cnfVerifierOfRawMachine
    (rawMachine : Machine)
    (rawBound : NatPolynomial)
    (rawHalts : ∀ input certificate,
      BitString.size certificate ≤
          cnfCertificateBound.eval (BitString.size input) →
        boundedDecide rawMachine
            (rawBound.eval
              (BitString.size (BitString.pair input certificate)))
            (BitString.pair input certificate) ≠ .timeout)
    (rawAccepts : ∀ input certificate,
      boundedDecide rawMachine
          (rawBound.eval (BitString.size (BitString.pair input certificate)))
          (BitString.pair input certificate) = .accept ↔
        checkEncodedCertificate input certificate = true) :
    PolynomialTimeVerifier CNFSAT :=
  { program :=
      { inputMode := .paired
        decision := .machine rawMachine rawBound }
    certificateBound := cnfCertificateBound
    runtimeBound := cnfVerifierRuntimeBound rawBound
    haltsWithin := by
      intro input certificate certificateSize
      exact rawHalts input certificate certificateSize
    runtime_le := by
      intro input certificate certificateSize
      change rawBound.eval
          (BitString.size (BitString.pair input certificate)) ≤
        (cnfVerifierRuntimeBound rawBound).eval (BitString.size input)
      unfold cnfVerifierRuntimeBound
      rw [NatPolynomial.eval_substitute]
      exact NatPolynomial.eval_mono rawBound
        (size_pair_le_cnfCertificateBound input certificate certificateSize)
    accepts_iff := by
      intro input
      constructor
      · intro satisfiable
        have boundedCertificate :=
          (cnfSAT_iff_bounded_encoded_certificate input).mp satisfiable
        rcases boundedCertificate with ⟨certificate, certificateSize, checked⟩
        refine ⟨certificate, certificateSize, ?_⟩
        change boundedDecide rawMachine
            (rawBound.eval (BitString.size (BitString.pair input certificate)))
            (BitString.pair input certificate) = .accept
        exact (rawAccepts input certificate).mpr checked
      · intro acceptedCertificate
        rcases acceptedCertificate with ⟨certificate, certificateSize, accepted⟩
        have acceptedRaw :
            boundedDecide rawMachine
                (rawBound.eval
                  (BitString.size (BitString.pair input certificate)))
                (BitString.pair input certificate) = .accept := accepted
        have checked := (rawAccepts input certificate).mp acceptedRaw
        exact (cnfSAT_iff_bounded_encoded_certificate input).mpr
          ⟨certificate, certificateSize, checked⟩ }

/-- The same direct raw-machine hypotheses establish concrete NP membership. -/
theorem cnf_inNP_of_rawMachine
    (rawMachine : Machine)
    (rawBound : NatPolynomial)
    (rawHalts : ∀ input certificate,
      BitString.size certificate ≤
          cnfCertificateBound.eval (BitString.size input) →
        boundedDecide rawMachine
            (rawBound.eval
              (BitString.size (BitString.pair input certificate)))
            (BitString.pair input certificate) ≠ .timeout)
    (rawAccepts : ∀ input certificate,
      boundedDecide rawMachine
          (rawBound.eval (BitString.size (BitString.pair input certificate)))
          (BitString.pair input certificate) = .accept ↔
        checkEncodedCertificate input certificate = true) :
    InNP CNFSAT :=
  ⟨cnfVerifierOfRawMachine rawMachine rawBound rawHalts rawAccepts⟩

end PNP.Concrete
