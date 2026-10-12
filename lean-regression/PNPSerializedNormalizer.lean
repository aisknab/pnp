import PNP

namespace PNP.Concrete.SerializedNormalizerRegression

open NativeNormalization SerializedNormalizer

-- These contracts are uniform in the original encoded input, not fixed instances.
example (input : BitString) :
    output input = NativeSerializedNormalizer.serialize input := output_eq input

example : ∃ runtime : NatPolynomial, ∀ input : BitString,
    boundedDecide rawRefinement.machine (runtime.eval (BitString.size input)) input ≠ .timeout ∧
      machineOutput rawRefinement.machine (runtime.eval (BitString.size input)) input =
        NativeSerializedNormalizer.serialize input :=
  ⟨rawRefinement.timeBound, fun input => ⟨halts input, output_eq input⟩⟩

example (input : BitString) :
    BitString.size (output input) ≤ polynomial.outputSizeBound.eval (BitString.size input) :=
  output_size input

example (input : BitString) :
    (output input).length ≤ NativeSerializedNormalizer.outputPolynomial.eval input.length :=
  sparse_output_size input

example (input : BitString) :
    NativeOutputPacket.codec.decode (output input) =
      some (NativeSerializedNormalizer.packet input) := decode_output input

example (input : BitString) :
    (∃ certificate, NativeSerializedNormalizer.checkEncoded (output input) certificate = true) ↔
      CNFSAT input := satisfiability_iff input

example (input : BitString) (satisfiable : CNFSAT input) :
    ∃ certificate, certificate.length ≤ 30 * input.length + 12 ∧
      NativeSerializedNormalizer.checkEncoded (output input) certificate = true :=
  certificate_bound input satisfiable

example (input : BitString) (malformed : decodeEncodedCNF input = none) :
    output input = [false, false, false] := malformed_output input malformed

example (input : BitString) (rows : Nat) (D : NativeSparseSystem.System rows)
    (decoded : NativeOutputPacket.codec.decode (output input) = some (.system rows D)) :
    (∃ certificate : BitString, certificate.length = 2 * rows ∧
      D.Satisfied (MeasuredBits.rowValues rows certificate)) ↔ CNFSAT input :=
  residual_system_iff input rows D decoded

example (input assignment : BitString)
    (decoded : NativeOutputPacket.codec.decode (output input) = some (.model assignment)) :
    ∃ F, decodeEncodedCNF input = some F ∧ F.Satisfied assignment :=
  model_sound input assignment decoded

example (input : BitString) : reduction.function.output input = output input :=
  reduction_output input

example (input : BitString) : CNFSAT input ↔ language (reduction.function.output input) :=
  reduction.correctness input

-- These small kernel-checked guards test encodings, not progress towards solving SAT.
theorem malformed_empty : output [] = [false, false, false] :=
  malformed_output [] rfl

theorem empty_output_is_not_a_packet : NativeOutputPacket.codec.decode [] = none := rfl

theorem malformed_packet_rejects (certificate : BitString) :
    NativeSerializedNormalizer.checkEncoded [false, false, false] certificate = false := rfl

theorem model_framing_roundtrip (assignment : BitString) :
    NativeOutputPacket.codec.decode ([false, false, true] ++ BitString.frame assignment) =
      some (.model assignment) := by
  rw [← NativeOutputPacket.model_frame]
  exact NativeOutputPacket.roundtrip _

theorem trailing_packet_rejected (packet : NativeOutputPacket.Packet) (bit : Bool) :
    NativeOutputPacket.codec.decode (NativeOutputPacket.encode packet ++ [bit]) = none :=
  NativeOutputPacket.reject_trailing packet [bit] (by intro impossible; cases impossible)

private def emptySystem : NativeSparseSystem.System 0 := { b := [], a := [], e := [] }

theorem empty_residual_has_no_certificate :
    NativeSerializedNormalizer.checkEncoded (NativeOutputPacket.encode (.system 0 emptySystem)) [] =
      false := by decide

end PNP.Concrete.SerializedNormalizerRegression

#print axioms PNP.Concrete.SerializedNormalizerRegression.malformed_empty
#print axioms PNP.Concrete.SerializedNormalizerRegression.empty_output_is_not_a_packet
#print axioms PNP.Concrete.SerializedNormalizerRegression.malformed_packet_rejects
#print axioms PNP.Concrete.SerializedNormalizerRegression.model_framing_roundtrip
#print axioms PNP.Concrete.SerializedNormalizerRegression.trailing_packet_rejected
#print axioms PNP.Concrete.SerializedNormalizerRegression.empty_residual_has_no_certificate

#eval IO.println "serialized-normalizer-regressions-complete: 12 general type contracts; 6 kernel guards"
