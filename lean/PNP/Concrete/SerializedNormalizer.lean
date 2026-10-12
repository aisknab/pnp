/-
Copyright (c) 2026 PNP Labs.

Complete source-derived normalization, including literal-machine execution and
the entire serialized output. A model packet contains a checked source model;
a system packet retains the residual constraints and is not a refutation.
No general residual solver or deterministic SAT decision procedure is supplied.
-/
import PNP.Concrete.NativeNormalization.SerializedMachineBridge

namespace PNP.Concrete.SerializedNormalizer

open NativeNormalization

/-- The complete frontend, matching, construction, recovery and serialization program. -/
abbrev polynomial : PolynomialTimeFunction :=
  NormalizerBlocks.OriginalNormalizer.polynomial

/-- A literal finite-machine implementation, not only an abstract function program. -/
abbrev rawRefinement : FunctionProgram.RawRefinement polynomial.program :=
  NormalizerBlocks.OriginalNormalizer.rawRefinement

/-- Run that machine for its proved encoded-input polynomial bound. -/
def output (input : BitString) : BitString :=
  machineOutput rawRefinement.machine
    (rawRefinement.timeBound.eval (BitString.size input)) input

theorem output_eq (input : BitString) :
    output input = NativeSerializedNormalizer.serialize input :=
  WholePacketSourceBridge.machine_source input

theorem halts (input : BitString) :
    boundedDecide rawRefinement.machine
      (rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  NormalizerBlocks.OriginalNormalizer.machine_halts input

theorem output_size (input : BitString) :
    BitString.size (output input) ≤ polynomial.outputSizeBound.eval (BitString.size input) :=
  NormalizerBlocks.OriginalNormalizer.machine_output_size input

/-- A separate sparse-output bound is proved for the actual emitted bytes. -/
theorem sparse_output_size (input : BitString) :
    (output input).length ≤ NativeSerializedNormalizer.outputPolynomial.eval input.length := by
  rw [output_eq]
  exact NativeSerializedNormalizer.serialize_length input

theorem decode_output (input : BitString) :
    NativeOutputPacket.codec.decode (output input) =
      some (NativeSerializedNormalizer.packet input) := by
  rw [output_eq]
  exact NativeSerializedNormalizer.decode_serialize input

/-- Exact semantic preservation for every bitstring, including malformed words. -/
theorem satisfiability_iff (input : BitString) :
    (∃ certificate, NativeSerializedNormalizer.checkEncoded (output input) certificate = true) ↔
      CNFSAT input := by
  rw [output_eq]
  exact NativeSerializedNormalizer.encoded_language_iff input

/-- A short witness exists for satisfiable inputs; this does not find that witness. -/
theorem certificate_bound (input : BitString) (satisfiable : CNFSAT input) :
    ∃ certificate, certificate.length ≤ 30 * input.length + 12 ∧
      NativeSerializedNormalizer.checkEncoded (output input) certificate = true := by
  rw [output_eq]
  exact NativeSerializedNormalizer.bounded_certificate input satisfiable

theorem malformed_output (input : BitString) (malformed : decodeEncodedCNF input = none) :
    output input = [false, false, false] :=
  NormalizerBlocks.OriginalNormalizer.machine_malformed input malformed

/-- A computed residual packet carries the full system, not an unsatisfiable verdict. -/
theorem residual_system_iff (input : BitString) (rows : Nat) (D : NativeSparseSystem.System rows)
    (decoded : NativeOutputPacket.codec.decode (output input) = some (.system rows D)) :
    (∃ certificate : BitString, certificate.length = 2 * rows ∧
      D.Satisfied (MeasuredBits.rowValues rows certificate)) ↔ CNFSAT input := by
  have packet : NativeSerializedNormalizer.packet input = .system rows D :=
    Option.some.inj ((decode_output input).symm.trans decoded)
  have semantics := NativeSerializedNormalizer.packet_check_iff input
  rw [packet] at semantics
  simpa only [NativeSerializedNormalizer.check_system_iff] using semantics

/-- Every emitted model is an assignment satisfying the original decoded formula. -/
theorem model_sound (input assignment : BitString)
    (decoded : NativeOutputPacket.codec.decode (output input) = some (.model assignment)) :
    ∃ F, decodeEncodedCNF input = some F ∧ F.Satisfied assignment := by
  have packet : NativeSerializedNormalizer.packet input = .model assignment :=
    Option.some.inj ((decode_output input).symm.trans decoded)
  have correct := MeasuredSharedNormalizer.convert_correct input
  unfold NativeSerializedNormalizer.packet at packet
  cases result : (MeasuredSharedNormalizer.convert input).value with
  | malformed =>
      rw [result] at packet
      cases packet
  | success produced =>
      rw [result] at packet correct
      cases produced with
      | model a =>
          change NativeOutputPacket.Packet.model a = .model assignment at packet
          cases packet
          exact correct
      | system c D liftModel =>
          cases packet

/-- The encoded target is a residual witness language, not a decided language. -/
def language : Language :=
  fun bytes => ∃ certificate, NativeSerializedNormalizer.checkEncoded bytes certificate = true

/-- A concrete polynomial many-one reduction to the complete serialized language. -/
def reduction : PolynomialReduction CNFSAT language :=
  { function := polynomial
    correctness := by
      intro input
      change CNFSAT input ↔
        ∃ certificate, NativeSerializedNormalizer.checkEncoded (polynomial.output input) certificate = true
      rw [WholePacketSourceBridge.polynomial_source]
      exact (NativeSerializedNormalizer.encoded_language_iff input).symm }

theorem reduction_output (input : BitString) :
    reduction.function.output input = output input := by
  rw [output_eq]
  exact WholePacketSourceBridge.polynomial_source input

theorem reduction_correct (input : BitString) :
    CNFSAT input ↔ language (output input) :=
  (satisfiability_iff input).symm

end PNP.Concrete.SerializedNormalizer
