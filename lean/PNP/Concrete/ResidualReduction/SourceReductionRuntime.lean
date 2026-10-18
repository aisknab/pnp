import PNP.Concrete.ResidualReduction.SourceReductionPolynomial
import PNP.Concrete.ResidualReduction.SourceReplayEndpointBudget
import PNP.Concrete.ResidualReduction.NativeSourceReduction

/-! Complete source-contraction phase and physical witness-replay contract.
The actual source bitstring drives normalization and history construction.
Replay reconstructs the exact source certificate in polynomial physical time,
and a terminal model gives a certificate accepted by the actual source checker.
No terminal model is discovered here. A positive-dimensional stopped core
remains unknown, so this is not a total residual solver or a P = NP theorem. -/

namespace PNP.Concrete.ResidualReduction.SourceReductionRuntime
open PNP.Concrete PNP.Concrete.NativeNormalization
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction

private theorem packet_of_decoded (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D)) :
    NativeSerializedNormalizer.packet input = .system c D :=
  Option.some.inj ((SerializedNormalizer.decode_output input).symm.trans decoded)

theorem source_output (input : BitString) :
    SourceReductionPolynomial.output input =
      SourceEncoding.encodeNativePacket (NativeSerializedNormalizer.packet input) :=
  SourceReductionPolynomial.output_eq input

theorem source_halts (input : BitString) :
    boundedDecide SourceReductionPolynomial.rawRefinement.machine
      (SourceReductionPolynomial.rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  SourceReductionPolynomial.halts input

theorem source_output_size (input : BitString) :
    (SourceReductionPolynomial.output input).length ≤ SourceEncoding.sourceOutputPolynomial.eval input.length :=
  SourceReductionPolynomial.encoded_size input

theorem source_system_output (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D)) :
    SourceReductionPolynomial.output input = [true,true] ++ natural (2 * c) ++
      SourceEncoding.dataCodec.encode (SourceEncoding.toData (NativeSource.reduceSystem D)) :=
  SourceReductionPolynomial.system_output input c D (packet_of_decoded input c D decoded)

theorem source_satisfiability (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D)) :
    (∃ z, models (NativeSource.reduceSystem D).core z = true) ↔ CNFSAT input :=
  NativeSource.reduced_source_iff input c D decoded

def replayOutput (input : BitString) : BitString :=
  machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine
    (SourceReplayEndpointPolynomial.rawRefinement.timeBound.eval (BitString.size input)) input

theorem replay_output (input : BitString) :
    replayOutput input = SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) :=
  SourceReplayEndpointPolynomial.machine_output input

theorem replay_halts (input : BitString) :
    boundedDecide SourceReplayEndpointPolynomial.rawRefinement.machine
      (SourceReplayEndpointPolynomial.rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  SourceReplayEndpointPolynomial.rawRefinement.haltsWithin input
    (SourceReplayEndpointPolynomial.polynomial.haltsWithin input)

theorem replay_output_size (input : BitString) : (replayOutput input).length ≤ 2 * input.length + 2 :=
  SourceReplayEndpointPolynomial.machine_output_length input

/-- The data is generated from the actual source system; no history-correctness
certificate, parsed reduction or selected contraction is supplied by the caller. -/
def recoveryRequest (c : Nat) (D : NativeSparseSystem.System c)
    (z : Point (NativeSource.reduceSystem D).dimension) : SourceReplayRequest.Request :=
  SourceReplayEndpointGenerated.recoverRequest (2 * c) (NativeSource.family D) z

theorem recovery_output (c : Nat) (D : NativeSparseSystem.System c)
    (z : Point (NativeSource.reduceSystem D).dimension) :
    replayOutput (SourceReplayRequest.codec.encode (recoveryRequest c D z)) =
      SourceReplayEndpointOutput.codec.encode (some (NativeSource.pointBytes ((NativeSource.reduceSystem D).lift z))) :=
  SourceReplayEndpointGenerated.machine_recover_generated (2 * c) (NativeSource.family D) z

theorem recover_certificate (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D))
    (z : Point (NativeSource.reduceSystem D).dimension)
    (model : models (NativeSource.reduceSystem D).core z = true) :
    ∃ certificate,
      SourceReplayEndpointOutput.codec.decode
        (replayOutput (SourceReplayRequest.codec.encode (recoveryRequest c D z))) = some (some certificate) ∧
      certificate.length = 2 * c ∧
      NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input) certificate = true := by
  have checked := NativeSource.lifted_certificate input c D decoded z model
  refine ⟨NativeSource.pointBytes ((NativeSource.reduceSystem D).lift z),?_,checked⟩
  rw [recovery_output,NativeNormalization.NativeBitCodec.decode_encode]

/-- This is replay time in the original source length, not merely in the
already-expanded history size. The terminal-model premise is not discharged. -/
theorem recover_certificate_runtime (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D))
    (z : Point (NativeSource.reduceSystem D).dimension)
    (model : models (NativeSource.reduceSystem D).core z = true) :
    ∃ steps ≤ SourceReplayEndpointBudget.nativeRuntimePolynomial.eval input.length,
      ∃ certificate,
        boundedDecide SourceReplayEndpointPolynomial.rawRefinement.machine steps
          (SourceReplayRequest.codec.encode (recoveryRequest c D z)) ≠ .timeout ∧
        SourceReplayEndpointOutput.codec.decode
          (machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine steps
            (SourceReplayRequest.codec.encode (recoveryRequest c D z))) = some (some certificate) ∧
        certificate.length = 2 * c ∧
        NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input) certificate = true := by
  obtain ⟨steps,bound,halts,output⟩ := SourceReplayEndpointBudget.native_recover_run input c D
    (packet_of_decoded input c D decoded) z
  have checked := NativeSource.lifted_certificate input c D decoded z model
  refine ⟨steps,bound,NativeSource.pointBytes ((NativeSource.reduceSystem D).lift z),halts,?_,checked⟩
  rw [recoveryRequest,output,NativeNormalization.NativeBitCodec.decode_encode]
  rfl

theorem unresolved_remains_unknown (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D))
    (remaining : (NativeSource.reduceSystem D).dimension ≠ 0) :
    NativeSource.sourceVerdict input = none :=
  NativeSource.sourceVerdict_unresolved input c D decoded remaining

end PNP.Concrete.ResidualReduction.SourceReductionRuntime
