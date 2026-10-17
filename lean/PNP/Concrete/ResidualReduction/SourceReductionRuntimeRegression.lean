import PNP.Concrete.ResidualReduction.SourceReductionRuntime
import Lean

/-! Independent public type contracts for the whole source-construction/replay
boundary. The prior component execution suites are not imported or rerun.
The checker assertion is about the actual reconstructed machine output.
The unresolved-core case remains unknown, not a guessed yes/no answer. -/

namespace PNP.Concrete.ResidualReduction.SourceReductionRuntimeRegression
open PNP.Concrete PNP.Concrete.NativeNormalization
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceReductionRuntime (replayOutput recoveryRequest)

example (input : BitString) : SourceReductionPolynomial.output input =
    SourceEncoding.encodeNativePacket (NativeSerializedNormalizer.packet input) :=
  SourceReductionRuntime.source_output input
example (input : BitString) :
    boundedDecide SourceReductionPolynomial.rawRefinement.machine
      (SourceReductionPolynomial.rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  SourceReductionRuntime.source_halts input
example (input : BitString) :
    (SourceReductionPolynomial.output input).length ≤ SourceEncoding.sourceOutputPolynomial.eval input.length :=
  SourceReductionRuntime.source_output_size input
example (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D)) :
    SourceReductionPolynomial.output input = [true,true] ++ natural (2 * c) ++
      SourceEncoding.dataCodec.encode (SourceEncoding.toData (NativeSource.reduceSystem D)) :=
  SourceReductionRuntime.source_system_output input c D decoded
example (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D)) :
    (∃ z, models (NativeSource.reduceSystem D).core z = true) ↔ CNFSAT input :=
  SourceReductionRuntime.source_satisfiability input c D decoded
example (input : BitString) :
    replayOutput input = SourceReplayEndpointOutput.codec.encode (SourceReplayRequest.answer input) :=
  SourceReductionRuntime.replay_output input
example (input : BitString) :
    boundedDecide SourceReplayEndpointPolynomial.rawRefinement.machine
      (SourceReplayEndpointPolynomial.rawRefinement.timeBound.eval (BitString.size input)) input ≠ .timeout :=
  SourceReductionRuntime.replay_halts input
example (input : BitString) : (replayOutput input).length ≤ 2 * input.length + 2 :=
  SourceReductionRuntime.replay_output_size input
example (c : Nat) (D : NativeSparseSystem.System c) (z : Point (NativeSource.reduceSystem D).dimension) :
    replayOutput (SourceReplayRequest.codec.encode (recoveryRequest c D z)) =
      SourceReplayEndpointOutput.codec.encode (some (NativeSource.pointBytes ((NativeSource.reduceSystem D).lift z))) :=
  SourceReductionRuntime.recovery_output c D z
example (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D))
    (z : Point (NativeSource.reduceSystem D).dimension) (model : models (NativeSource.reduceSystem D).core z = true) :
    ∃ certificate,
      SourceReplayEndpointOutput.codec.decode
        (replayOutput (SourceReplayRequest.codec.encode (recoveryRequest c D z))) = some (some certificate) ∧
      certificate.length = 2 * c ∧
      NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input) certificate = true :=
  SourceReductionRuntime.recover_certificate input c D decoded z model
example (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D))
    (z : Point (NativeSource.reduceSystem D).dimension) (model : models (NativeSource.reduceSystem D).core z = true) :
    ∃ steps ≤ SourceReplayEndpointBudget.nativeRuntimePolynomial.eval input.length,
      ∃ certificate,
        boundedDecide SourceReplayEndpointPolynomial.rawRefinement.machine steps
          (SourceReplayRequest.codec.encode (recoveryRequest c D z)) ≠ .timeout ∧
        SourceReplayEndpointOutput.codec.decode
          (machineOutput SourceReplayEndpointPolynomial.rawRefinement.machine steps
            (SourceReplayRequest.codec.encode (recoveryRequest c D z))) = some (some certificate) ∧
        certificate.length = 2 * c ∧
        NativeSerializedNormalizer.checkEncoded (SerializedNormalizer.output input) certificate = true :=
  SourceReductionRuntime.recover_certificate_runtime input c D decoded z model
example (input : BitString) (c : Nat) (D : NativeSparseSystem.System c)
    (decoded : NativeOutputPacket.codec.decode (SerializedNormalizer.output input) = some (.system c D))
    (remaining : (NativeSource.reduceSystem D).dimension ≠ 0) :
    NativeSource.sourceVerdict input = none :=
  SourceReductionRuntime.unresolved_remains_unknown input c D decoded remaining

run_cmd do
  let names := [
    ``SourceReductionRuntime.source_output,
    ``SourceReductionRuntime.source_halts,
    ``SourceReductionRuntime.source_output_size,
    ``SourceReductionRuntime.source_system_output,
    ``SourceReductionRuntime.source_satisfiability,
    ``SourceReductionRuntime.replay_output,
    ``SourceReductionRuntime.replay_halts,
    ``SourceReductionRuntime.replay_output_size,
    ``SourceReductionRuntime.recovery_output,
    ``SourceReductionRuntime.recover_certificate,
    ``SourceReductionRuntime.recover_certificate_runtime,
    ``SourceReductionRuntime.unresolved_remains_unknown]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"SOURCE_REDUCTION_RUNTIME_AXIOMS_GREEN: {names.length} declarations"

run_cmd Lean.logInfo "SOURCE_REDUCTION_RUNTIME_CONTRACT_GREEN: 12 general kernel contracts; actual source checker and original-input replay runtime; unknown preserved"

end PNP.Concrete.ResidualReduction.SourceReductionRuntimeRegression
