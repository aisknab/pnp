import PNP.Concrete.NativeNormalization.FrontendBridge
import PNP.Concrete.NativeNormalization.SourceAssemblyBridge
import PNP.Concrete.NativeNormalization.SourceRecoveryBridge
import PNP.Concrete.NativeNormalization.NativeSerializedNormalizer
import PNP.Concrete.NormalizerOriginalPolynomial

namespace PNP.Concrete.NativeNormalization.WholePacketSourceBridge
open PNP.Concrete PNP.Concrete.NormalizerBlocks
open NativeSource NativeOutputPacket

abbrev sourceInput (F : CNFFormula) : BitString :=
  MatchingDriver.encode (NativeTseitin.frontend F).variableCount (NativeTseitin.frontend F).clauses
abbrev cache (F : CNFFormula) := (MeasuredSourceCache.fromSource F).value

theorem decodedPacket_eq (F : CNFFormula) :
    OriginalNormalizer.decodedPacket F =
      (OutputBranches.dispatched (SourceCheck.result (sourceInput F))
        (List.replicate F.variableCount true)).registers.output := by
  simp only [OriginalNormalizer.decodedPacket,OriginalNormalizer.transformed,ClosedFrontendBridge.frontend_value]

private theorem migrated_width_core (r : CutDriver.State) (width : BitString) :
    (SourceAssembly.migrated (OutputBranches.extend r width)).core =
      (SourceAssembly.migrated (SourceAssembly.extended r)).core := rfl

theorem failure_bytes (F : CNFFormula) (failed : Fin (cache F).rows)
    (found : (MeasuredCandidate.firstFailed (MeasuredCache.operations (cache F).data)).value = some failed) :
    (SourceAssembly.failureResult
      (OutputBranches.extend (SourceCheck.result (sourceInput F)) (List.replicate F.variableCount true))).registers.output =
        (NativeSystemCodec.systemCodec (cache F).rows).encode
          (MeasuredAssembly.assemble (MeasuredCache.operations (cache F).data) failed).value := by
  have encoded := SourceAssemblySourceBridge.migrated_encoded
    (NativeTseitin.frontend F) (NativeFrontend.frontend_three F) failed found
  have rows := SourceAssemblySourceBridge.migrated_rows
    (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
  apply SystemRowsSourceBridge.complete_measured_system (cache F).data failed
  · rw [migrated_width_core]
    exact encoded
  · rw [migrated_width_core]
    exact rows

attribute [local irreducible] SourceCheck.result

theorem decodedPacket_model (F : CNFFormula)
    (found : (MeasuredCandidate.firstFailed (MeasuredCache.operations (cache F).data)).value = none) :
    OriginalNormalizer.decodedPacket F =
      encode (.model (MeasuredSourceRecovery.candidate F (cache F)).value) := by
  have output := CheckSourceBridge.result_source (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
  dsimp only [cache,MeasuredSourceCache.fromSource] at found
  rw [found] at output
  rw [decodedPacket_eq,OutputBranches.dispatched_model_output _ _ output,NativeOutputPacket.model_frame]
  have recovered :
      (SourceRecovery.called (OutputBranches.requested (SourceCheck.result (sourceInput F))
        (List.replicate F.variableCount true))).registers.output =
          (MeasuredSourceRecovery.candidate F (cache F)).value :=
    RecoverySourceBridge.requested_call_source F
  rw [recovered]

theorem decodedPacket_system (F : CNFFormula) (failed : Fin (cache F).rows)
    (found : (MeasuredCandidate.firstFailed (MeasuredCache.operations (cache F).data)).value = some failed) :
    OriginalNormalizer.decodedPacket F =
      encode (.system (cache F).rows
        (MeasuredAssembly.assemble (MeasuredCache.operations (cache F).data) failed).value) := by
  have output := CheckSourceBridge.result_source (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)
  dsimp only [cache,MeasuredSourceCache.fromSource] at found
  rw [found] at output
  rw [decodedPacket_eq,OutputBranches.dispatched_system_output _ _ failed.val output,failure_bytes F failed found]
  have rows := (CheckSourceBridge.cache_retained
    (NativeTseitin.frontend F) (NativeFrontend.frontend_three F)).rowsRead
  rw [rows,List.length_replicate]
  simp only [NativeOutputPacket.encode,NativeBitCodec.natural,List.append_assoc,
    List.cons_append,List.nil_append,cache,MeasuredSourceCache.fromSource]

theorem recovered_model (F : CNFFormula)
    (passed : (SourceCheck.result (sourceInput F)).registers.output = TableOwner.answer none) :
    F.Satisfied (MeasuredSourceRecovery.candidate F (cache F)).value := by
  rw [← RecoverySourceBridge.requested_call_source]
  exact RecoverySourceBridge.requested_call_model_from_runtime_success F passed

private theorem fromFrontend_congr (F G H : CNFFormula) (same : G = H)
    (threeG : ThreeCore G) (threeH : ThreeCore H) :
    (MeasuredSharedProducer.fromCache F G threeG (MeasuredSourceCache.build G threeG).value).value =
      (MeasuredSharedProducer.fromCache F H threeH (MeasuredSourceCache.build H threeH).value).value := by
  subst H
  rfl

theorem produce_value (F : CNFFormula) :
    (MeasuredSharedProducer.produce F).value =
      (MeasuredSharedProducer.fromCache F (NativeTseitin.frontend F)
        (NativeFrontend.frontend_three F) (cache F)).value := by
  simpa only [MeasuredSharedProducer.produce,cache,MeasuredSourceCache.fromSource] using
    fromFrontend_congr F (MeasuredRawFrontend.build F).value (NativeTseitin.frontend F)
      (MeasuredRawFrontend.build_value F) (MeasuredSharedProducer.built_three F) (NativeFrontend.frontend_three F)

theorem decodedPacket_source (F : CNFFormula) :
    OriginalNormalizer.decodedPacket F =
      encode (NativeSerializedNormalizer.ofResult (.success (MeasuredSharedProducer.produce F).value)) := by
  rw [produce_value]
  cases found : (MeasuredCandidate.firstFailed (MeasuredCache.operations (cache F).data)).value with
  | none =>
      rw [decodedPacket_model F found]
      simp only [MeasuredSharedProducer.fromCache,MeasuredRun.run,found,
        MeasuredSharedProducer.finish,NativeSerializedNormalizer.ofResult]
      rfl
  | some failed =>
      rw [decodedPacket_system F failed found]
      simp only [MeasuredSharedProducer.fromCache,MeasuredRun.run,found,
        MeasuredSharedProducer.finish,NativeSerializedNormalizer.ofResult]

theorem data_source (input : BitString) :
    OriginalNormalizer.data input = NativeSerializedNormalizer.serialize input := by
  simp only [NativeSerializedNormalizer.serialize,NativeSerializedNormalizer.packet,
    MeasuredSharedNormalizer.convert,MeasuredDecoder.decode_value]
  cases decoded : decodeEncodedCNF input with
  | none =>
      simp only [OriginalNormalizer.data,decoded,NativeSerializedNormalizer.ofResult,NativeOutputPacket.encode]
  | some F =>
      simp only [OriginalNormalizer.data,decoded]
      exact decodedPacket_source F

theorem polynomial_source (input : BitString) :
    OriginalNormalizer.polynomial.output input = NativeSerializedNormalizer.serialize input :=
  (OriginalNormalizer.polynomial_output input).trans (data_source input)
theorem machine_source (input : BitString) :
    machineOutput OriginalNormalizer.rawRefinement.machine
      (OriginalNormalizer.rawRefinement.timeBound.eval (BitString.size input)) input =
        NativeSerializedNormalizer.serialize input :=
  (OriginalNormalizer.machine_output input).trans (data_source input)

end PNP.Concrete.NativeNormalization.WholePacketSourceBridge
