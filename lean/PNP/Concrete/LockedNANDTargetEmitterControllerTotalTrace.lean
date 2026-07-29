/-
Copyright (c) 2026 PNP Labs.

Closed all-input traces for the fixed grammar-only locked-NAND target emitter.

Malformed source words take the scanner node's literal reject bridge and
leave empty output.  Decoded words are joined to the complete controller
trace in the success section below.  The raw decoder is used only to select
and verify the fixed machine's branch; it is not part of the executable
machine.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerPolynomialBound

namespace PNP.Concrete.LockedNAND.TargetEmitterControllerTotalTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open TargetEmitterController

private theorem scannerNode_member :
    scannerNode ∈ graph.nodes := by
  change scannerNode ∈ TargetEmitterController.nodes
  apply controlNode_member_nodes scannerNode
  exact List.Mem.head _

/-! ### Decoder-failure branch -/

/-- Every grammar-decoder failure takes the scanner node's already
materialized reject bridge. -/
theorem malformed_path
    (bits : BitString)
    (malformed : decodeCircuit bits = none) :
    ∃ steps finalTape,
      AcceptPath graph (.node scannerRef) .reject steps
          (rawInputWorkTape bits) finalTape ∧
      (encodeWorkTape finalTape).outputBits = [] := by
  rcases
      TargetEmitterGrammarScanner.malformed_exact bits malformed with
    ⟨localSteps, localFinal, localRun, _halted,
      finalState, outputEmpty⟩
  rcases localFinal with ⟨localFinalState, localFinalTape⟩
  change
    localFinalState =
      TargetEmitterGrammarScanner.machine.rejectState at finalState
  subst localFinalState
  have localReject :
      LocalRejectRun scannerNode localSteps
        (rawInputWorkTape bits) localFinalTape := by
    unfold LocalRejectRun
    simpa [scannerNode, controlNode, workStartConfiguration] using localRun
  have tail :
      AcceptPath graph .reject .reject 0
        localFinalTape localFinalTape :=
    .terminal .reject localFinalTape
  have path :=
    AcceptPath.stepReject scannerNode .reject
      localSteps 0 (rawInputWorkTape bits)
      localFinalTape localFinalTape
      scannerNode_member localReject tail
  refine ⟨localSteps + 1, localFinalTape, ?_, outputEmpty⟩
  simpa [scannerNode, scannerRef, controlNode, controlRef,
    Node.reference] using path

/-- Graph-machine execution of the fail-closed branch. -/
theorem malformed_exact
    (bits : BitString)
    (malformed : decodeCircuit bits = none) :
    ∃ steps final,
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = machine.rejectState ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  rcases malformed_path bits malformed with
    ⟨steps, finalTape, path, outputEmpty⟩
  let final : WorkConfiguration :=
    { state := machine.rejectState, tape := finalTape }
  have exactRun :=
    runEntryToReject graph steps
      (rawInputWorkTape bits) finalTape graph_wellFormed path
  refine ⟨steps, final, ?_, ?_, ?_, outputEmpty⟩
  · simpa [TargetEmitterController.machine, final,
      workStartConfiguration] using exactRun
  · exact reject_halted finalTape
  · rfl

/-! ### Grammar-success branch -/

/-- Every grammar-decodable source follows the scanner/ledger prefix and the
complete physical controller to global acceptance.  The reached output is
the exact direct raw target, including for decoded circuits whose intrinsic
references are out of range. -/
theorem decoded_path
    (bits : BitString) (raw : RawCircuit)
    (decoded : decodeCircuit bits = some raw) :
    ∃ steps finalTape,
      AcceptPath graph (.node scannerRef) .accept steps
          (rawInputWorkTape bits) finalTape ∧
      (encodeWorkTape finalTape).outputBits =
        RawBuilder.targetBytes bits := by
  rcases
      TargetEmitterControllerCompletionTrace.controller_complete_path_output
        raw with
    ⟨gateListSteps, normalizationSteps, prefixSteps, outputSteps,
      finalTape, controllerPath, _finalRepresents, outputEq⟩
  let scannerLedgerSteps :=
    TargetEmitterGrammarScanner.canonicalSteps raw + 1 +
      (TargetEmitterLedger.workSteps raw + 1)
  let controllerSteps :=
    gateListSteps + normalizationSteps + prefixSteps + outputSteps
  let steps := scannerLedgerSteps + controllerSteps
  have complete :
      AcceptPath graph (.node scannerRef) .accept steps
        (rawInputWorkTape (encodeCircuit raw)) finalTape := by
    exact
      AcceptPath.trans graph (.node scannerRef)
        (.node stackInitializeRef) .accept
        scannerLedgerSteps controllerSteps
        (rawInputWorkTape (encodeCircuit raw))
        (TargetEmitterLedger.finalConfiguration raw).tape
        finalTape
        (by
          simpa [scannerLedgerSteps] using
            TargetEmitterControllerTrace.scanner_ledger_path raw)
        (by simpa [controllerSteps] using controllerPath)
  have sourceCanonical :
      encodeCircuit raw = bits :=
    PNP.Concrete.LockedNAND.encodeCircuit_eq_of_decodeCircuit_eq_some
      bits raw decoded
  refine ⟨steps, finalTape, ?_, ?_⟩
  · simpa [sourceCanonical] using complete
  · calc
      (encodeWorkTape finalTape).outputBits =
          encodeTokens
            (TargetEmitterSemanticCompletion.completeRuntime
              raw).targetTokens := outputEq
      _ =
          encodeTokens
            (encodeLockedInstanceTokens
              (RawBuilder.rawLockedInstance raw)) :=
        congrArg encodeTokens
          (TargetEmitterSemanticCompletion.completeRuntime_targetTokens raw)
      _ = RawBuilder.targetBytes bits := by
        rw [RawBuilder.targetBytes_of_decoded bits raw decoded]
        rfl

/-- Exact graph-machine execution of the grammar-success branch. -/
theorem decoded_exact
    (bits : BitString) (raw : RawCircuit)
    (decoded : decodeCircuit bits = some raw) :
    ∃ steps final,
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = machine.acceptState ∧
      (encodeWorkTape final.tape).outputBits =
        RawBuilder.targetBytes bits := by
  rcases decoded_path bits raw decoded with
    ⟨steps, finalTape, path, outputEq⟩
  let final : WorkConfiguration :=
    { state := machine.acceptState, tape := finalTape }
  have exactRun :=
    runEntryToAccept graph steps
      (rawInputWorkTape bits) finalTape graph_wellFormed path
  refine ⟨steps, final, ?_, ?_, ?_, outputEq⟩
  · simpa [TargetEmitterController.machine, final,
      workStartConfiguration] using exactRun
  · exact accept_halted finalTape
  · rfl

/-! ### Closed all-input polynomial accounting -/

/-- Decoder failure, its graph reject bridge, and the empty output all fit the
same closed all-input work polynomial used by the successful branch. -/
theorem malformed_bounded_exact
    (bits : BitString)
    (malformed : decodeCircuit bits = none) :
    ∃ steps final,
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = machine.rejectState ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  rcases
      TargetEmitterGrammarScanner.malformed_bounded_exact bits malformed with
    ⟨localSteps, localFinal, localBound, localRun, localHalted,
      localRejected, outputEmpty⟩
  rcases localFinal with ⟨localFinalState, localFinalTape⟩
  change
    localFinalState =
      TargetEmitterGrammarScanner.machine.rejectState at localRejected
  subst localFinalState
  have localReject :
      LocalRejectRun scannerNode localSteps
        (rawInputWorkTape bits) localFinalTape := by
    unfold LocalRejectRun
    simpa [scannerNode, controlNode, workStartConfiguration] using localRun
  have tail :
      AcceptPath graph .reject .reject 0
        localFinalTape localFinalTape :=
    .terminal .reject localFinalTape
  have path :=
    AcceptPath.stepReject scannerNode .reject
      localSteps 0 (rawInputWorkTape bits)
      localFinalTape localFinalTape
      scannerNode_member localReject tail
  let steps := localSteps + 1
  let final : WorkConfiguration :=
    { state := machine.rejectState, tape := localFinalTape }
  have exactRun :=
    runEntryToReject graph steps
      (rawInputWorkTape bits) localFinalTape graph_wellFormed
      (by
        simpa [steps, scannerNode, scannerRef, controlNode, controlRef,
          Node.reference, TargetEmitterController.graph] using path)
  have grammarPhase :
      TargetEmitterGrammarScanner.grammarWorkBound bits.length ≤
        TargetEmitterControllerPolynomialBound.phaseUnit bits.length :=
    TargetEmitterControllerPolynomialBound.grammarWorkBound_le_phaseUnit _
  have localPhase := Nat.le_trans localBound grammarPhase
  have phasePositive :=
    TargetEmitterControllerPolynomialBound.one_le_phaseUnit bits.length
  have shiftedPositive :
      1 ≤
        TargetEmitterControllerPolynomialBound.shiftedSize bits.length := by
    unfold TargetEmitterControllerPolynomialBound.shiftedSize
    omega
  have phaseLift :
      TargetEmitterControllerPolynomialBound.phaseUnit bits.length ≤
        TargetEmitterControllerPolynomialBound.shiftedSize bits.length *
          TargetEmitterControllerPolynomialBound.phaseUnit bits.length := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right
        (TargetEmitterControllerPolynomialBound.phaseUnit bits.length)
        shiftedPositive
  have bounded :
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound
          bits.length := by
    have twice :
        localSteps + 1 ≤
          2 * TargetEmitterControllerPolynomialBound.phaseUnit bits.length := by
      omega
    have lifted := Nat.le_trans twice
      (Nat.mul_le_mul_left 2 phaseLift)
    have relaxed :=
      Nat.mul_le_mul_right
        (TargetEmitterControllerPolynomialBound.shiftedSize bits.length *
          TargetEmitterControllerPolynomialBound.phaseUnit bits.length)
        (show 2 ≤ 512 by decide)
    unfold steps
      TargetEmitterControllerPolynomialBound.allInputWorkBound
    exact Nat.le_trans lifted (by
      simpa only [Nat.mul_assoc] using relaxed)
  refine ⟨steps, final, bounded, ?_, ?_, ?_, outputEmpty⟩
  · simpa [TargetEmitterController.machine, final,
      workStartConfiguration] using exactRun
  · exact reject_halted localFinalTape
  · rfl

/-- Grammar success, the ledger bridge, and the exact four-phase controller
trace fit the all-input work polynomial and emit the direct raw target. -/
theorem decoded_bounded_exact
    (bits : BitString) (raw : RawCircuit)
    (decoded : decodeCircuit bits = some raw) :
    ∃ steps final,
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = machine.acceptState ∧
      (encodeWorkTape final.tape).outputBits =
        RawBuilder.targetBytes bits := by
  rcases
      TargetEmitterControllerPolynomialBound.controller_complete_path_polynomial
        raw with
    ⟨gateListSteps, normalizationSteps, prefixSteps, outputSteps,
      finalTape, controllerPath, _finalRepresents, controllerOutput,
      controllerBound⟩
  let scannerLedgerSteps :=
    TargetEmitterGrammarScanner.canonicalSteps raw + 1 +
      (TargetEmitterLedger.workSteps raw + 1)
  let controllerSteps :=
    gateListSteps + normalizationSteps + prefixSteps + outputSteps
  let steps := scannerLedgerSteps + controllerSteps
  have complete :
      AcceptPath graph (.node scannerRef) .accept steps
        (rawInputWorkTape (encodeCircuit raw)) finalTape := by
    exact
      AcceptPath.trans graph (.node scannerRef)
        (.node stackInitializeRef) .accept
        scannerLedgerSteps controllerSteps
        (rawInputWorkTape (encodeCircuit raw))
        (TargetEmitterLedger.finalConfiguration raw).tape
        finalTape
        (by
          simpa [scannerLedgerSteps] using
            TargetEmitterControllerTrace.scanner_ledger_path raw)
        (by simpa [controllerSteps] using controllerPath)
  have sourceCanonical :
      encodeCircuit raw = bits :=
    PNP.Concrete.LockedNAND.encodeCircuit_eq_of_decodeCircuit_eq_some
      bits raw decoded
  have scanner :
      TargetEmitterGrammarScanner.canonicalSteps raw ≤
        TargetEmitterControllerPolynomialBound.phaseUnit
          (encodeCircuit raw).length := by
    exact Nat.le_trans
      (TargetEmitterGrammarScanner.canonicalSteps_le_grammarWorkBound raw)
      (TargetEmitterControllerPolynomialBound.grammarWorkBound_le_phaseUnit _)
  have ledger :=
    TargetEmitterControllerPolynomialBound.ledgerWorkSteps_add_one_le_phaseUnit
      raw
  have phasePositive :=
    TargetEmitterControllerPolynomialBound.one_le_phaseUnit
      (encodeCircuit raw).length
  have scannerLedger :
      scannerLedgerSteps ≤
        3 * TargetEmitterControllerPolynomialBound.phaseUnit
          (encodeCircuit raw).length := by
    unfold scannerLedgerSteps
    omega
  have sizePositive :
      1 ≤ TargetEmitterControllerPolynomialBound.shiftedSize
          (encodeCircuit raw).length := by
    unfold TargetEmitterControllerPolynomialBound.shiftedSize
    omega
  have phaseLift :
      TargetEmitterControllerPolynomialBound.phaseUnit
          (encodeCircuit raw).length ≤
        TargetEmitterControllerPolynomialBound.shiftedSize
            (encodeCircuit raw).length *
          TargetEmitterControllerPolynomialBound.phaseUnit
            (encodeCircuit raw).length := by
    simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right
        (TargetEmitterControllerPolynomialBound.phaseUnit
          (encodeCircuit raw).length)
        sizePositive
  have scannerLedgerCommon :
      scannerLedgerSteps ≤
        3 *
          (TargetEmitterControllerPolynomialBound.shiftedSize
              (encodeCircuit raw).length *
            TargetEmitterControllerPolynomialBound.phaseUnit
              (encodeCircuit raw).length) :=
    Nat.le_trans scannerLedger (Nat.mul_le_mul_left 3 phaseLift)
  have controllerCommon :
      controllerSteps ≤
        256 *
          (TargetEmitterControllerPolynomialBound.shiftedSize
              (encodeCircuit raw).length *
            TargetEmitterControllerPolynomialBound.phaseUnit
              (encodeCircuit raw).length) := by
    rw [
      TargetEmitterControllerPolynomialBound.controllerWorkTimePolynomial_eval]
      at controllerBound
    simpa only [
      TargetEmitterControllerPolynomialBound.controllerWorkBound,
      controllerSteps, Nat.mul_assoc] using controllerBound
  have allCommon := Nat.add_le_add scannerLedgerCommon controllerCommon
  have encodedBound :
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound
          (encodeCircuit raw).length := by
    have relaxed :
        259 *
            (TargetEmitterControllerPolynomialBound.shiftedSize
                (encodeCircuit raw).length *
              TargetEmitterControllerPolynomialBound.phaseUnit
                (encodeCircuit raw).length) ≤
          512 *
            (TargetEmitterControllerPolynomialBound.shiftedSize
                (encodeCircuit raw).length *
              TargetEmitterControllerPolynomialBound.phaseUnit
                (encodeCircuit raw).length) :=
      Nat.mul_le_mul_right _ (by decide)
    have sumCommon :
        steps ≤
          259 *
            (TargetEmitterControllerPolynomialBound.shiftedSize
                (encodeCircuit raw).length *
              TargetEmitterControllerPolynomialBound.phaseUnit
                (encodeCircuit raw).length) := by
      unfold steps
      exact Nat.le_trans allCommon (by omega)
    unfold TargetEmitterControllerPolynomialBound.allInputWorkBound
    exact Nat.le_trans sumCommon
      (by simpa only [Nat.mul_assoc] using relaxed)
  let final : WorkConfiguration :=
    { state := machine.acceptState, tape := finalTape }
  have exactRun :=
    runEntryToAccept graph steps
      (rawInputWorkTape bits) finalTape graph_wellFormed
      (by
        simpa [sourceCanonical, TargetEmitterController.graph] using
          complete)
  refine
    ⟨steps, final, ?_, ?_, accept_halted finalTape, rfl, ?_⟩
  · simpa [sourceCanonical] using encodedBound
  · simpa [TargetEmitterController.machine, final,
      workStartConfiguration] using exactRun
  · calc
      (encodeWorkTape finalTape).outputBits =
          encodeTokens
            (TargetEmitterSemanticCompletion.completeRuntime
              raw).targetTokens := controllerOutput
      _ =
          encodeTokens
            (encodeLockedInstanceTokens
              (RawBuilder.rawLockedInstance raw)) :=
        congrArg encodeTokens
          (TargetEmitterSemanticCompletion.completeRuntime_targetTokens raw)
      _ = RawBuilder.targetBytes bits := by
        rw [RawBuilder.targetBytes_of_decoded bits raw decoded]
        rfl

/-! ### Closed all-input interface -/

/-- The fixed grammar-only emitter has one exact halted outcome on every raw
bitstring.  Acceptance is precisely successful strict-v0 grammar decoding;
the output is the direct raw target on success and empty on failure. -/
theorem allInput_exact
    (bits : BitString) :
    ∃ steps final,
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      (final.state = machine.acceptState ↔
        ∃ raw, decodeCircuit bits = some raw) ∧
      (encodeWorkTape final.tape).outputBits =
        RawBuilder.targetBytes bits := by
  cases decoded : decodeCircuit bits with
  | none =>
      rcases malformed_exact bits decoded with
        ⟨steps, final, runExact, halted, rejected, outputEmpty⟩
      refine ⟨steps, final, runExact, halted, ?_, ?_⟩
      · constructor
        · intro accepted
          exfalso
          rw [rejected] at accepted
          exact
            TargetEmitterController.machine_accept_ne_reject
              accepted.symm
        · rintro ⟨raw, rawDecoded⟩
          contradiction
      · rw [RawBuilder.targetBytes_of_malformed bits decoded]
        exact outputEmpty
  | some raw =>
      rcases decoded_exact bits raw decoded with
        ⟨steps, final, runExact, halted, accepted, outputEq⟩
      refine ⟨steps, final, runExact, halted, ?_, outputEq⟩
      constructor
      · intro _
        exact ⟨raw, rfl⟩
      · intro _
        exact accepted

/-- Polynomially bounded form of the unconditional exact interface.  The
witness and bound are constructed internally from the literal malformed or
decoded branch; callers supply no schedule certificate. -/
theorem allInput_bounded_exact
    (bits : BitString) :
    ∃ steps final,
      steps ≤
        TargetEmitterControllerPolynomialBound.allInputWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      (final.state = machine.acceptState ↔
        ∃ raw, decodeCircuit bits = some raw) ∧
      (encodeWorkTape final.tape).outputBits =
        RawBuilder.targetBytes bits := by
  cases decoded : decodeCircuit bits with
  | none =>
      rcases malformed_bounded_exact bits decoded with
        ⟨steps, final, bounded, runExact, halted, rejected, outputEmpty⟩
      refine ⟨steps, final, bounded, runExact, halted, ?_, ?_⟩
      · constructor
        · intro accepted
          exfalso
          rw [rejected] at accepted
          exact
            TargetEmitterController.machine_accept_ne_reject
              accepted.symm
        · rintro ⟨raw, rawDecoded⟩
          contradiction
      · rw [RawBuilder.targetBytes_of_malformed bits decoded]
        exact outputEmpty
  | some raw =>
      rcases decoded_bounded_exact bits raw decoded with
        ⟨steps, final, bounded, runExact, halted, accepted, outputEq⟩
      refine ⟨steps, final, bounded, runExact, halted, ?_, outputEq⟩
      constructor
      · intro _
        exact ⟨raw, rfl⟩
      · intro _
        exact accepted

end PNP.Concrete.LockedNAND.TargetEmitterControllerTotalTrace
