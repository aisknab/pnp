/-
Copyright (c) 2026 PNP Labs.

Closed all-input exact traces for the fixed three-node CNF-to-NAND compiler.
Decoded formulas use the parser/carrier prefix and the complete physical
controller.  Malformed words take the parser's literal reject bridge and
retain the empty fail-closed output.
-/

import PNP.Concrete.CNFToNANDControllerTotalTrace
import PNP.Concrete.CNFToNANDCompilerPolynomialBound

namespace PNP.Concrete.CNFToNANDCompilerTotalTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open CNFToNANDCompilerMachine

/-! ## Transported controller launch -/

private theorem outerController_path_of_inner
    (formula : CNFFormula) (controllerSteps : Nat)
    (canonicalFinal actualInitial : WorkTape)
    (innerPath :
      AcceptPath CNFToNANDController.graph
        (.node CNFToNANDController.scannerRef) .accept
        controllerSteps
        (rawInputWorkTape
          (LockedNAND.encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula)))
        canonicalFinal)
    (canonicalOutput :
      (encodeWorkTape canonicalFinal).outputBits =
        CNFToNAND.emitFormulaPlan formula)
    (initialEquivalent :
      WorkTape.BlankEquivalent actualInitial
        (rawInputWorkTape
          (LockedNAND.encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula)))) :
    ∃ actualFinal,
      AcceptPath graph (.node controllerRef) .accept
        (controllerSteps + 1) actualInitial actualFinal ∧
      (encodeWorkTape actualFinal).outputBits =
        CNFToNAND.emitFormulaPlan formula := by
  rcases AcceptPath.transport innerPath initialEquivalent with
    ⟨actualFinal, actualInnerPath, finalEquivalent⟩
  have innerExact :=
    runEntryToAccept CNFToNANDController.graph controllerSteps
      actualInitial actualFinal
      CNFToNANDController.graph_wellFormed actualInnerPath
  have localRun :
      LocalAcceptRun controllerNode controllerSteps
        actualInitial actualFinal := by
    unfold LocalAcceptRun
    simpa [controllerNode, CNFToNANDController.machine,
      workStartConfiguration] using innerExact
  have tail :
      AcceptPath graph .accept .accept 0
        actualFinal actualFinal :=
    .terminal _ _
  have path :=
    AcceptPath.step controllerNode .accept controllerSteps 0
      actualInitial actualFinal actualFinal
      controllerNode_member localRun tail
  refine ⟨actualFinal, ?_, ?_⟩
  · simpa [controllerNode, controllerRef, Node.reference] using path
  · exact
      (CNFToNANDControllerCompletionTrace.encodeWorkTape_outputBits_eq_of_blankEquivalent
          finalEquivalent).trans canonicalOutput

/-! ## Fail-closed parser branch -/

/-- Every malformed source reaches the global reject halt within the common
all-input polynomial and leaves empty output. -/
theorem malformed_bounded_exact
    (bits : BitString)
    (malformed : decodeEncodedCNF bits = none) :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = machine.rejectState ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  rcases CNFToNANDCompilerTrace.malformed_exact bits malformed with
    ⟨steps, final, bounded, runExact, halted, rejected, outputEmpty⟩
  exact
    ⟨steps, final,
      Nat.le_trans bounded
        (CNFToNANDCompilerPolynomialBound.malformedWorkBound_le
          bits.length),
      runExact, halted, rejected, outputEmpty⟩

/-! ## Successful decoded branch -/

/-- Every successfully decoded CNF word traverses the canonical carrier and
complete count/emission controller, then reaches global acceptance with the
pure compiler's exact bytes. -/
theorem decoded_bounded_exact
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = machine.acceptState ∧
      (encodeWorkTape final.tape).outputBits =
        CNFToNAND.compileEncodedCNFToNAND bits := by
  rcases
      CNFToNANDCompilerTrace.decoded_preController_path
        bits formula decoded with
    ⟨prefixFinal, prefixPath, prefixEquivalent⟩
  rcases CNFToNANDControllerTotalTrace.canonical_path formula with
    ⟨controllerSteps, canonicalFinal, controllerBound,
      controllerPath, controllerOutput⟩
  have carrierEquivalent :
      WorkTape.BlankEquivalent prefixFinal
        (rawInputWorkTape
          (LockedNAND.encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula))) := by
    exact WorkTape.blankEquivalent_trans prefixEquivalent (by
      simpa [CNFToNANDWorkspace.formulaTokens,
        CNFToNANDWorkspace.carrierCircuit] using
        CNFToNANDCarrierEncoder.finalTape_blankEquivalent_rawInput
          (encodeFormulaTokens formula))
  rcases
      outerController_path_of_inner formula
        controllerSteps
        canonicalFinal prefixFinal controllerPath controllerOutput
        carrierEquivalent with
    ⟨finalTape, controllerOuterPath, outputEq⟩
  let steps :=
    CNFToNANDCompilerTrace.preControllerSteps formula +
      (controllerSteps + 1)
  have complete :
      AcceptPath graph (.node parserRef) .accept steps
        (rawInputWorkTape bits) finalTape := by
    exact
      AcceptPath.trans graph (.node parserRef)
        (.node controllerRef) .accept
        (CNFToNANDCompilerTrace.preControllerSteps formula)
        (controllerSteps + 1)
        _ _ _ prefixPath controllerOuterPath
  have componentBound :=
    CNFToNANDCompilerPolynomialBound.canonicalComponents_le formula
      (CNFToNANDCarrierEncoder.canonicalWorkSteps
        (CNFToNANDWorkspace.formulaTokens formula))
      controllerSteps
      (Nat.le_refl _)
      controllerBound
  have sourceCanonical : encodeCNF formula = bits := by
    exact
      CNFToNAND.encodeCNF_of_decodeEncodedCNF
        bits formula decoded
  have bounded :
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound bits.length := by
    rw [← sourceCanonical]
    unfold steps CNFToNANDCompilerTrace.preControllerSteps
    simpa [CNFToNANDWorkspace.formulaTokens,
      Nat.add_assoc] using componentBound
  let final : WorkConfiguration :=
    { state := machine.acceptState, tape := finalTape }
  have exactRun :=
    runEntryToAccept graph steps
      (rawInputWorkTape bits) finalTape graph_wellFormed complete
  refine
    ⟨steps, final, bounded, ?_, accept_halted finalTape, rfl, ?_⟩
  · simpa [CNFToNANDCompilerMachine.machine, final,
      workStartConfiguration] using exactRun
  · exact outputEq.trans
      (CNFToNAND.emitFormulaPlan_eq_compileEncodedCNFToNAND_of_decoded
        bits formula decoded)

/-! ## Closed all-input interface -/

/-- The fixed compiler has one bounded halted outcome on every bitstring.
Acceptance is strict CNF decoding; output is the exact pure compiler result
on success and the empty fail-closed word on failure. -/
theorem allInput_bounded_exact
    (bits : BitString) :
    ∃ steps final,
      steps ≤
        CNFToNANDCompilerPolynomialBound.allInputWorkBound bits.length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      (final.state = machine.acceptState ↔
        CNFSourceParser.ValidEncodedCNF bits) ∧
      (encodeWorkTape final.tape).outputBits =
        CNFToNAND.compileEncodedCNFToNAND bits := by
  cases decoded : decodeEncodedCNF bits with
  | none =>
      rcases malformed_bounded_exact bits decoded with
        ⟨steps, final, bounded, runExact, halted,
          rejected, outputEmpty⟩
      refine
        ⟨steps, final, bounded, runExact, halted, ?_, ?_⟩
      · constructor
        · intro accepted
          exfalso
          rw [rejected] at accepted
          exact machine_accept_ne_reject accepted.symm
        · intro valid
          exact
            (CNFSourceParser.not_valid_of_decode_none decoded valid).elim
      · rw [CNFToNAND.compileEncodedCNFToNAND_of_malformed bits decoded]
        exact outputEmpty
  | some formula =>
      rcases decoded_bounded_exact bits formula decoded with
        ⟨steps, final, bounded, runExact, halted,
          accepted, outputEq⟩
      refine
        ⟨steps, final, bounded, runExact, halted, ?_, outputEq⟩
      constructor
      · intro _
        exact CNFSourceParser.valid_of_decoded decoded
      · intro _
        exact accepted

/-- Bound-erased exact interface for clients that need only total execution,
acceptance, and output semantics. -/
theorem allInput_exact
    (bits : BitString) :
    ∃ steps final,
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final ∧
      machine.isHalted final = true ∧
      (final.state = machine.acceptState ↔
        CNFSourceParser.ValidEncodedCNF bits) ∧
      (encodeWorkTape final.tape).outputBits =
        CNFToNAND.compileEncodedCNFToNAND bits := by
  rcases allInput_bounded_exact bits with
    ⟨steps, final, _bounded, runExact, halted,
      acceptanceIff, outputEq⟩
  exact
    ⟨steps, final, runExact, halted, acceptanceIff, outputEq⟩

end PNP.Concrete.CNFToNANDCompilerTotalTrace
