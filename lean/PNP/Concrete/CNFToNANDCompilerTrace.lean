/-
Copyright (c) 2026 PNP Labs.

Exact all-input traces for the fixed CNF-to-NAND compiler graph.

The parser is the only outer node exposed to arbitrary raw bits.  Its reject
branch reaches the graph reject halt directly.  Its accept branch preserves
the canonical CNF word and hands an equivalent infinite blank tape to the
carrier encoder.  The carrier and controller suffix is composed below only
from their certificate-free canonical exact interfaces.
-/

import PNP.Concrete.CNFToNANDCompilerMachine
import PNP.Concrete.CNFToNANDControllerCanonicalTrace
import PNP.Concrete.WorkMachineProgramPathBlankEquivalence

namespace PNP.Concrete.CNFToNANDCompilerTrace

open PNP.Concrete
open WorkMachineProgramGraph
open WorkMachineProgramPath
open CNFToNANDCompilerMachine

/-! ## Parser boundary -/

/-- A canonical formula follows the parser node's literal accept bridge to
the carrier node. -/
theorem parser_path (formula : CNFFormula) :
    AcceptPath graph (.node parserRef) (.node carrierRef)
      (CNFSourceParser.validWorkSteps formula + 1)
      (rawInputWorkTape (encodeFormula formula))
      (CNFSourceParser.acceptedConfiguration formula).tape := by
  have localRun :
      LocalAcceptRun parserNode
        (CNFSourceParser.validWorkSteps formula)
        (rawInputWorkTape (encodeFormula formula))
        (CNFSourceParser.acceptedConfiguration formula).tape := by
    unfold LocalAcceptRun
    change
      workRunExact? CNFSourceParser.machine
          (CNFSourceParser.validWorkSteps formula)
          (workStartConfiguration CNFSourceParser.machine
            (rawInputWorkTape (encodeFormula formula))) =
        some
          { state := CNFSourceParser.machine.acceptState
            tape :=
              (CNFSourceParser.acceptedConfiguration formula).tape }
    rw [← CNFSourceParser.acceptedConfiguration_state formula]
    exact CNFSourceParser.encodeFormula_exact formula
  have tail :
      AcceptPath graph (.node carrierRef) (.node carrierRef) 0
        (CNFSourceParser.acceptedConfiguration formula).tape
        (CNFSourceParser.acceptedConfiguration formula).tape :=
    .terminal _ _
  have path :=
    AcceptPath.step parserNode (.node carrierRef)
      (CNFSourceParser.validWorkSteps formula) 0
      (rawInputWorkTape (encodeFormula formula))
      (CNFSourceParser.acceptedConfiguration formula).tape
      (CNFSourceParser.acceptedConfiguration formula).tape
      parserNode_member localRun tail
  simpa [parserNode, parserRef, Node.reference] using path

/-- The same parser path starts from any successfully decoded external word;
strict decoder inversion identifies that word with its canonical encoding. -/
theorem decoded_parser_path
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    AcceptPath graph (.node parserRef) (.node carrierRef)
      (CNFSourceParser.validWorkSteps formula + 1)
      (rawInputWorkTape bits)
      (CNFSourceParser.acceptedConfiguration formula).tape := by
  have path := parser_path formula
  rw [encodeFormula_of_decode bits formula decoded] at path
  exact path

/-- The successful parser endpoint denotes the same infinite blank tape as
the ordinary canonical raw input.  The extra materialized blanks are not
observable by any work-machine transition. -/
theorem parserAcceptedTape_blankEquivalent_rawInput
    (formula : CNFFormula) :
    WorkTape.BlankEquivalent
      (CNFSourceParser.acceptedConfiguration formula).tape
      (rawInputWorkTape (encodeFormula formula)) := by
  rw [CNFSourceParser.rawInputWorkTape_encodeFormula,
    ← CNFSourceParser.formulaWord_eq_token_work_symbols]
  cases wordEq : CNFSourceParser.formulaWord formula with
  | nil =>
      exact False.elim
        (CNFSourceParser.formulaWord_ne_nil formula wordEq)
  | cons first rest =>
      have padded :=
        WorkTape.blankEquivalent_of_padding
          (WorkTape.ofSymbols
            ((first :: rest) ++ [CNFSourceParser.formulaPad]))
          1 1
      exact (by
        simpa [CNFSourceParser.acceptedConfiguration, wordEq,
          workConfigAtWord, WorkTape.atWord, WorkTape.ofSymbols,
          WorkTape.focus,
          CNFSourceParser.cellBlank, CNFSourceParser.formulaPad,
          cnfBlank, List.append_assoc] using padded)

/-- The parser's accepted finite window can launch the carrier whose
canonical statement reserves a larger blank work area. -/
theorem parserAcceptedTape_blankEquivalent_carrierEntry
    (formula : CNFFormula) :
    WorkTape.BlankEquivalent
      (CNFSourceParser.acceptedConfiguration formula).tape
      (CNFToNANDCarrierEncoder.entryTape
        (encodeFormulaTokens formula) [] []) := by
  have parserEquivalent :=
    parserAcceptedTape_blankEquivalent_rawInput formula
  have carrierEquivalent :=
    CNFToNANDCarrierEncoder.entryTape_blankEquivalent_rawInput
      (encodeFormulaTokens formula)
  exact WorkTape.blankEquivalent_trans parserEquivalent
    (WorkTape.blankEquivalent_symm (by
      simpa [encodeFormula, encodeCNF,
        encodeFormulaTokens] using carrierEquivalent))

/-! ## Canonical carrier boundary -/

set_option maxHeartbeats 1000000 in
/-- The parser endpoint launches the carrier through blank-equivalence
transport.  The existential finite endpoint may retain a different number of
exterior blank cells, but denotes the exact canonical carrier output. -/
theorem carrier_path (formula : CNFFormula) :
    ∃ finalTape,
      AcceptPath graph (.node carrierRef) (.node controllerRef)
        (CNFToNANDCarrierEncoder.canonicalWorkSteps
            (encodeFormulaTokens formula) + 1)
        (CNFSourceParser.acceptedConfiguration formula).tape
        finalTape ∧
      WorkTape.BlankEquivalent finalTape
        (CNFToNANDCarrierEncoder.finalTape
          (encodeFormulaTokens formula) [] []) := by
  cases tokensEq : encodeFormulaTokens formula with
  | nil =>
      have impossible :
          CNFToNANDWorkspace.formulaTokens formula = [] := by
        simpa [CNFToNANDWorkspace.formulaTokens] using tokensEq
      exact False.elim
        (CNFToNANDWorkspace.formulaTokens_ne_nil formula impossible)
  | cons first rest =>
      let actualInitial : WorkConfiguration :=
        { state := CNFToNANDCarrierEncoder.machine.startState
          tape := (CNFSourceParser.acceptedConfiguration formula).tape }
      have initialEquivalent :
          WorkConfiguration.BlankEquivalent actualInitial
            (CNFToNANDCarrierEncoder.entryConfiguration
              (encodeFormulaTokens formula) [] []) := by
        refine ⟨rfl, ?_⟩
        exact parserAcceptedTape_blankEquivalent_carrierEntry formula
      have canonicalRun :
          workRunExact? CNFToNANDCarrierEncoder.machine
              (CNFToNANDCarrierEncoder.canonicalWorkSteps
                (encodeFormulaTokens formula))
              (CNFToNANDCarrierEncoder.entryConfiguration
                (encodeFormulaTokens formula) [] []) =
            some
              (CNFToNANDCarrierEncoder.finalConfiguration
                (encodeFormulaTokens formula) [] []) := by
        simpa [tokensEq] using
          CNFToNANDCarrierEncoder.canonical_exact first rest
      rcases PNP.Concrete.workRunExact?_transport
          CNFToNANDCarrierEncoder.machine
          (CNFToNANDCarrierEncoder.canonicalWorkSteps
            (encodeFormulaTokens formula))
          initialEquivalent canonicalRun with
        ⟨actualFinal, actualRun, finalEquivalent⟩
      have actualFinalState :
          actualFinal.state =
            CNFToNANDCarrierEncoder.machine.acceptState :=
        finalEquivalent.state
      have localRun :
          LocalAcceptRun carrierNode
            (CNFToNANDCarrierEncoder.canonicalWorkSteps
              (encodeFormulaTokens formula))
            (CNFSourceParser.acceptedConfiguration formula).tape
            actualFinal.tape := by
        unfold LocalAcceptRun
        change
          workRunExact? CNFToNANDCarrierEncoder.machine
              (CNFToNANDCarrierEncoder.canonicalWorkSteps
                (encodeFormulaTokens formula))
              actualInitial =
            some
              { state :=
                  CNFToNANDCarrierEncoder.machine.acceptState
                tape := actualFinal.tape }
        rw [← actualFinalState]
        exact actualRun
      have tail :
          AcceptPath graph (.node controllerRef) (.node controllerRef) 0
            actualFinal.tape actualFinal.tape :=
        .terminal _ _
      have path :=
        AcceptPath.step carrierNode (.node controllerRef)
          (CNFToNANDCarrierEncoder.canonicalWorkSteps
            (encodeFormulaTokens formula))
          0
          (CNFSourceParser.acceptedConfiguration formula).tape
          actualFinal.tape actualFinal.tape
          carrierNode_member localRun tail
      have finalTapeEquivalent :
          WorkTape.BlankEquivalent actualFinal.tape
            (CNFToNANDCarrierEncoder.finalTape
              (encodeFormulaTokens formula) [] []) :=
        finalEquivalent.tape
      have referenceEq :
          carrierNode.reference = carrierRef := rfl
      rw [referenceEq] at path
      refine ⟨actualFinal.tape, ?_, ?_⟩
      · rw [Nat.add_zero, tokensEq] at path
        exact path
      · simpa only [tokensEq] using finalTapeEquivalent

def preControllerSteps (formula : CNFFormula) : Nat :=
  (CNFSourceParser.validWorkSteps formula + 1) +
    (CNFToNANDCarrierEncoder.canonicalWorkSteps
      (encodeFormulaTokens formula) + 1)

/-- The exact successful outer prefix from canonical source bytes to the
controller launch, retaining the carrier's canonical infinite-tape meaning. -/
theorem preController_path (formula : CNFFormula) :
    ∃ finalTape,
      AcceptPath graph (.node parserRef) (.node controllerRef)
        (preControllerSteps formula)
        (rawInputWorkTape (encodeFormula formula)) finalTape ∧
      WorkTape.BlankEquivalent finalTape
        (CNFToNANDCarrierEncoder.finalTape
          (encodeFormulaTokens formula) [] []) := by
  rcases carrier_path formula with
    ⟨finalTape, carrierPath, finalEquivalent⟩
  refine ⟨finalTape, ?_, finalEquivalent⟩
  exact
    AcceptPath.trans graph (.node parserRef)
      (.node carrierRef) (.node controllerRef)
      (CNFSourceParser.validWorkSteps formula + 1)
      (CNFToNANDCarrierEncoder.canonicalWorkSteps
        (encodeFormulaTokens formula) + 1)
      _ _ _ (parser_path formula) carrierPath

/-- Strict decoder inversion transports the complete successful prefix to
the caller's original byte word. -/
theorem decoded_preController_path
    (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    ∃ finalTape,
      AcceptPath graph (.node parserRef) (.node controllerRef)
        (preControllerSteps formula)
        (rawInputWorkTape bits) finalTape ∧
      WorkTape.BlankEquivalent finalTape
        (CNFToNANDCarrierEncoder.finalTape
          (encodeFormulaTokens formula) [] []) := by
  rw [← encodeFormula_of_decode bits formula decoded]
  exact preController_path formula

/-! ## Fail-closed parser branch -/

/-- Every malformed source follows the parser node's materialized reject
bridge and retains the parser's empty output. -/
theorem malformed_path
    (bits : BitString)
    (malformed : decodeEncodedCNF bits = none) :
    ∃ steps finalTape,
      steps ≤ CNFSourceParser.parserWorkBound bits.length + 1 ∧
      AcceptPath graph (.node parserRef) .reject steps
        (rawInputWorkTape bits) finalTape ∧
      (encodeWorkTape finalTape).outputBits = [] := by
  rcases CNFSourceParser.malformed_rejectingTrace bits malformed with
    ⟨localSteps, localFinal, localBound, localRun,
      rejected, outputEmpty⟩
  rcases localFinal with ⟨localFinalState, localFinalTape⟩
  change localFinalState = CNFSourceParser.State.reject at rejected
  subst localFinalState
  have localReject :
      LocalRejectRun parserNode localSteps
        (rawInputWorkTape bits) localFinalTape := by
    unfold LocalRejectRun
    change
      workRunExact? CNFSourceParser.machine localSteps
          (workStartConfiguration CNFSourceParser.machine
            (rawInputWorkTape bits)) =
        some
          { state := CNFSourceParser.machine.rejectState
            tape := localFinalTape }
    change
      workRunExact? CNFSourceParser.machine localSteps
          (workStartConfiguration CNFSourceParser.machine
            (rawInputWorkTape bits)) =
        some
          { state := CNFSourceParser.State.reject
            tape := localFinalTape }
    exact localRun
  have tail :
      AcceptPath graph .reject .reject 0
        localFinalTape localFinalTape :=
    .terminal _ _
  have path :=
    AcceptPath.stepReject parserNode .reject
      localSteps 0 (rawInputWorkTape bits)
      localFinalTape localFinalTape
      parserNode_member localReject tail
  refine
    ⟨localSteps + 1, localFinalTape, ?_, ?_, outputEmpty⟩
  · omega
  · simpa [parserNode, parserRef, Node.reference] using path

/-- Exact graph-machine execution of every malformed source. -/
theorem malformed_exact
    (bits : BitString)
    (malformed : decodeEncodedCNF bits = none) :
    ∃ steps final,
      steps ≤ CNFSourceParser.parserWorkBound bits.length + 1 ∧
      workRunExact? CNFToNANDCompilerMachine.machine steps
          (workStartConfiguration
            CNFToNANDCompilerMachine.machine
            (rawInputWorkTape bits)) =
        some final ∧
      CNFToNANDCompilerMachine.machine.isHalted final = true ∧
      final.state =
        CNFToNANDCompilerMachine.machine.rejectState ∧
      (encodeWorkTape final.tape).outputBits = [] := by
  rcases malformed_path bits malformed with
    ⟨steps, finalTape, bounded, path, outputEmpty⟩
  let final : WorkConfiguration :=
    { state := CNFToNANDCompilerMachine.machine.rejectState
      tape := finalTape }
  have exactRun :=
    runEntryToReject graph steps
      (rawInputWorkTape bits) finalTape graph_wellFormed path
  refine
    ⟨steps, final, bounded, ?_, reject_halted finalTape, rfl,
      outputEmpty⟩
  simpa [CNFToNANDCompilerMachine.machine, final,
    workStartConfiguration] using exactRun

end PNP.Concrete.CNFToNANDCompilerTrace
