/-
Copyright (c) 2026 PNP Labs.

Choice-free total execution of the fixed canonical CNF-to-NAND controller.

The proof composes the exact scanner/ledger/validation prefix, the structural
count traversal, and the structural emission traversal.  Step counts remain
existential witnesses carried by those traces; no schedule is selected with
classical choice or supplied by a caller.
-/

import PNP.Concrete.CNFToNANDControllerCountTrace
import PNP.Concrete.CNFToNANDControllerCompletionTrace
import PNP.Concrete.CNFToNANDControllerTotalBound

namespace PNP.Concrete.CNFToNANDControllerTotalTrace

open PNP.Concrete
open PNP.Concrete.LockedNAND
open PNP.Concrete.WorkMachineProgramGraph
open PNP.Concrete.WorkMachineProgramPath
open PNP.Concrete.CNFToNANDController

private abbrev TapeRepresents :=
  PNP.Concrete.CNFToNANDControllerCanonicalTrace.TapeRepresents

/-- The canonical retained carrier reaches global acceptance within the
closed encoded-input controller polynomial and emits exactly the pure
CNF-to-NAND formula plan. -/
theorem canonical_path (formula : CNFFormula) :
    ∃ steps finalTape,
      steps ≤
        CNFToNANDControllerPolynomialBound.controllerWorkBound
          (encodeCNF formula).length ∧
      AcceptPath graph (.node scannerRef) .accept steps
        (rawInputWorkTape
          (encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula)))
        finalTape ∧
      (encodeWorkTape finalTape).outputBits =
        CNFToNAND.emitFormulaPlan formula := by
  rcases
      CNFToNANDControllerCanonicalTrace.canonical_prefix_path formula with
    ⟨prefixTape, prefixPath, prefixRepresents⟩
  have countInput :
      TapeRepresents (passHeaderRef .count).startState
          (CNFToNANDWorkspace.capacity formula) 0
          (CNFToNANDControllerCountTrace.countedRegisters formula 0 0)
          [] (CNFToNANDControllerCanonicalTrace.canonicalSource formula)
          [] prefixTape := by
    simpa [CNFToNANDControllerCountTrace.countedRegisters_zero] using
      prefixRepresents
  rcases
      CNFToNANDControllerCountTrace.count_pass_path
        formula prefixTape countInput with
    ⟨countSteps, countTape, countPath, emitRepresents, countBound⟩
  have completionInput :
      TapeRepresents (passHeaderRef .emit).startState
          (CNFToNANDWorkspace.capacity formula)
          (CNFToNANDControllerCountTrace.emitInitialRuntime formula).scratch
          (CNFToNANDControllerCountTrace.emitInitialRuntime formula).registers
          (CNFToNANDControllerCountTrace.emitInitialRuntime formula).checks
          (CNFToNANDControllerCanonicalTrace.canonicalSource formula)
          (CNFToNANDControllerCountTrace.headerTokens formula)
          countTape := by
    simpa using emitRepresents
  rcases
      CNFToNANDControllerCompletionTrace.completion_path
        formula countTape completionInput with
    ⟨completionSteps, finalTape, completionBound, completionPath, outputEq⟩
  let steps :=
    CNFToNANDControllerCanonicalTrace.canonicalPrefixSteps formula +
      countSteps + completionSteps
  have prefixCount :
      AcceptPath graph (.node scannerRef)
        (.node (passHeaderRef .emit))
        (CNFToNANDControllerCanonicalTrace.canonicalPrefixSteps formula +
          countSteps)
        (rawInputWorkTape
          (encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula)))
        countTape :=
    AcceptPath.trans graph _ _ _ _ _ _ _ _
      prefixPath countPath
  have complete :
      AcceptPath graph (.node scannerRef) .accept steps
        (rawInputWorkTape
          (encodeCircuit
            (CNFToNANDWorkspace.carrierCircuit formula)))
        finalTape := by
    exact
      AcceptPath.trans graph _ _ _ _ _ _ _ _
        prefixCount completionPath
  have envelopeBound :=
    CNFToNANDControllerTotalBound.canonicalEnvelope_le_controllerWorkBound
      formula
  have bounded :
      steps ≤
        CNFToNANDControllerPolynomialBound.controllerWorkBound
          (encodeCNF formula).length := by
    unfold steps
    unfold CNFToNANDControllerTotalBound.canonicalEnvelope at envelopeBound
    omega
  exact ⟨steps, finalTape, bounded, complete, outputEq⟩

/-- Exact graph-machine execution corresponding to `canonical_path`. -/
theorem canonical_bounded_exact (formula : CNFFormula) :
    ∃ steps final,
      steps ≤
        CNFToNANDControllerPolynomialBound.controllerWorkBound
          (encodeCNF formula).length ∧
      workRunExact? machine steps
          (workStartConfiguration machine
            (rawInputWorkTape
              (encodeCircuit
                (CNFToNANDWorkspace.carrierCircuit formula)))) =
        some final ∧
      machine.isHalted final = true ∧
      final.state = machine.acceptState ∧
      (encodeWorkTape final.tape).outputBits =
        CNFToNAND.emitFormulaPlan formula := by
  rcases canonical_path formula with
    ⟨steps, finalTape, bounded, path, outputEq⟩
  let final : WorkConfiguration :=
    { state := machine.acceptState, tape := finalTape }
  have exactRun :=
    runEntryToAccept graph steps
      (rawInputWorkTape
        (encodeCircuit
          (CNFToNANDWorkspace.carrierCircuit formula)))
      finalTape graph_wellFormed path
  refine
    ⟨steps, final, bounded, ?_, accept_halted finalTape, rfl, outputEq⟩
  simpa [CNFToNANDController.machine, final,
    workStartConfiguration] using exactRun

end PNP.Concrete.CNFToNANDControllerTotalTrace
