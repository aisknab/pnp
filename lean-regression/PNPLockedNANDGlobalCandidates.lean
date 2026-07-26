import PNP

namespace PNP.DirectWire.LockedNANDGlobalCandidatesRegression

open LockedNANDTrace
open LockedNANDGlobalCandidates

def inputFalse : Valuation 1 := fun _ => false
def inputTrue : Valuation 1 := fun _ => true

def negationProgram : Program 1 1 :=
  .snoc .empty
    { left := .input fin1Zero
      right := .input fin1Zero }

abbrev negationCircuit : Circuit 1 :=
  { gateCount := 1
    program := negationProgram
    outputGate := fin1Zero }

def conjunctionProgram : Program 2 2 :=
  .snoc nandProgram
    { left := .gate fin1Zero
      right := .gate fin1Zero }

abbrev conjunctionCircuit : Circuit 2 :=
  { gateCount := 2
    program := conjunctionProgram
    outputGate := fin2One }

def zeroInput : Valuation 0 := fun index => Fin.elim0 index

def constantTrueProgram : Program 0 1 :=
  .snoc .empty
    { left := .constant false
      right := .constant false }

abbrev constantTrueCircuit : Circuit 0 :=
  { gateCount := 1
    program := constantTrueProgram
    outputGate := fin1Zero }

def allTrue3 : Valuation 3 := fun _ => true

def oneFalse3 : Valuation 3 :=
  fun index => index.val != 1

example (valuation : CarrierValuation 2 2) :
    unflattenCarrier (flattenCarrier valuation) = valuation :=
  unflatten_flatten valuation

example (valuation : Valuation (carrierWidth 2 2)) :
    flattenCarrier (unflattenCarrier valuation) = valuation :=
  flatten_unflatten valuation

example (valuation : CarrierValuation 2 2) :
    flattenCarrier valuation (finalLockSlot 2 2) =
      valuation.finalLock :=
  flattenCarrier_finalLock valuation

example :
    sourceMacroGateCount
      (Source.input fin1Zero : Source 1 0) = 10 := rfl

example :
    sourceMacroGateCount
      (Source.constant false : Source 0 0) = 3 := rfl

example :
    sourceMacroGateCount
      (Source.constant true : Source 0 0) = 2 := rfl

example : macroGateCount negationProgram = 38 := rfl

example : macroGateCount constantTrueProgram = 24 := rfl

example : checkTailCount negationCircuit = 2 := rfl

example : checkTailCount conjunctionCircuit = 5 := rfl

example : rawBaselineGateCount negationCircuit = 42 := rfl

example : rawBaselineGateCount constantTrueCircuit = 28 := rfl

example :
    rawBaselineGateCount negationCircuit =
      lockedBaselineCount negationProgram :=
  rawBaselineGateCount_eq_lockedBaselineCount negationCircuit

example :
    (nonemptyPrefixCandidate 2).program.size = 4 :=
  nonemptyPrefixCandidate_size 2

example :
    (nonemptyPrefixCandidate 2).semantics allTrue3 fin1Zero = true := by
  rw [nonemptyPrefixCandidate_semantics]
  decide

example :
    (nonemptyPrefixCandidate 2).semantics oneFalse3 fin1Zero = false := by
  rw [nonemptyPrefixCandidate_semantics]
  decide

example :
    (circuitPrefixCandidate negationCircuit).program.size = 4 :=
  circuitPrefixCandidate_size negationCircuit

example :
    (baselineCandidate negationCircuit).program.size = 42 := by
  rw [baselineCandidate_size]
  rfl

example :
    (fullCandidate negationCircuit).program.size = 46 := by
  rw [fullCandidate_size]
  rfl

example :
    ∀ input output,
      (fullCandidate negationCircuit).semantics input
          (baselineOutputEmbedding output) =
        (baselineCandidate negationCircuit).semantics input output :=
  fullCandidate_initial_semantics negationCircuit

example :
    (fullCandidate negationCircuit).semantics
        (flattenCarrier
          (coherentExtension negationProgram inputFalse))
        (conditionalFinalOutput
          (lockedBaselineCount negationProgram)) = true := by
  rw [fullCandidate_final_semantics_flatten]
  rw [tracePredicate_coherentExtension]
  rfl

example :
    (fullCandidate negationCircuit).semantics
        (flattenCarrier
          (coherentExtension negationProgram inputTrue))
        (conditionalFinalOutput
          (lockedBaselineCount negationProgram)) = false := by
  rw [fullCandidate_final_semantics_flatten]
  rw [tracePredicate_coherentExtension]
  rfl

example :
    (fullCandidate constantTrueCircuit).semantics
        (flattenCarrier
          (coherentExtension constantTrueProgram zeroInput))
        (conditionalFinalOutput
          (lockedBaselineCount constantTrueProgram)) = true := by
  rw [fullCandidate_final_semantics_flatten]
  rw [tracePredicate_coherentExtension]
  rfl

example :
    (baselineCandidate negationCircuit).program.hasNoConstant = true :=
  baselineCandidate_no_internal_constants negationCircuit

example :
    (fullCandidate negationCircuit).program.hasNoConstant = true :=
  fullCandidate_no_internal_constants negationCircuit

example
    (input : Valuation (carrierWidth 1 negationCircuit.gateCount))
    (output : Fin (lockedBaselineCount negationProgram)) :
    (baselineCandidate negationCircuit).semantics
        (setFinalLockValue input false) output =
      (baselineCandidate negationCircuit).semantics
        (setFinalLockValue input true) output :=
  baselineCandidate_finalLock_irrelevant negationCircuit
    input false true output

end PNP.DirectWire.LockedNANDGlobalCandidatesRegression
