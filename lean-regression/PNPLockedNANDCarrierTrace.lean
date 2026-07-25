import PNP

namespace PNP.DirectWire.LockedNANDTraceRegression

open LockedNANDTrace

def inputFalse : Valuation 1 := fun _ => false
def inputTrue : Valuation 1 := fun _ => true

def negationProgram : Program 1 1 :=
  .snoc .empty
    { left := .input fin1Zero
      right := .input fin1Zero }

def negationCircuit : Circuit 1 :=
  { gateCount := 1
    program := negationProgram
    outputGate := fin1Zero }

def conjunctionProgram : Program 2 2 :=
  .snoc nandProgram
    { left := .gate fin1Zero
      right := .gate fin1Zero }

def conjunctionCircuit : Circuit 2 :=
  { gateCount := 2
    program := conjunctionProgram
    outputGate := fin2One }

def zeroInput : Valuation 0 := fun index => Fin.elim0 index

def constantTrueProgram : Program 0 1 :=
  .snoc .empty
    { left := .constant false
      right := .constant false }

def constantTrueCircuit : Circuit 0 :=
  { gateCount := 1
    program := constantTrueProgram
    outputGate := fin1Zero }

example : carrierWidth 2 2 = 15 := rfl

example :
    decodeCarrierSlot (primarySlot (gates := 2) fin2Zero) =
      CarrierSlot.primary fin2Zero :=
  decodeCarrierSlot_primary fin2Zero

example :
    decodeCarrierSlot (traceSlot (inputs := 2) fin2One) =
      CarrierSlot.trace fin2One :=
  decodeCarrierSlot_trace fin2One

example :
    decodeCarrierSlot
        (occurrenceSlot (inputs := 2)
          (occurrenceCoordinate fin2One .right)) =
      CarrierSlot.occurrence (occurrenceCoordinate fin2One .right) :=
  decodeCarrierSlot_occurrence _

example :
    decodeCarrierSlot
        (sourceLockSlot (inputs := 2)
          (occurrenceCoordinate fin2Zero .left)) =
      CarrierSlot.sourceLock (occurrenceCoordinate fin2Zero .left) :=
  decodeCarrierSlot_sourceLock _

example :
    decodeCarrierSlot (traceLockSlot (inputs := 2) fin2Zero) =
      CarrierSlot.traceLock fin2Zero :=
  decodeCarrierSlot_traceLock fin2Zero

example :
    decodeCarrierSlot (finalLockSlot 2 2) =
      (CarrierSlot.finalLock : CarrierSlot 2 2) :=
  decodeCarrierSlot_finalLock 2 2

example :
    (CarrierSlot.primary fin2Zero :
      CarrierSlot 2 2).encode ≠ finalLockSlot 2 2 :=
  finalLock_fresh (.primary fin2Zero) (by simp)

example :
    (distinguishedChecks (Program.empty : Program 3 0)
      (coherentExtension .empty (fun _ => false))).length = 0 := rfl

example :
    (distinguishedChecks negationProgram
      (coherentExtension negationProgram inputFalse)).length = 3 := by
  rw [distinguishedChecks_length]

example :
    (distinguishedChecks conjunctionProgram
      (coherentExtension conjunctionProgram (fun _ => true))).length = 6 := by
  rw [distinguishedChecks_length]

example :
    tracePredicate negationProgram
      (coherentExtension negationProgram inputFalse) = true :=
  tracePredicate_coherentExtension negationProgram inputFalse

example :
    tracePredicate conjunctionProgram
      (coherentExtension conjunctionProgram (fun _ => true)) = true :=
  tracePredicate_coherentExtension conjunctionProgram (fun _ => true)

example :
    (∃ valuation : CarrierValuation 1 1,
        valuation.primary = inputFalse ∧
        tracePredicate negationProgram valuation = true ∧
        valuation.trace fin1Zero = true) := by
  exact (traceEquivalence negationCircuit inputFalse).mpr rfl

example :
    ¬ (∃ valuation : CarrierValuation 1 1,
        valuation.primary = inputTrue ∧
        tracePredicate negationProgram valuation = true ∧
        valuation.trace fin1Zero = true) := by
  change
    ¬ (∃ valuation : CarrierValuation 1 negationCircuit.gateCount,
        valuation.primary = inputTrue ∧
        tracePredicate negationCircuit.program valuation = true ∧
        valuation.trace negationCircuit.outputGate = true)
  rw [traceEquivalence negationCircuit inputTrue]
  decide

example : constantTrueCircuit.Satisfiable :=
  ⟨zeroInput, rfl⟩

example :
    ∃ valuation : CarrierValuation 0 1,
      tracePredicate constantTrueProgram valuation = true ∧
      valuation.trace fin1Zero = true := by
  exact (satisfiable_iff_trace_extension constantTrueCircuit).mp
    ⟨zeroInput, rfl⟩

def malformedNegationTrace : CarrierValuation 1 1 :=
  { primary := inputFalse
    trace := fun _ => false
    occurrence := fun _ => false
    sourceLock := fun _ => true
    traceLock := fun _ => true
    finalLock := true }

def unlockedNegationTrace : CarrierValuation 1 1 :=
  { primary := inputFalse
    trace := fun _ => true
    occurrence := fun _ => false
    sourceLock := fun _ => false
    traceLock := fun _ => true
    finalLock := true }

example :
    tracePredicate negationProgram malformedNegationTrace = false := by
  rfl

example :
    tracePredicate negationProgram unlockedNegationTrace = false := by
  rfl

example :
    ∀ valuation : CarrierValuation 2 2,
      tracePredicate conjunctionProgram valuation = true →
      valuation.trace fin2One =
        conjunctionProgram.eval valuation.primary fin2One := by
  intro valuation accepted
  exact trace_sound_of_predicate_true conjunctionProgram valuation
    accepted fin2One

end PNP.DirectWire.LockedNANDTraceRegression
