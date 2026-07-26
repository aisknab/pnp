/-
Copyright (c) 2026 PNP Labs.

Answer-independent assembly of the complete exposed baseline and four-gate
extension from Section 17 of the pinned legacy manuscript.  The construction
is indexed by an intrinsically topological NAND circuit and uses the exact
`X ⊔ T ⊔ O ⊔ R ⊔ L ⊔ {z}` carrier from `LockedNANDCarrierTrace`.

This file constructs the two typed candidates required by the conditional
threshold boundary and proves their structural and semantic interface.  It
does not prove global `BaselineDistinct`, either conditional final-output law,
the locked-NAND threshold, a bitstring encoder, or polynomial runtime.
-/

import PNP.LockedNANDCarrierTrace
import PNP.LockedNANDThresholdBoundary
import PNP.NANDComposition

namespace PNP
namespace DirectWire
namespace LockedNANDGlobalCandidates

open LockedNANDTrace

/-! ## Flat carrier interface -/

/-- Flatten the six tagged carrier families into the exact contiguous input
layout used by a direct-wire candidate. -/
def flattenCarrier {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates) :
    Valuation (carrierWidth inputs gates) :=
  fun slot =>
    match decodeCarrierSlot slot with
    | .primary index => valuation.primary index
    | .trace index => valuation.trace index
    | .occurrence index => valuation.occurrence index
    | .sourceLock index => valuation.sourceLock index
    | .traceLock index => valuation.traceLock index
    | .finalLock => valuation.finalLock

/-- Recover the six tagged carrier families from a flat direct-wire input. -/
def unflattenCarrier {inputs gates : Nat}
    (valuation : Valuation (carrierWidth inputs gates)) :
    CarrierValuation inputs gates :=
  { primary := fun index => valuation (primarySlot index)
    trace := fun index => valuation (traceSlot index)
    occurrence := fun index => valuation (occurrenceSlot index)
    sourceLock := fun index => valuation (sourceLockSlot index)
    traceLock := fun index => valuation (traceLockSlot index)
    finalLock := valuation (finalLockSlot inputs gates) }

@[simp] theorem flattenCarrier_primary {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates) (index : Fin inputs) :
    flattenCarrier valuation (primarySlot (gates := gates) index) =
      valuation.primary index := by
  simp [flattenCarrier]

@[simp] theorem flattenCarrier_trace {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates) (index : Fin gates) :
    flattenCarrier valuation (traceSlot (inputs := inputs) index) =
      valuation.trace index := by
  simp [flattenCarrier]

@[simp] theorem flattenCarrier_occurrence {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates)
    (index : Fin (2 * gates)) :
    flattenCarrier valuation (occurrenceSlot (inputs := inputs) index) =
      valuation.occurrence index := by
  simp [flattenCarrier]

@[simp] theorem flattenCarrier_sourceLock {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates)
    (index : Fin (2 * gates)) :
    flattenCarrier valuation (sourceLockSlot (inputs := inputs) index) =
      valuation.sourceLock index := by
  simp [flattenCarrier]

@[simp] theorem flattenCarrier_traceLock {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates) (index : Fin gates) :
    flattenCarrier valuation (traceLockSlot (inputs := inputs) index) =
      valuation.traceLock index := by
  simp [flattenCarrier]

@[simp] theorem flattenCarrier_finalLock {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates) :
    flattenCarrier valuation (finalLockSlot inputs gates) =
      valuation.finalLock := by
  simp [flattenCarrier]

theorem unflatten_flatten {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates) :
    unflattenCarrier (flattenCarrier valuation) = valuation := by
  apply CarrierValuation.ext
  · funext index
    exact flattenCarrier_primary valuation index
  · funext index
    exact flattenCarrier_trace valuation index
  · funext index
    exact flattenCarrier_occurrence valuation index
  · funext index
    exact flattenCarrier_sourceLock valuation index
  · funext index
    exact flattenCarrier_traceLock valuation index
  · exact flattenCarrier_finalLock valuation

theorem flatten_unflatten {inputs gates : Nat}
    (valuation : Valuation (carrierWidth inputs gates)) :
    flattenCarrier (unflattenCarrier valuation) = valuation := by
  funext slot
  rw [← encode_decode slot]
  cases decoded : decodeCarrierSlot slot <;>
    simp [flattenCarrier, unflattenCarrier, CarrierSlot.encode]

/-! ## Restriction to an initial topological gate segment -/

/-- Restrict a carrier valuation to the first `smaller` gate coordinates. -/
def restrictCarrier {inputs smaller larger : Nat}
    (within : smaller ≤ larger)
    (valuation : CarrierValuation inputs larger) :
    CarrierValuation inputs smaller :=
  { primary := valuation.primary
    trace := fun index => valuation.trace (Fin.castLE within index)
    occurrence := fun index =>
      valuation.occurrence (Fin.castLE (by omega) index)
    sourceLock := fun index =>
      valuation.sourceLock (Fin.castLE (by omega) index)
    traceLock := fun index => valuation.traceLock (Fin.castLE within index)
    finalLock := valuation.finalLock }

@[simp] theorem restrictCarrier_primary {inputs smaller larger : Nat}
    (within : smaller ≤ larger)
    (valuation : CarrierValuation inputs larger) :
    (restrictCarrier within valuation).primary = valuation.primary := rfl

@[simp] theorem restrictCarrier_trace {inputs smaller larger : Nat}
    (within : smaller ≤ larger)
    (valuation : CarrierValuation inputs larger) (index : Fin smaller) :
    (restrictCarrier within valuation).trace index =
      valuation.trace (Fin.castLE within index) := rfl

@[simp] theorem restrictCarrier_occurrenceAt
    {inputs smaller larger : Nat}
    (within : smaller ≤ larger)
    (valuation : CarrierValuation inputs larger)
    (gate : Fin smaller) (side : OccurrenceSide) :
    (restrictCarrier within valuation).occurrenceAt gate side =
      valuation.occurrenceAt (Fin.castLE within gate) side := by
  unfold restrictCarrier CarrierValuation.occurrenceAt
  apply congrArg valuation.occurrence
  apply Fin.ext
  cases side <;> rfl

@[simp] theorem restrictCarrier_sourceLockAt
    {inputs smaller larger : Nat}
    (within : smaller ≤ larger)
    (valuation : CarrierValuation inputs larger)
    (gate : Fin smaller) (side : OccurrenceSide) :
    (restrictCarrier within valuation).sourceLockAt gate side =
      valuation.sourceLockAt (Fin.castLE within gate) side := by
  unfold restrictCarrier CarrierValuation.sourceLockAt
  apply congrArg valuation.sourceLock
  apply Fin.ext
  cases side <;> rfl

@[simp] theorem restrictCarrier_traceLock
    {inputs smaller larger : Nat}
    (within : smaller ≤ larger)
    (valuation : CarrierValuation inputs larger) (gate : Fin smaller) :
    (restrictCarrier within valuation).traceLock gate =
      valuation.traceLock (Fin.castLE within gate) := rfl

theorem restrictCarrier_refl {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates) :
    restrictCarrier (Nat.le_refl gates) valuation = valuation := by
  apply CarrierValuation.ext
  · rfl
  · funext index
    rfl
  · funext index
    rfl
  · funext index
    rfl
  · funext index
    rfl
  · rfl

theorem restrictCarrier_snoc_restrict
    {inputs gates larger : Nat}
    (within : gates + 1 ≤ larger)
    (valuation : CarrierValuation inputs larger) :
    (restrictCarrier within valuation).restrict =
      restrictCarrier (Nat.le_trans (Nat.le_succ gates) within) valuation := by
  apply CarrierValuation.ext
  · rfl
  · funext index
    rfl
  · funext index
    rfl
  · funext index
    rfl
  · funext index
    rfl
  · rfl

/-! ## Source-derived macro counts -/

/-- Exact number of exposed gates in the source macro selected by one typed
source occurrence. -/
def sourceMacroGateCount {inputs gates : Nat} :
    Source inputs gates → Nat
  | .input _ => 10
  | .constant false => 3
  | .constant true => 2
  | .gate _ => 10

theorem sourceMacroGateCount_eq_weighted_occurrenceCounts
    {inputs gates : Nat} (source : Source inputs gates) :
    sourceMacroGateCount source =
      10 * source.occurrenceCounts.equality +
        3 * source.occurrenceCounts.zero +
        2 * source.occurrenceCounts.one := by
  cases source with
  | input _ => rfl
  | constant value => cases value <;> rfl
  | gate _ => rfl

/-- Macro gates before the prefix tree, in canonical topological order:
left source, right source, then trace macro for each circuit gate. -/
def macroGateCount {inputs : Nat} :
    {gates : Nat} → Program inputs gates → Nat
  | 0, .empty => 0
  | _ + 1, .snoc initial gate =>
      ((macroGateCount initial + sourceMacroGateCount gate.left) +
          sourceMacroGateCount gate.right) + 18

theorem macroGateCount_report_formula
    {inputs gates : Nat} (program : Program inputs gates) :
    macroGateCount program =
      18 * gates +
        10 * program.sourceCounts.equality +
        3 * program.sourceCounts.zero +
        2 * program.sourceCounts.one := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      rw [macroGateCount, ih,
        sourceMacroGateCount_eq_weighted_occurrenceCounts,
        sourceMacroGateCount_eq_weighted_occurrenceCounts]
      simp only [Program.sourceCounts, Gate.sourceCounts,
        SourceOccurrenceCounts.add]
      omega

/-! ## Small bindings and generic block append -/

private def binding2 {alpha : Type} (first second : alpha) :
    Fin 2 → alpha :=
  fun index => if index.val = 0 then first else second

private def binding3 {alpha : Type} (first second third : alpha) :
    Fin 3 → alpha :=
  fun index =>
    if index.val = 0 then first
    else if index.val = 1 then second
    else third

private def binding4 {alpha : Type} (first second third fourth : alpha) :
    Fin 4 → alpha :=
  fun index =>
    if index.val = 0 then first
    else if index.val = 1 then second
    else if index.val = 2 then third
    else fourth

private def appendCandidateProgram
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (candidate : Candidate innerInputs suffixGates outputs) :
    Program outerInputs (prefixGates + suffixGates) :=
  sequentialProgram initial ⟨binding⟩ candidate.program

private def appendCandidateSource
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (candidate : Candidate innerInputs suffixGates outputs)
    (output : Fin outputs) :
    Source outerInputs (prefixGates + suffixGates) :=
  (candidate.directWireWord.source output).substituteInputs binding

private theorem appendCandidateSource_semantics
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (candidate : Candidate innerInputs suffixGates outputs)
    (input : Valuation outerInputs) (output : Fin outputs) :
    (appendCandidateSource binding candidate output).eval input
        ((appendCandidateProgram initial binding candidate).eval input) =
      candidate.semantics
        (fun index => (binding index).eval input (initial.eval input))
        output := by
  exact sequential_semantics initial ⟨binding⟩ candidate.program
    candidate.directWireWord input output

private theorem appendCandidate_preserves_source
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (candidate : Candidate innerInputs suffixGates outputs)
    (input : Valuation outerInputs)
    (source : Source outerInputs prefixGates) :
    (source.weakenGates suffixGates).eval input
        ((appendCandidateProgram initial binding candidate).eval input) =
      source.eval input (initial.eval input) := by
  unfold appendCandidateProgram sequentialProgram
  rw [Source.eval_weakenGates]
  apply source.eval_congr
  · intro index
    rfl
  · intro gate
    exact Program.eval_appendSubstituted_prefix initial binding
      candidate.program input gate

private theorem appendCandidate_preserves_sources
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (candidate : Candidate innerInputs suffixGates outputs)
    (input : Valuation outerInputs)
    (sources : List (Source outerInputs prefixGates)) :
    (sources.map fun source => source.weakenGates suffixGates).map
        (fun source =>
          source.eval input
            ((appendCandidateProgram initial binding candidate).eval input)) =
      sources.map (fun source => source.eval input (initial.eval input)) := by
  induction sources with
  | nil => rfl
  | cons source tail ih =>
      simp only [List.map_cons]
      rw [appendCandidate_preserves_source initial binding candidate, ih]

private def checkSourceValues
    {inputs gates : Nat} (program : Program inputs gates)
    (checks : List (Source inputs gates)) (input : Valuation inputs) :
    List Bool :=
  checks.map fun source => source.eval input (program.eval input)

/-! ## Selected macro blocks -/

private structure SourceMacroAppend
    (outerInputs prefixGates extraGates : Nat) where
  program : Program outerInputs (prefixGates + extraGates)
  check : Source outerInputs (prefixGates + extraGates)

private def appendSourceMacro
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide) :
    SourceMacroAppend (carrierWidth inputs totalGates) prefixGates
      (sourceMacroGateCount source) :=
  let occurrenceCoordinate := occurrenceCoordinate gate side
  let lock : Source (carrierWidth inputs totalGates) prefixGates :=
    .input (sourceLockSlot occurrenceCoordinate)
  let occurrence : Source (carrierWidth inputs totalGates) prefixGates :=
    .input (occurrenceSlot occurrenceCoordinate)
  match source with
  | .input index =>
      let sourceValue : Source (carrierWidth inputs totalGates) prefixGates :=
        .input (primarySlot (gates := totalGates) index)
      let binding := binding3 lock occurrence sourceValue
      { program := appendCandidateProgram initial binding equalityDirect
        check := appendCandidateSource binding equalityDirect
          ⟨7, by decide⟩ }
  | .constant false =>
      let binding := binding2 lock occurrence
      { program := appendCandidateProgram initial binding constantZeroDirect
        check := appendCandidateSource binding constantZeroDirect
          ⟨2, by decide⟩ }
  | .constant true =>
      let binding := binding2 lock occurrence
      { program := appendCandidateProgram initial binding constantOneDirect
        check := appendCandidateSource binding constantOneDirect
          ⟨1, by decide⟩ }
  | .gate index =>
      let sourceValue : Source (carrierWidth inputs totalGates) prefixGates :=
        .input (traceSlot (inputs := inputs) (Fin.castLE priorWithin index))
      let binding := binding3 lock occurrence sourceValue
      { program := appendCandidateProgram initial binding equalityDirect
        check := appendCandidateSource binding equalityDirect
          ⟨7, by decide⟩ }

private theorem appendSourceMacro_check_semantics
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide)
    (input : Valuation (carrierWidth inputs totalGates)) :
    let appended :=
      appendSourceMacro initial source priorWithin gate side
    appended.check.eval input (appended.program.eval input) =
      sourceCheck source
        ((unflattenCarrier input).sourceLockAt gate side)
        ((unflattenCarrier input).occurrenceAt gate side)
        (unflattenCarrier input).primary
        (fun index =>
          (unflattenCarrier input).trace (Fin.castLE priorWithin index)) := by
  cases source with
  | input index =>
      dsimp [appendSourceMacro, sourceCheck]
      simp only [sourceMacroGateCount]
      rw [appendCandidateSource_semantics]
      rw [equalityDirect_semantics]
      rfl
  | constant value =>
      cases value with
      | false =>
          dsimp [appendSourceMacro, sourceCheck]
          simp only [sourceMacroGateCount]
          rw [appendCandidateSource_semantics]
          rw [constantZeroDirect_semantics]
          rfl
      | true =>
          dsimp [appendSourceMacro, sourceCheck]
          simp only [sourceMacroGateCount]
          rw [appendCandidateSource_semantics]
          rw [constantOneDirect_semantics]
          rfl
  | gate index =>
      dsimp [appendSourceMacro, sourceCheck]
      simp only [sourceMacroGateCount]
      rw [appendCandidateSource_semantics]
      rw [equalityDirect_semantics]
      rfl

private theorem appendSourceMacro_preserves_source
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide)
    (input : Valuation (carrierWidth inputs totalGates))
    (old : Source (carrierWidth inputs totalGates) prefixGates) :
    let appended :=
      appendSourceMacro initial source priorWithin gate side
    (old.weakenGates (sourceMacroGateCount source)).eval input
        (appended.program.eval input) =
      old.eval input (initial.eval input) := by
  cases source with
  | input index =>
      change
        (old.weakenGates 10).eval input
            ((appendCandidateProgram initial
              (binding3
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side)))
                (.input (primarySlot (gates := totalGates) index)))
              equalityDirect).eval input) =
          old.eval input (initial.eval input)
      exact appendCandidate_preserves_source initial
          (binding3
            (.input (sourceLockSlot (occurrenceCoordinate gate side)))
            (.input (occurrenceSlot (occurrenceCoordinate gate side)))
            (.input (primarySlot (gates := totalGates) index)))
          equalityDirect input old
  | constant value =>
      cases value with
      | false =>
          change
            (old.weakenGates 3).eval input
                ((appendCandidateProgram initial
                  (binding2
                    (.input (sourceLockSlot
                      (occurrenceCoordinate gate side)))
                    (.input (occurrenceSlot
                      (occurrenceCoordinate gate side))))
                  constantZeroDirect).eval input) =
              old.eval input (initial.eval input)
          exact appendCandidate_preserves_source initial
              (binding2
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side))))
              constantZeroDirect input old
      | true =>
          change
            (old.weakenGates 2).eval input
                ((appendCandidateProgram initial
                  (binding2
                    (.input (sourceLockSlot
                      (occurrenceCoordinate gate side)))
                    (.input (occurrenceSlot
                      (occurrenceCoordinate gate side))))
                  constantOneDirect).eval input) =
              old.eval input (initial.eval input)
          exact appendCandidate_preserves_source initial
              (binding2
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side))))
              constantOneDirect input old
  | gate index =>
      change
        (old.weakenGates 10).eval input
            ((appendCandidateProgram initial
              (binding3
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side)))
                (.input (traceSlot (inputs := inputs)
                  (Fin.castLE priorWithin index))))
              equalityDirect).eval input) =
          old.eval input (initial.eval input)
      exact appendCandidate_preserves_source initial
          (binding3
            (.input (sourceLockSlot (occurrenceCoordinate gate side)))
            (.input (occurrenceSlot (occurrenceCoordinate gate side)))
            (.input (traceSlot (inputs := inputs)
              (Fin.castLE priorWithin index))))
          equalityDirect input old

private theorem appendSourceMacro_preserves_sources
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide)
    (input : Valuation (carrierWidth inputs totalGates))
    (old : List (Source (carrierWidth inputs totalGates) prefixGates)) :
    let appended :=
      appendSourceMacro initial source priorWithin gate side
    checkSourceValues appended.program
        (old.map fun item =>
          item.weakenGates (sourceMacroGateCount source)) input =
      checkSourceValues initial old input := by
  cases source with
  | input index =>
      change
        checkSourceValues
            (appendCandidateProgram initial
              (binding3
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side)))
                (.input (primarySlot (gates := totalGates) index)))
              equalityDirect)
            (old.map fun item => item.weakenGates 10) input =
          checkSourceValues initial old input
      simpa only [checkSourceValues] using
        appendCandidate_preserves_sources initial
          (binding3
            (.input (sourceLockSlot (occurrenceCoordinate gate side)))
            (.input (occurrenceSlot (occurrenceCoordinate gate side)))
            (.input (primarySlot (gates := totalGates) index)))
          equalityDirect input old
  | constant value =>
      cases value with
      | false =>
          change
            checkSourceValues
                (appendCandidateProgram initial
                  (binding2
                    (.input (sourceLockSlot
                      (occurrenceCoordinate gate side)))
                    (.input (occurrenceSlot
                      (occurrenceCoordinate gate side))))
                  constantZeroDirect)
                (old.map fun item => item.weakenGates 3) input =
              checkSourceValues initial old input
          simpa only [checkSourceValues] using
            appendCandidate_preserves_sources initial
              (binding2
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side))))
              constantZeroDirect input old
      | true =>
          change
            checkSourceValues
                (appendCandidateProgram initial
                  (binding2
                    (.input (sourceLockSlot
                      (occurrenceCoordinate gate side)))
                    (.input (occurrenceSlot
                      (occurrenceCoordinate gate side))))
                  constantOneDirect)
                (old.map fun item => item.weakenGates 2) input =
              checkSourceValues initial old input
          simpa only [checkSourceValues] using
            appendCandidate_preserves_sources initial
              (binding2
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side))))
              constantOneDirect input old
  | gate index =>
      change
        checkSourceValues
            (appendCandidateProgram initial
              (binding3
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side)))
                (.input (traceSlot (inputs := inputs)
                  (Fin.castLE priorWithin index))))
              equalityDirect)
            (old.map fun item => item.weakenGates 10) input =
          checkSourceValues initial old input
      simpa only [checkSourceValues] using
        appendCandidate_preserves_sources initial
          (binding3
            (.input (sourceLockSlot (occurrenceCoordinate gate side)))
            (.input (occurrenceSlot (occurrenceCoordinate gate side)))
            (.input (traceSlot (inputs := inputs)
              (Fin.castLE priorWithin index))))
          equalityDirect input old

private structure TraceMacroAppend
    (outerInputs prefixGates : Nat) where
  program : Program outerInputs (prefixGates + 18)
  check : Source outerInputs (prefixGates + 18)

private def appendTraceMacro
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates) :
    TraceMacroAppend (carrierWidth inputs totalGates) prefixGates :=
  let leftCoordinate := occurrenceCoordinate gate .left
  let rightCoordinate := occurrenceCoordinate gate .right
  let binding : Fin 4 →
      Source (carrierWidth inputs totalGates) prefixGates :=
    binding4
      (.input (traceLockSlot (inputs := inputs) gate))
      (.input (traceSlot (inputs := inputs) gate))
      (.input (occurrenceSlot (inputs := inputs) leftCoordinate))
      (.input (occurrenceSlot (inputs := inputs) rightCoordinate))
  { program := appendCandidateProgram initial binding traceDirect
    check := appendCandidateSource binding traceDirect ⟨15, by decide⟩ }

private theorem appendTraceMacro_check_semantics
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates)
    (input : Valuation (carrierWidth inputs totalGates)) :
    let appended := appendTraceMacro initial gate
    appended.check.eval input (appended.program.eval input) =
      traceCheck
        ((unflattenCarrier input).traceLock gate)
        ((unflattenCarrier input).trace gate)
        ((unflattenCarrier input).occurrenceAt gate .left)
        ((unflattenCarrier input).occurrenceAt gate .right) := by
  dsimp [appendTraceMacro, traceCheck]
  rw [appendCandidateSource_semantics]
  rw [traceDirect_semantics]
  rfl

private theorem appendTraceMacro_preserves_source
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates)
    (input : Valuation (carrierWidth inputs totalGates))
    (old : Source (carrierWidth inputs totalGates) prefixGates) :
    let appended := appendTraceMacro initial gate
    (old.weakenGates 18).eval input (appended.program.eval input) =
      old.eval input (initial.eval input) := by
  simpa [appendTraceMacro] using
    appendCandidate_preserves_source initial
      (binding4
        (.input (traceLockSlot (inputs := inputs) gate))
        (.input (traceSlot (inputs := inputs) gate))
        (.input (occurrenceSlot (inputs := inputs)
          (occurrenceCoordinate gate .left)))
        (.input (occurrenceSlot (inputs := inputs)
          (occurrenceCoordinate gate .right))))
      traceDirect input old

private theorem appendTraceMacro_preserves_sources
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates)
    (input : Valuation (carrierWidth inputs totalGates))
    (old : List (Source (carrierWidth inputs totalGates) prefixGates)) :
    let appended := appendTraceMacro initial gate
    checkSourceValues appended.program
        (old.map fun item => item.weakenGates 18) input =
      checkSourceValues initial old input := by
  simpa [appendTraceMacro, checkSourceValues] using
    appendCandidate_preserves_sources initial
      (binding4
        (.input (traceLockSlot (inputs := inputs) gate))
        (.input (traceSlot (inputs := inputs) gate))
        (.input (occurrenceSlot (inputs := inputs)
          (occurrenceCoordinate gate .left)))
        (.input (occurrenceSlot (inputs := inputs)
          (occurrenceCoordinate gate .right))))
      traceDirect input old

/-! ## Macro assembly over an arbitrary finite typed program -/

private structure MacroAssembly
    (carrierInputs gateCount : Nat) where
  program : Program carrierInputs gateCount
  checks : List (Source carrierInputs gateCount)

private def macroAssembly
    {inputs gates totalGates : Nat}
    (program : Program inputs gates)
    (within : gates ≤ totalGates) :
    MacroAssembly (carrierWidth inputs totalGates)
      (macroGateCount program) :=
  match program with
  | .empty =>
      { program := .empty
        checks := [] }
  | @Program.snoc _ gates initial gate =>
      let earlierWithin : gates ≤ totalGates :=
        Nat.le_trans (Nat.le_succ gates) within
      let coordinate : Fin totalGates :=
        Fin.castLE within (Fin.last gates)
      let earlier := macroAssembly initial earlierWithin
      let left := appendSourceMacro earlier.program gate.left
        earlierWithin coordinate .left
      let right := appendSourceMacro left.program gate.right
        earlierWithin coordinate .right
      let trace := appendTraceMacro right.program coordinate
      let earlierChecks :=
        ((earlier.checks.map fun source =>
            source.weakenGates (sourceMacroGateCount gate.left)).map
          fun source => source.weakenGates
            (sourceMacroGateCount gate.right)).map
          fun source => source.weakenGates 18
      let leftCheck :=
        (left.check.weakenGates
          (sourceMacroGateCount gate.right)).weakenGates 18
      let rightCheck := right.check.weakenGates 18
      { program := trace.program
        checks := earlierChecks ++ [leftCheck, rightCheck, trace.check] }

private theorem macroAssembly_checks_length
    {inputs gates totalGates : Nat}
    (program : Program inputs gates) (within : gates ≤ totalGates) :
    (macroAssembly program within).checks.length = 3 * gates := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      let earlierWithin : gates ≤ totalGates :=
        Nat.le_trans (Nat.le_succ gates) within
      let earlier := macroAssembly initial earlierWithin
      let earlierChecks :=
        ((earlier.checks.map fun source =>
            source.weakenGates (sourceMacroGateCount gate.left)).map
          fun source =>
            source.weakenGates (sourceMacroGateCount gate.right)).map
          fun source => source.weakenGates 18
      have earlierLength : earlier.checks.length = 3 * gates := by
        exact ih earlierWithin
      have earlierChecksLength :
          earlierChecks.length = 3 * gates := by
        simp [earlierChecks, earlierLength]
      change
        (earlierChecks ++ [_, _, _]).length = 3 * (gates + 1)
      simp only [List.length_append, List.length_cons,
        List.length_nil, earlierChecksLength]
      omega

private theorem macroAssembly_check_values
    {inputs gates totalGates : Nat}
    (program : Program inputs gates) (within : gates ≤ totalGates)
    (input : Valuation (carrierWidth inputs totalGates)) :
    checkSourceValues (macroAssembly program within).program
        (macroAssembly program within).checks input =
      distinguishedChecks program
        (restrictCarrier within (unflattenCarrier input)) := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      let earlierWithin : gates ≤ totalGates :=
        Nat.le_trans (Nat.le_succ gates) within
      let coordinate : Fin totalGates :=
        Fin.castLE within (Fin.last gates)
      let earlier := macroAssembly initial earlierWithin
      let left := appendSourceMacro earlier.program gate.left
        earlierWithin coordinate .left
      let right := appendSourceMacro left.program gate.right
        earlierWithin coordinate .right
      let trace := appendTraceMacro right.program coordinate
      let earlierChecks :=
        ((earlier.checks.map fun source =>
            source.weakenGates (sourceMacroGateCount gate.left)).map
          fun source =>
            source.weakenGates (sourceMacroGateCount gate.right)).map
          fun source => source.weakenGates 18
      let leftCheck :=
        (left.check.weakenGates
          (sourceMacroGateCount gate.right)).weakenGates 18
      let rightCheck := right.check.weakenGates 18
      have earlierValues :
          checkSourceValues earlier.program earlier.checks input =
            distinguishedChecks initial
              (restrictCarrier earlierWithin
                (unflattenCarrier input)) := by
        exact ih earlierWithin
      have afterLeft :
          checkSourceValues left.program
              (earlier.checks.map fun source =>
                source.weakenGates
                  (sourceMacroGateCount gate.left)) input =
            checkSourceValues earlier.program earlier.checks input := by
        exact appendSourceMacro_preserves_sources earlier.program gate.left
          earlierWithin coordinate .left input earlier.checks
      have afterRight :
          checkSourceValues right.program
              ((earlier.checks.map fun source =>
                  source.weakenGates
                    (sourceMacroGateCount gate.left)).map
                fun source => source.weakenGates
                  (sourceMacroGateCount gate.right)) input =
            checkSourceValues left.program
              (earlier.checks.map fun source =>
                source.weakenGates
                  (sourceMacroGateCount gate.left)) input := by
        exact appendSourceMacro_preserves_sources left.program gate.right
          earlierWithin coordinate .right input
          (earlier.checks.map fun source =>
            source.weakenGates (sourceMacroGateCount gate.left))
      have afterTrace :
          checkSourceValues trace.program
              (((earlier.checks.map fun source =>
                    source.weakenGates
                      (sourceMacroGateCount gate.left)).map
                  fun source => source.weakenGates
                    (sourceMacroGateCount gate.right)).map
                fun source => source.weakenGates 18) input =
            checkSourceValues right.program
              ((earlier.checks.map fun source =>
                  source.weakenGates
                    (sourceMacroGateCount gate.left)).map
                fun source => source.weakenGates
                  (sourceMacroGateCount gate.right)) input := by
        exact appendTraceMacro_preserves_sources right.program coordinate
          input _
      have afterTrace' :
          checkSourceValues trace.program earlierChecks input =
            checkSourceValues right.program
              ((earlier.checks.map fun source =>
                  source.weakenGates
                    (sourceMacroGateCount gate.left)).map
                fun source => source.weakenGates
                  (sourceMacroGateCount gate.right)) input := by
        exact afterTrace
      have leftValue :
          leftCheck.eval input (trace.program.eval input) =
            sourceCheck gate.left
              ((unflattenCarrier input).sourceLockAt coordinate .left)
              ((unflattenCarrier input).occurrenceAt coordinate .left)
              (unflattenCarrier input).primary
              (fun index =>
                (unflattenCarrier input).trace
                  (Fin.castLE earlierWithin index)) := by
        calc
          leftCheck.eval input (trace.program.eval input) =
              (left.check.weakenGates
                (sourceMacroGateCount gate.right)).eval input
                (right.program.eval input) := by
                  exact appendTraceMacro_preserves_source right.program
                    coordinate input _
          _ = left.check.eval input (left.program.eval input) := by
                exact appendSourceMacro_preserves_source left.program
                  gate.right earlierWithin coordinate .right input left.check
          _ = _ := appendSourceMacro_check_semantics earlier.program
                gate.left earlierWithin coordinate .left input
      have rightValue :
          rightCheck.eval input (trace.program.eval input) =
            sourceCheck gate.right
              ((unflattenCarrier input).sourceLockAt coordinate .right)
              ((unflattenCarrier input).occurrenceAt coordinate .right)
              (unflattenCarrier input).primary
              (fun index =>
                (unflattenCarrier input).trace
                  (Fin.castLE earlierWithin index)) := by
        calc
          rightCheck.eval input (trace.program.eval input) =
              right.check.eval input (right.program.eval input) := by
                exact appendTraceMacro_preserves_source right.program
                  coordinate input right.check
          _ = _ := appendSourceMacro_check_semantics left.program
                gate.right earlierWithin coordinate .right input
      have traceValue :
          trace.check.eval input (trace.program.eval input) =
            traceCheck
              ((unflattenCarrier input).traceLock coordinate)
              ((unflattenCarrier input).trace coordinate)
              ((unflattenCarrier input).occurrenceAt coordinate .left)
              ((unflattenCarrier input).occurrenceAt coordinate .right) :=
        appendTraceMacro_check_semantics right.program coordinate input
      change
        checkSourceValues trace.program
            (earlierChecks ++ [leftCheck, rightCheck, trace.check]) input =
          distinguishedChecks (initial.snoc gate)
            (restrictCarrier within (unflattenCarrier input))
      rw [checkSourceValues, List.map_append]
      simp only [List.map_cons, List.map_nil]
      change
        checkSourceValues trace.program earlierChecks input ++
            [leftCheck.eval input (trace.program.eval input),
             rightCheck.eval input (trace.program.eval input),
             trace.check.eval input (trace.program.eval input)] =
          distinguishedChecks (initial.snoc gate)
            (restrictCarrier within (unflattenCarrier input))
      rw [afterTrace', afterRight, afterLeft, earlierValues]
      rw [leftValue, rightValue, traceValue]
      rw [distinguishedChecks, restrictCarrier_snoc_restrict]
      unfold gateChecks
      rfl

/-! ## The exact nonempty prefix-conjunction program -/

private structure NonemptyPrefixAssembly (tailChecks : Nat) where
  program : Program (tailChecks + 1) (2 * tailChecks)
  output : Source (tailChecks + 1) (2 * tailChecks)

/-- A uniform two-gate left fold over one initial check and `tailChecks`
additional checks.  The newest input is inserted at the front; conjunction
commutativity makes this order immaterial while keeping the recursion
intrinsically typed. -/
private def nonemptyPrefixAssembly :
    (tailChecks : Nat) → NonemptyPrefixAssembly tailChecks
  | 0 =>
      { program := .empty
        output := .input fin1Zero }
  | tailChecks + 1 =>
      let earlier := nonemptyPrefixAssembly tailChecks
      let renamedProgram := earlier.program.renameInputs Fin.succ
      let renamedOutput := earlier.output.renameInputs Fin.succ
      let newest : Source ((tailChecks + 1) + 1) (2 * tailChecks) :=
        .input ⟨0, by omega⟩
      let binding := binding2 renamedOutput newest
      { program :=
          appendCandidateProgram renamedProgram binding prefixAndDirect
        output :=
          appendCandidateSource binding prefixAndDirect ⟨1, by decide⟩ }

/-- The standalone nonempty prefix candidate exposes its final conjunction
wire and uses exactly two gates per check after the first. -/
def nonemptyPrefixCandidate (tailChecks : Nat) :
    Candidate (tailChecks + 1) (2 * tailChecks) 1 :=
  let assembly := nonemptyPrefixAssembly tailChecks
  Candidate.ofDirectWireWord assembly.program
    ⟨fun _ => assembly.output⟩

theorem nonemptyPrefixCandidate_size (tailChecks : Nat) :
    (nonemptyPrefixCandidate tailChecks).program.size =
      2 * tailChecks := by
  exact Program.size_eq_gateCount _

theorem nonemptyPrefixCandidate_output_source (tailChecks : Nat) :
    (nonemptyPrefixCandidate tailChecks).directWireWord.source fin1Zero =
      (nonemptyPrefixAssembly tailChecks).output := by
  unfold nonemptyPrefixCandidate
  rw [Candidate.ofDirectWireWord_pointwise]

private theorem prefixConjunction_cons_comm (head : Bool)
    (tail : List Bool) :
    prefixConjunction (head :: tail) =
      (prefixConjunction tail && head) := by
  rw [prefixConjunction_spec, prefixConjunction_spec]
  simp only [allChecks]
  exact Bool.and_comm head (allChecks tail)

theorem nonemptyPrefixCandidate_semantics (tailChecks : Nat)
    (input : Valuation (tailChecks + 1)) :
    (nonemptyPrefixCandidate tailChecks).semantics input fin1Zero =
      prefixConjunction (List.ofFn input) := by
  induction tailChecks with
  | zero =>
      unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
      rw [nonemptyPrefixCandidate_output_source]
      change
        (nonemptyPrefixAssembly 0).output.eval input
            ((nonemptyPrefixAssembly 0).program.eval input) =
          prefixConjunction (List.ofFn input)
      simp [nonemptyPrefixAssembly, List.ofFn_succ, prefixConjunction]
      rfl
  | succ tailChecks ih =>
      unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
      rw [nonemptyPrefixCandidate_output_source]
      change
        (nonemptyPrefixAssembly (tailChecks + 1)).output.eval input
            ((nonemptyPrefixAssembly (tailChecks + 1)).program.eval input) =
          prefixConjunction (List.ofFn input)
      dsimp [nonemptyPrefixAssembly]
      rw [appendCandidateSource_semantics]
      rw [prefixAndDirect_semantics]
      change
        (prefixAndMacro
          ((binding2
              ((nonemptyPrefixAssembly tailChecks).output.renameInputs
                Fin.succ)
              (Source.input ⟨0, by omega⟩) fin2Zero).eval input
            (((nonemptyPrefixAssembly tailChecks).program.renameInputs
              Fin.succ).eval input))
          ((binding2
              ((nonemptyPrefixAssembly tailChecks).output.renameInputs
                Fin.succ)
              (Source.input ⟨0, by omega⟩) fin2One).eval input
            (((nonemptyPrefixAssembly tailChecks).program.renameInputs
              Fin.succ).eval input))).out =
          prefixConjunction (List.ofFn input)
      rw [prefixAndMacro_out_spec]
      have earlierValue :
          ((nonemptyPrefixAssembly tailChecks).output.renameInputs
              Fin.succ).eval input
              (((nonemptyPrefixAssembly tailChecks).program.renameInputs
                Fin.succ).eval input) =
            prefixConjunction
              (List.ofFn fun index : Fin (tailChecks + 1) =>
                input index.succ) := by
        rw [Source.eval_renameInputs]
        have gateValues :
            ∀ gate,
              ((nonemptyPrefixAssembly tailChecks).program.renameInputs
                  Fin.succ).eval input gate =
                (nonemptyPrefixAssembly tailChecks).program.eval
                  (fun index => input index.succ) gate := by
          intro gate
          exact Program.eval_renameInputs _ Fin.succ input gate
        rw [(nonemptyPrefixAssembly tailChecks).output.eval_congr
          (fun _ => rfl) gateValues]
        have old := ih (fun index => input index.succ)
        unfold Candidate.semantics DirectWire.semantics
          DirectWireWord.eval at old
        rw [nonemptyPrefixCandidate_output_source] at old
        change
          (nonemptyPrefixAssembly tailChecks).output.eval
              (fun index => input index.succ)
              ((nonemptyPrefixAssembly tailChecks).program.eval
                fun index => input index.succ) =
            prefixConjunction
              (List.ofFn fun index : Fin (tailChecks + 1) =>
                input index.succ) at old
        exact old
      have firstValue :
          (binding2
              ((nonemptyPrefixAssembly tailChecks).output.renameInputs
                Fin.succ)
              (Source.input ⟨0, by omega⟩) fin2Zero).eval input
            (((nonemptyPrefixAssembly tailChecks).program.renameInputs
              Fin.succ).eval input) =
            ((nonemptyPrefixAssembly tailChecks).output.renameInputs
              Fin.succ).eval input
              (((nonemptyPrefixAssembly tailChecks).program.renameInputs
                Fin.succ).eval input) := by
        rfl
      have secondValue :
          (binding2
              ((nonemptyPrefixAssembly tailChecks).output.renameInputs
                Fin.succ)
              (Source.input ⟨0, by omega⟩) fin2One).eval input
            (((nonemptyPrefixAssembly tailChecks).program.renameInputs
              Fin.succ).eval input) =
            input ⟨0, by omega⟩ := by
        rfl
      rw [firstValue, secondValue]
      rw [earlierValue]
      have inputList :
          List.ofFn input =
            input ⟨0, by omega⟩ ::
              List.ofFn (fun index : Fin (tailChecks + 1) =>
                input index.succ) := by
        exact List.ofFn_succ
      rw [inputList, prefixConjunction_cons_comm]

/-! ## Circuit-indexed macro and prefix composition -/

/-- Number of checks after the first in the nonempty locked trace list. -/
def checkTailCount {inputs : Nat} (circuit : Circuit inputs) : Nat :=
  3 * circuit.gateCount - 1

theorem checkTailCount_add_one {inputs : Nat} (circuit : Circuit inputs) :
    checkTailCount circuit + 1 = 3 * circuit.gateCount := by
  unfold checkTailCount
  have nonempty : 0 < circuit.gateCount :=
    Nat.zero_lt_of_lt circuit.outputGate.isLt
  omega

private theorem list_ofFn_finCast {left right : Nat}
    (equal : left = right) (valuation : Valuation right) :
    List.ofFn (fun index : Fin left => valuation (Fin.cast equal index)) =
      List.ofFn valuation := by
  cases equal
  rfl

/-- The exact prefix candidate specialized to the circuit's `3m`
distinguished checks. -/
def circuitPrefixCandidate {inputs : Nat} (circuit : Circuit inputs) :
    Candidate (3 * circuit.gateCount) (2 * checkTailCount circuit) 1 :=
  (nonemptyPrefixCandidate (checkTailCount circuit)).renameInputs
    (fun index => Fin.cast (checkTailCount_add_one circuit) index)

theorem circuitPrefixCandidate_size {inputs : Nat}
    (circuit : Circuit inputs) :
    (circuitPrefixCandidate circuit).program.size =
      2 * checkTailCount circuit := by
  exact Program.size_eq_gateCount _

theorem circuitPrefixCandidate_semantics {inputs : Nat}
    (circuit : Circuit inputs)
    (input : Valuation (3 * circuit.gateCount)) :
    (circuitPrefixCandidate circuit).semantics input fin1Zero =
      prefixConjunction (List.ofFn input) := by
  rw [circuitPrefixCandidate, Candidate.renameInputs_semantics]
  rw [nonemptyPrefixCandidate_semantics]
  exact congrArg prefixConjunction
    (list_ofFn_finCast (checkTailCount_add_one circuit) input)

private def macroCheckSource {inputs : Nat} (circuit : Circuit inputs)
    (index : Fin (3 * circuit.gateCount)) :
    Source (carrierWidth inputs circuit.gateCount)
      (macroGateCount circuit.program) :=
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  let lengthEqual :
      assembly.checks.length = 3 * circuit.gateCount :=
    macroAssembly_checks_length circuit.program
      (Nat.le_refl circuit.gateCount)
  assembly.checks.get (Fin.cast lengthEqual.symm index)

private theorem list_ofFn_get_map
    {alpha beta : Type} (items : List alpha) (mapValue : alpha → beta) :
    List.ofFn (fun index : Fin items.length =>
      mapValue (items.get index)) = items.map mapValue := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.ofFn_succ]
      simp only [List.map_cons]
      congr

private theorem list_ofFn_get_cast_map
    {alpha beta : Type} (items : List alpha) (count : Nat)
    (lengthEqual : items.length = count) (mapValue : alpha → beta) :
    List.ofFn (fun index : Fin count =>
      mapValue (items.get (Fin.cast lengthEqual.symm index))) =
        items.map mapValue := by
  cases lengthEqual
  exact list_ofFn_get_map items mapValue

private theorem macroCheckSource_values {inputs : Nat}
    (circuit : Circuit inputs)
    (input : Valuation (carrierWidth inputs circuit.gateCount)) :
    let assembly :=
      macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
    List.ofFn (fun index =>
        (macroCheckSource circuit index).eval input
          (assembly.program.eval input)) =
      checkSourceValues assembly.program assembly.checks input := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  let mapValue :
      Source (carrierWidth inputs circuit.gateCount)
          (macroGateCount circuit.program) → Bool :=
    fun source => source.eval input (assembly.program.eval input)
  let lengthEqual :
      assembly.checks.length = 3 * circuit.gateCount :=
    macroAssembly_checks_length circuit.program
      (Nat.le_refl circuit.gateCount)
  change
    List.ofFn (fun index : Fin (3 * circuit.gateCount) =>
      mapValue
        (assembly.checks.get (Fin.cast lengthEqual.symm index))) =
      assembly.checks.map mapValue
  exact list_ofFn_get_cast_map assembly.checks
    (3 * circuit.gateCount) lengthEqual mapValue

/-- Exact gate count before transport to the manuscript's baseline
coordinate. -/
def rawBaselineGateCount {inputs : Nat} (circuit : Circuit inputs) : Nat :=
  macroGateCount circuit.program + 2 * checkTailCount circuit

/-- Compose all selected source/trace macros with the exact prefix fold. -/
def rawBaselineProgram {inputs : Nat} (circuit : Circuit inputs) :
    Program (carrierWidth inputs circuit.gateCount)
      (rawBaselineGateCount circuit) :=
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  appendCandidateProgram assembly.program (macroCheckSource circuit)
    (circuitPrefixCandidate circuit)

/-- The final prefix-conjunction wire before the gate-count transport. -/
def rawBaselinePrefixSource {inputs : Nat} (circuit : Circuit inputs) :
    Source (carrierWidth inputs circuit.gateCount)
      (rawBaselineGateCount circuit) :=
  appendCandidateSource (macroCheckSource circuit)
    (circuitPrefixCandidate circuit) fin1Zero

theorem rawBaselinePrefixSource_semantics {inputs : Nat}
    (circuit : Circuit inputs)
    (input : Valuation (carrierWidth inputs circuit.gateCount)) :
    (rawBaselinePrefixSource circuit).eval input
        ((rawBaselineProgram circuit).eval input) =
      tracePredicate circuit.program (unflattenCarrier input) := by
  dsimp only [rawBaselinePrefixSource, rawBaselineProgram,
    rawBaselineGateCount]
  rw [appendCandidateSource_semantics]
  rw [circuitPrefixCandidate_semantics]
  rw [macroCheckSource_values]
  rw [macroAssembly_check_values]
  rw [restrictCarrier_refl]
  rfl

theorem rawBaselineGateCount_eq_lockedBaselineCount {inputs : Nat}
    (circuit : Circuit inputs) :
    rawBaselineGateCount circuit =
      lockedBaselineCount circuit.program := by
  rw [rawBaselineGateCount, macroGateCount_report_formula]
  rw [lockedBaselineCount_report_formula]
  rfl

private def castProgramGateCount {inputs left right : Nat}
    (equal : left = right) (program : Program inputs left) :
    Program inputs right :=
  equal ▸ program

private def castSourceGateCount {inputs left right : Nat}
    (equal : left = right) (source : Source inputs left) :
    Source inputs right :=
  equal ▸ source

private theorem castSourceGateCount_semantics
    {inputs left right : Nat} (equal : left = right)
    (program : Program inputs left) (source : Source inputs left)
    (input : Valuation inputs) :
    (castSourceGateCount equal source).eval input
        ((castProgramGateCount equal program).eval input) =
      source.eval input (program.eval input) := by
  cases equal
  rfl

/-! ## The exact baseline and four-gate extension -/

/-- The complete report baseline program with its index transported to the
source-derived `lockedBaselineCount`. -/
def baselineProgram {inputs : Nat} (circuit : Circuit inputs) :
    Program (carrierWidth inputs circuit.gateCount)
      (lockedBaselineCount circuit.program) :=
  castProgramGateCount
    (rawBaselineGateCount_eq_lockedBaselineCount circuit)
    (rawBaselineProgram circuit)

/-- The transported final prefix-conjunction wire inside the exact baseline. -/
def baselinePrefixSource {inputs : Nat} (circuit : Circuit inputs) :
    Source (carrierWidth inputs circuit.gateCount)
      (lockedBaselineCount circuit.program) :=
  castSourceGateCount
    (rawBaselineGateCount_eq_lockedBaselineCount circuit)
    (rawBaselinePrefixSource circuit)

/-- The complete square baseline exposes every macro and prefix gate in exact
construction order. -/
def baselineCandidate {inputs : Nat} (circuit : Circuit inputs) :
    Candidate (carrierWidth inputs circuit.gateCount)
      (lockedBaselineCount circuit.program)
      (lockedBaselineCount circuit.program) :=
  exposeAllGates (baselineProgram circuit)

theorem baselineCandidate_size {inputs : Nat}
    (circuit : Circuit inputs) :
    (baselineCandidate circuit).program.size =
      lockedBaselineCount circuit.program := by
  exact Program.size_eq_gateCount _

theorem baselineCandidate_output_source {inputs : Nat}
    (circuit : Circuit inputs)
    (output : Fin (lockedBaselineCount circuit.program)) :
    (baselineCandidate circuit).directWireWord.source output =
      .gate output :=
  exposeAllGates_source (baselineProgram circuit) output

theorem baselinePrefixSource_semantics {inputs : Nat}
    (circuit : Circuit inputs)
    (input : Valuation (carrierWidth inputs circuit.gateCount)) :
    (baselinePrefixSource circuit).eval input
        ((baselineProgram circuit).eval input) =
      tracePredicate circuit.program (unflattenCarrier input) := by
  rw [baselinePrefixSource, baselineProgram,
    castSourceGateCount_semantics]
  exact rawBaselinePrefixSource_semantics circuit input

private def finalBinding {inputs : Nat} (circuit : Circuit inputs) :
    Fin 3 → Source (carrierWidth inputs circuit.gateCount)
      (lockedBaselineCount circuit.program) :=
  binding3
    (.input (finalLockSlot inputs circuit.gateCount))
    (baselinePrefixSource circuit)
    (.input (traceSlot (inputs := inputs) circuit.outputGate))

/-- Append the manuscript's final four-gate conjunction to the exact
baseline. -/
def fullProgram {inputs : Nat} (circuit : Circuit inputs) :
    Program (carrierWidth inputs circuit.gateCount)
      (lockedBaselineCount circuit.program + 4) :=
  appendCandidateProgram (baselineProgram circuit) (finalBinding circuit)
    finalConjunctionDirect

/-- Expose the complete baseline tuple followed by the one new final
coordinate. -/
def fullCandidate {inputs : Nat} (circuit : Circuit inputs) :
    Candidate (carrierWidth inputs circuit.gateCount)
      (lockedBaselineCount circuit.program + 4)
      (lockedBaselineCount circuit.program + 1) :=
  Candidate.ofDirectWireWord (fullProgram circuit)
    ⟨splitFin
      (fun output =>
        (Source.gate output).weakenGates 4)
      (fun _ =>
        appendCandidateSource (finalBinding circuit)
          finalConjunctionDirect fin1Zero)⟩

theorem fullCandidate_size {inputs : Nat} (circuit : Circuit inputs) :
    (fullCandidate circuit).program.size =
      lockedBaselineCount circuit.program + 4 := by
  exact Program.size_eq_gateCount _

theorem fullCandidate_initial_source {inputs : Nat}
    (circuit : Circuit inputs)
    (output : Fin (lockedBaselineCount circuit.program)) :
    (fullCandidate circuit).directWireWord.source
        (baselineOutputEmbedding output) =
      (Source.gate output).weakenGates 4 := by
  unfold fullCandidate
  rw [Candidate.ofDirectWireWord_pointwise]
  change
    splitFin
        (fun output =>
          Source.weakenGates 4 (Source.gate output))
        (fun _ =>
          appendCandidateSource (finalBinding circuit)
            finalConjunctionDirect fin1Zero)
        (Fin.castAdd 1 output) =
      Source.weakenGates 4 (Source.gate output)
  exact splitFin_left _ _ output

theorem fullCandidate_final_source {inputs : Nat}
    (circuit : Circuit inputs) :
    (fullCandidate circuit).directWireWord.source
        (conditionalFinalOutput
          (lockedBaselineCount circuit.program)) =
      appendCandidateSource (finalBinding circuit)
        finalConjunctionDirect fin1Zero := by
  unfold fullCandidate
  rw [Candidate.ofDirectWireWord_pointwise]
  change
    splitFin
        (fun output =>
          Source.weakenGates 4 (Source.gate output))
        (fun _ =>
          appendCandidateSource (finalBinding circuit)
            finalConjunctionDirect fin1Zero)
        (Fin.natAdd (lockedBaselineCount circuit.program) fin1Zero) =
      appendCandidateSource (finalBinding circuit)
        finalConjunctionDirect fin1Zero
  exact splitFin_right _ _ fin1Zero

theorem fullCandidate_initial_semantics {inputs : Nat}
    (circuit : Circuit inputs)
    (input : Valuation (carrierWidth inputs circuit.gateCount))
    (output : Fin (lockedBaselineCount circuit.program)) :
    (fullCandidate circuit).semantics input
        (baselineOutputEmbedding output) =
      (baselineCandidate circuit).semantics input output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [fullCandidate_initial_source, baselineCandidate_output_source]
  exact appendCandidate_preserves_source (baselineProgram circuit)
    (finalBinding circuit) finalConjunctionDirect input (.gate output)

theorem fullCandidate_final_semantics {inputs : Nat}
    (circuit : Circuit inputs)
    (input : Valuation (carrierWidth inputs circuit.gateCount)) :
    (fullCandidate circuit).semantics input
        (conditionalFinalOutput
          (lockedBaselineCount circuit.program)) =
      finalConjunction4
        (input (finalLockSlot inputs circuit.gateCount))
        (tracePredicate circuit.program (unflattenCarrier input))
        (input (traceSlot (inputs := inputs) circuit.outputGate)) := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [fullCandidate_final_source]
  change
    (appendCandidateSource (finalBinding circuit)
        finalConjunctionDirect fin1Zero).eval input
        ((fullProgram circuit).eval input) =
      finalConjunction4
        (input (finalLockSlot inputs circuit.gateCount))
        (tracePredicate circuit.program (unflattenCarrier input))
        (input (traceSlot (inputs := inputs) circuit.outputGate))
  rw [fullProgram]
  rw [appendCandidateSource_semantics]
  rw [finalConjunctionDirect_semantics]
  have first :
      (finalBinding circuit ⟨0, by decide⟩).eval input
          ((baselineProgram circuit).eval input) =
        input (finalLockSlot inputs circuit.gateCount) := by
    rfl
  have second :
      (finalBinding circuit ⟨1, by decide⟩).eval input
          ((baselineProgram circuit).eval input) =
        tracePredicate circuit.program (unflattenCarrier input) := by
    exact baselinePrefixSource_semantics circuit input
  have third :
      (finalBinding circuit ⟨2, by decide⟩).eval input
          ((baselineProgram circuit).eval input) =
        input (traceSlot (inputs := inputs) circuit.outputGate) := by
    rfl
  rw [first, second, third]

theorem fullCandidate_final_semantics_conjunction {inputs : Nat}
    (circuit : Circuit inputs)
    (input : Valuation (carrierWidth inputs circuit.gateCount)) :
    (fullCandidate circuit).semantics input
        (conditionalFinalOutput
          (lockedBaselineCount circuit.program)) =
      (input (finalLockSlot inputs circuit.gateCount) &&
        tracePredicate circuit.program (unflattenCarrier input) &&
        input (traceSlot (inputs := inputs) circuit.outputGate)) := by
  rw [fullCandidate_final_semantics, finalConjunction4_spec]

theorem fullCandidate_final_semantics_flatten {inputs : Nat}
    (circuit : Circuit inputs)
    (valuation : CarrierValuation inputs circuit.gateCount) :
    (fullCandidate circuit).semantics (flattenCarrier valuation)
        (conditionalFinalOutput
          (lockedBaselineCount circuit.program)) =
      finalConjunction4 valuation.finalLock
        (tracePredicate circuit.program valuation)
        (valuation.trace circuit.outputGate) := by
  rw [fullCandidate_final_semantics]
  rw [flattenCarrier_finalLock, flattenCarrier_trace, unflatten_flatten]

/-! ## Constant-free structural boundary -/

private theorem source_hasNoConstant_weakenGates
    {inputs gates : Nat} (source : Source inputs gates) (extra : Nat) :
    (source.weakenGates extra).hasNoConstant = source.hasNoConstant := by
  cases source <;> rfl

private theorem source_hasNoConstant_renameInputs
    {fromInputs toInputs gates : Nat}
    (source : Source fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs) :
    (source.renameInputs rename).hasNoConstant =
      source.hasNoConstant := by
  cases source <;> rfl

private theorem source_hasNoConstant_substituteInputs
    {innerInputs outerInputs prefixGates suffixGates : Nat}
    (source : Source innerInputs suffixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingNoConstants :
      ∀ index, (binding index).hasNoConstant = true) :
    (source.substituteInputs binding).hasNoConstant =
      source.hasNoConstant := by
  cases source with
  | input index =>
      rw [Source.substituteInputs, source_hasNoConstant_weakenGates,
        bindingNoConstants]
      rfl
  | constant value => rfl
  | gate index => rfl

private theorem gate_hasNoConstant_renameInputs
    {fromInputs toInputs gates : Nat}
    (gate : Gate fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs) :
    (gate.renameInputs rename).hasNoConstant = gate.hasNoConstant := by
  unfold Gate.renameInputs Gate.hasNoConstant
  rw [source_hasNoConstant_renameInputs,
    source_hasNoConstant_renameInputs]

private theorem gate_hasNoConstant_substituteInputs
    {innerInputs outerInputs prefixGates suffixGates : Nat}
    (gate : Gate innerInputs suffixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingNoConstants :
      ∀ index, (binding index).hasNoConstant = true) :
    (gate.substituteInputs binding).hasNoConstant =
      gate.hasNoConstant := by
  unfold Gate.substituteInputs Gate.hasNoConstant
  rw [source_hasNoConstant_substituteInputs _ binding bindingNoConstants,
    source_hasNoConstant_substituteInputs _ binding bindingNoConstants]

private theorem program_hasNoConstant_renameInputs
    {fromInputs toInputs gates : Nat}
    (program : Program fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs) :
    (program.renameInputs rename).hasNoConstant =
      program.hasNoConstant := by
  induction program with
  | empty => rfl
  | snoc initial gate ih =>
      unfold Program.renameInputs Program.hasNoConstant
      rw [ih, gate_hasNoConstant_renameInputs]

private theorem program_hasNoConstant_appendSubstituted
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingNoConstants :
      ∀ index, (binding index).hasNoConstant = true)
    (suffix : Program innerInputs suffixGates)
    (initialNoConstants : initial.hasNoConstant = true)
    (suffixNoConstants : suffix.hasNoConstant = true) :
    (initial.appendSubstituted binding suffix).hasNoConstant = true := by
  induction suffix with
  | empty =>
      simpa [Program.appendSubstituted] using initialNoConstants
  | snoc earlier gate ih =>
      have parts :
          earlier.hasNoConstant = true ∧
            gate.hasNoConstant = true := by
        simpa [Program.hasNoConstant, Bool.and_eq_true] using
          suffixNoConstants
      unfold Program.appendSubstituted Program.hasNoConstant
      rw [ih parts.1]
      rw [gate_hasNoConstant_substituteInputs _ binding
        bindingNoConstants, parts.2]
      rfl

private theorem appendCandidateProgram_hasNoConstant
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingNoConstants :
      ∀ index, (binding index).hasNoConstant = true)
    (candidate : Candidate innerInputs suffixGates outputs)
    (initialNoConstants : initial.hasNoConstant = true)
    (candidateNoConstants : candidate.program.hasNoConstant = true) :
    (appendCandidateProgram initial binding candidate).hasNoConstant =
      true := by
  unfold appendCandidateProgram sequentialProgram
  exact program_hasNoConstant_appendSubstituted initial binding
    bindingNoConstants candidate.program initialNoConstants
      candidateNoConstants

private theorem appendCandidateSource_hasNoConstant
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingNoConstants :
      ∀ index, (binding index).hasNoConstant = true)
    (candidate : Candidate innerInputs suffixGates outputs)
    (output : Fin outputs) :
    (appendCandidateSource binding candidate output).hasNoConstant =
      (candidate.directWireWord.source output).hasNoConstant := by
  unfold appendCandidateSource
  exact source_hasNoConstant_substituteInputs
    (candidate.directWireWord.source output) binding bindingNoConstants

private theorem list_all_hasNoConstant_map_weaken
    {inputs gates : Nat} (sources : List (Source inputs gates))
    (extra : Nat) :
    (sources.map fun source => source.weakenGates extra).all
        (fun source => source.hasNoConstant) =
      sources.all (fun source => source.hasNoConstant) := by
  induction sources with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.all_cons]
      rw [source_hasNoConstant_weakenGates, ih]

private theorem appendSourceMacro_noConstants
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide)
    (initialNoConstants : initial.hasNoConstant = true) :
    let appended :=
      appendSourceMacro initial source priorWithin gate side
    appended.program.hasNoConstant = true ∧
      appended.check.hasNoConstant = true := by
  cases source with
  | input index =>
      simp only [sourceMacroGateCount]
      constructor
      · rw [show (appendSourceMacro initial (.input index) priorWithin
            gate side).program =
          appendCandidateProgram initial
            (binding3
              (.input (sourceLockSlot (occurrenceCoordinate gate side)))
              (.input (occurrenceSlot (occurrenceCoordinate gate side)))
              (.input (primarySlot (gates := totalGates) index)))
            equalityDirect from rfl]
        apply appendCandidateProgram_hasNoConstant
        · intro bindingIndex
          unfold binding3
          split
          · rfl
          · split <;> rfl
        · exact initialNoConstants
        · exact equalityDirect_no_internal_constants
      · rw [show (appendSourceMacro initial (.input index) priorWithin
            gate side).check =
          appendCandidateSource
            (binding3
              (.input (sourceLockSlot (occurrenceCoordinate gate side)))
              (.input (occurrenceSlot (occurrenceCoordinate gate side)))
              (.input (primarySlot (gates := totalGates) index)))
            equalityDirect ⟨7, by decide⟩ from rfl]
        rw [appendCandidateSource_hasNoConstant]
        · change true = true
          rfl
        · intro bindingIndex
          unfold binding3
          split
          · rfl
          · split <;> rfl
  | constant value =>
      cases value with
      | false =>
          simp only [sourceMacroGateCount]
          constructor
          · rw [show
                (appendSourceMacro initial (.constant false) priorWithin
                  gate side).program =
                appendCandidateProgram initial
                  (binding2
                    (.input (sourceLockSlot
                      (occurrenceCoordinate gate side)))
                    (.input (occurrenceSlot
                      (occurrenceCoordinate gate side))))
                  constantZeroDirect from rfl]
            apply appendCandidateProgram_hasNoConstant
            · intro bindingIndex
              unfold binding2
              split <;> rfl
            · exact initialNoConstants
            · exact constantZeroDirect_no_internal_constants
          · rw [show
                (appendSourceMacro initial (.constant false) priorWithin
                  gate side).check =
                appendCandidateSource
                  (binding2
                    (.input (sourceLockSlot
                      (occurrenceCoordinate gate side)))
                    (.input (occurrenceSlot
                      (occurrenceCoordinate gate side))))
                  constantZeroDirect ⟨2, by decide⟩ from rfl]
            rw [appendCandidateSource_hasNoConstant]
            · change true = true
              rfl
            · intro bindingIndex
              unfold binding2
              split <;> rfl
      | true =>
          simp only [sourceMacroGateCount]
          constructor
          · rw [show
                (appendSourceMacro initial (.constant true) priorWithin
                  gate side).program =
                appendCandidateProgram initial
                  (binding2
                    (.input (sourceLockSlot
                      (occurrenceCoordinate gate side)))
                    (.input (occurrenceSlot
                      (occurrenceCoordinate gate side))))
                  constantOneDirect from rfl]
            apply appendCandidateProgram_hasNoConstant
            · intro bindingIndex
              unfold binding2
              split <;> rfl
            · exact initialNoConstants
            · exact constantOneDirect_no_internal_constants
          · rw [show
                (appendSourceMacro initial (.constant true) priorWithin
                  gate side).check =
                appendCandidateSource
                  (binding2
                    (.input (sourceLockSlot
                      (occurrenceCoordinate gate side)))
                    (.input (occurrenceSlot
                      (occurrenceCoordinate gate side))))
                  constantOneDirect ⟨1, by decide⟩ from rfl]
            rw [appendCandidateSource_hasNoConstant]
            · change true = true
              rfl
            · intro bindingIndex
              unfold binding2
              split <;> rfl
  | gate index =>
      simp only [sourceMacroGateCount]
      constructor
      · rw [show
            (appendSourceMacro initial (.gate index) priorWithin
              gate side).program =
            appendCandidateProgram initial
              (binding3
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side)))
                (.input (traceSlot (inputs := inputs)
                  (Fin.castLE priorWithin index))))
              equalityDirect from rfl]
        apply appendCandidateProgram_hasNoConstant
        · intro bindingIndex
          unfold binding3
          split
          · rfl
          · split <;> rfl
        · exact initialNoConstants
        · exact equalityDirect_no_internal_constants
      · rw [show
            (appendSourceMacro initial (.gate index) priorWithin
              gate side).check =
            appendCandidateSource
              (binding3
                (.input (sourceLockSlot (occurrenceCoordinate gate side)))
                (.input (occurrenceSlot (occurrenceCoordinate gate side)))
                (.input (traceSlot (inputs := inputs)
                  (Fin.castLE priorWithin index))))
              equalityDirect ⟨7, by decide⟩ from rfl]
        rw [appendCandidateSource_hasNoConstant]
        · change true = true
          rfl
        · intro bindingIndex
          unfold binding3
          split
          · rfl
          · split <;> rfl

private theorem appendTraceMacro_noConstants
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates)
    (initialNoConstants : initial.hasNoConstant = true) :
    let appended := appendTraceMacro initial gate
    appended.program.hasNoConstant = true ∧
      appended.check.hasNoConstant = true := by
  constructor
  · rw [show (appendTraceMacro initial gate).program =
        appendCandidateProgram initial
          (binding4
            (.input (traceLockSlot (inputs := inputs) gate))
            (.input (traceSlot (inputs := inputs) gate))
            (.input (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate .left)))
            (.input (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate .right))))
          traceDirect from rfl]
    apply appendCandidateProgram_hasNoConstant
    · intro bindingIndex
      unfold binding4
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
    · exact initialNoConstants
    · exact traceDirect_no_internal_constants
  · rw [show (appendTraceMacro initial gate).check =
        appendCandidateSource
          (binding4
            (.input (traceLockSlot (inputs := inputs) gate))
            (.input (traceSlot (inputs := inputs) gate))
            (.input (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate .left)))
            (.input (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate .right))))
          traceDirect ⟨15, by decide⟩ from rfl]
    rw [appendCandidateSource_hasNoConstant]
    · change true = true
      rfl
    · intro bindingIndex
      unfold binding4
      split
      · rfl
      · split
        · rfl
        · split <;> rfl

private theorem macroAssembly_noConstants
    {inputs gates totalGates : Nat}
    (program : Program inputs gates) (within : gates ≤ totalGates) :
    let assembly := macroAssembly program within
    assembly.program.hasNoConstant = true ∧
      assembly.checks.all (fun source => source.hasNoConstant) = true := by
  induction program with
  | empty =>
      constructor <;> rfl
  | @snoc gates initial gate ih =>
      let earlierWithin : gates ≤ totalGates :=
        Nat.le_trans (Nat.le_succ gates) within
      let coordinate : Fin totalGates :=
        Fin.castLE within (Fin.last gates)
      let earlier := macroAssembly initial earlierWithin
      let left := appendSourceMacro earlier.program gate.left
        earlierWithin coordinate .left
      let right := appendSourceMacro left.program gate.right
        earlierWithin coordinate .right
      let trace := appendTraceMacro right.program coordinate
      let earlierChecks :=
        ((earlier.checks.map fun source =>
            source.weakenGates (sourceMacroGateCount gate.left)).map
          fun source =>
            source.weakenGates (sourceMacroGateCount gate.right)).map
          fun source => source.weakenGates 18
      let leftCheck :=
        (left.check.weakenGates
          (sourceMacroGateCount gate.right)).weakenGates 18
      let rightCheck := right.check.weakenGates 18
      have earlierNo :
          earlier.program.hasNoConstant = true ∧
            earlier.checks.all
              (fun source => source.hasNoConstant) = true := by
        exact ih earlierWithin
      have leftNo :
          left.program.hasNoConstant = true ∧
            left.check.hasNoConstant = true :=
        appendSourceMacro_noConstants earlier.program gate.left
          earlierWithin coordinate .left earlierNo.1
      have rightNo :
          right.program.hasNoConstant = true ∧
            right.check.hasNoConstant = true :=
        appendSourceMacro_noConstants left.program gate.right
          earlierWithin coordinate .right leftNo.1
      have traceNo :
          trace.program.hasNoConstant = true ∧
            trace.check.hasNoConstant = true :=
        appendTraceMacro_noConstants right.program coordinate rightNo.1
      have earlierChecksNo :
          earlierChecks.all
              (fun source => source.hasNoConstant) = true := by
        dsimp only [earlierChecks]
        rw [list_all_hasNoConstant_map_weaken,
          list_all_hasNoConstant_map_weaken,
          list_all_hasNoConstant_map_weaken]
        exact earlierNo.2
      have leftCheckNo : leftCheck.hasNoConstant = true := by
        dsimp only [leftCheck]
        rw [source_hasNoConstant_weakenGates,
          source_hasNoConstant_weakenGates]
        exact leftNo.2
      have rightCheckNo : rightCheck.hasNoConstant = true := by
        dsimp only [rightCheck]
        rw [source_hasNoConstant_weakenGates]
        exact rightNo.2
      change
        trace.program.hasNoConstant = true ∧
          (earlierChecks ++
            [leftCheck, rightCheck, trace.check]).all
              (fun source => source.hasNoConstant) = true
      constructor
      · exact traceNo.1
      · rw [List.all_append]
        simp only [List.all_cons, List.all_nil, Bool.and_true]
        rw [earlierChecksNo, leftCheckNo, rightCheckNo, traceNo.2]
        rfl

private theorem macroCheckSource_noConstant {inputs : Nat}
    (circuit : Circuit inputs)
    (index : Fin (3 * circuit.gateCount)) :
    (macroCheckSource circuit index).hasNoConstant = true := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  let lengthEqual :
      assembly.checks.length = 3 * circuit.gateCount :=
    macroAssembly_checks_length circuit.program
      (Nat.le_refl circuit.gateCount)
  change
    (assembly.checks.get
      (Fin.cast lengthEqual.symm index)).hasNoConstant = true
  have allNo := (macroAssembly_noConstants circuit.program
    (Nat.le_refl circuit.gateCount)).2
  exact (List.all_eq_true.mp allNo) _
    (List.get_mem assembly.checks (Fin.cast lengthEqual.symm index))

private theorem nonemptyPrefixAssembly_noConstants
    (tailChecks : Nat) :
    let assembly := nonemptyPrefixAssembly tailChecks
    assembly.program.hasNoConstant = true ∧
      assembly.output.hasNoConstant = true := by
  induction tailChecks with
  | zero =>
      constructor <;> rfl
  | succ tailChecks ih =>
      let earlier := nonemptyPrefixAssembly tailChecks
      let renamedProgram := earlier.program.renameInputs Fin.succ
      let renamedOutput := earlier.output.renameInputs Fin.succ
      let newest : Source ((tailChecks + 1) + 1) (2 * tailChecks) :=
        .input ⟨0, by omega⟩
      let binding := binding2 renamedOutput newest
      have renamedProgramNo :
          renamedProgram.hasNoConstant = true := by
        dsimp only [renamedProgram]
        rw [program_hasNoConstant_renameInputs]
        exact ih.1
      have renamedOutputNo :
          renamedOutput.hasNoConstant = true := by
        dsimp only [renamedOutput]
        rw [source_hasNoConstant_renameInputs]
        exact ih.2
      have bindingNo :
          ∀ index, (binding index).hasNoConstant = true := by
        intro index
        dsimp only [binding]
        unfold binding2
        split
        · exact renamedOutputNo
        · rfl
      change
        (appendCandidateProgram renamedProgram binding
            prefixAndDirect).hasNoConstant = true ∧
          (appendCandidateSource binding prefixAndDirect
            ⟨1, by decide⟩).hasNoConstant = true
      constructor
      · exact appendCandidateProgram_hasNoConstant renamedProgram
          binding bindingNo prefixAndDirect renamedProgramNo
          prefixAndDirect_no_internal_constants
      · rw [appendCandidateSource_hasNoConstant binding bindingNo]
        change true = true
        rfl

theorem nonemptyPrefixCandidate_no_internal_constants
    (tailChecks : Nat) :
    (nonemptyPrefixCandidate tailChecks).program.hasNoConstant = true := by
  change
    (nonemptyPrefixAssembly tailChecks).program.hasNoConstant = true
  exact (nonemptyPrefixAssembly_noConstants tailChecks).1

private theorem circuitPrefixCandidate_output_noConstant
    {inputs : Nat} (circuit : Circuit inputs) :
    ((circuitPrefixCandidate circuit).directWireWord.source
        fin1Zero).hasNoConstant = true := by
  unfold circuitPrefixCandidate Candidate.renameInputs
  rw [Candidate.ofDirectWireWord_pointwise]
  unfold DirectWireWord.renameInputs
  rw [source_hasNoConstant_renameInputs]
  rw [nonemptyPrefixCandidate_output_source]
  exact (nonemptyPrefixAssembly_noConstants
    (checkTailCount circuit)).2

theorem circuitPrefixCandidate_no_internal_constants
    {inputs : Nat} (circuit : Circuit inputs) :
    (circuitPrefixCandidate circuit).program.hasNoConstant = true := by
  unfold circuitPrefixCandidate Candidate.renameInputs
  change
    ((nonemptyPrefixCandidate
      (checkTailCount circuit)).program.renameInputs _).hasNoConstant = true
  rw [program_hasNoConstant_renameInputs]
  exact nonemptyPrefixCandidate_no_internal_constants
    (checkTailCount circuit)

private theorem rawBaselineProgram_noConstants {inputs : Nat}
    (circuit : Circuit inputs) :
    (rawBaselineProgram circuit).hasNoConstant = true := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  have assemblyNo :
      assembly.program.hasNoConstant = true :=
    (macroAssembly_noConstants circuit.program
      (Nat.le_refl circuit.gateCount)).1
  dsimp only [rawBaselineProgram, rawBaselineGateCount]
  exact appendCandidateProgram_hasNoConstant assembly.program
    (macroCheckSource circuit) (macroCheckSource_noConstant circuit)
    (circuitPrefixCandidate circuit) assemblyNo
    (circuitPrefixCandidate_no_internal_constants circuit)

private theorem rawBaselinePrefixSource_noConstant {inputs : Nat}
    (circuit : Circuit inputs) :
    (rawBaselinePrefixSource circuit).hasNoConstant = true := by
  dsimp only [rawBaselinePrefixSource, rawBaselineGateCount]
  rw [appendCandidateSource_hasNoConstant
    (macroCheckSource circuit) (macroCheckSource_noConstant circuit)]
  exact circuitPrefixCandidate_output_noConstant circuit

private theorem castProgramGateCount_hasNoConstant
    {inputs left right : Nat} (equal : left = right)
    (program : Program inputs left) :
    (castProgramGateCount equal program).hasNoConstant =
      program.hasNoConstant := by
  cases equal
  rfl

private theorem castSourceGateCount_hasNoConstant
    {inputs left right : Nat} (equal : left = right)
    (source : Source inputs left) :
    (castSourceGateCount equal source).hasNoConstant =
      source.hasNoConstant := by
  cases equal
  rfl

theorem baselineCandidate_no_internal_constants {inputs : Nat}
    (circuit : Circuit inputs) :
    (baselineCandidate circuit).program.hasNoConstant = true := by
  change (baselineProgram circuit).hasNoConstant = true
  rw [baselineProgram, castProgramGateCount_hasNoConstant]
  exact rawBaselineProgram_noConstants circuit

private theorem baselinePrefixSource_noConstant {inputs : Nat}
    (circuit : Circuit inputs) :
    (baselinePrefixSource circuit).hasNoConstant = true := by
  rw [baselinePrefixSource, castSourceGateCount_hasNoConstant]
  exact rawBaselinePrefixSource_noConstant circuit

private theorem finalBinding_noConstants {inputs : Nat}
    (circuit : Circuit inputs) :
    ∀ index, (finalBinding circuit index).hasNoConstant = true := by
  intro index
  unfold finalBinding binding3
  split
  · rfl
  · split
    · exact baselinePrefixSource_noConstant circuit
    · rfl

theorem fullCandidate_no_internal_constants {inputs : Nat}
    (circuit : Circuit inputs) :
    (fullCandidate circuit).program.hasNoConstant = true := by
  change (fullProgram circuit).hasNoConstant = true
  exact appendCandidateProgram_hasNoConstant (baselineProgram circuit)
    (finalBinding circuit) (finalBinding_noConstants circuit)
    finalConjunctionDirect
    (baselineCandidate_no_internal_constants circuit)
    finalConjunctionDirect_no_internal_constants

/-! ## Baseline independence from the fresh final-lock coordinate -/

private def sourceAvoidsInput {inputs gates : Nat}
    (target : Fin inputs) : Source inputs gates → Prop
  | .input index => index ≠ target
  | .constant _ => True
  | .gate _ => True

private def gateAvoidsInput {inputs gates : Nat}
    (target : Fin inputs) (gate : Gate inputs gates) : Prop :=
  sourceAvoidsInput target gate.left ∧
    sourceAvoidsInput target gate.right

private def programAvoidsInput {inputs : Nat} (target : Fin inputs) :
    {gates : Nat} → Program inputs gates → Prop
  | _, .empty => True
  | _, .snoc initial gate =>
      programAvoidsInput target initial ∧ gateAvoidsInput target gate

private theorem sourceAvoidsInput_weakenGates
    {inputs gates : Nat} (target : Fin inputs)
    (source : Source inputs gates) (extra : Nat) :
    sourceAvoidsInput target (source.weakenGates extra) ↔
      sourceAvoidsInput target source := by
  cases source <;> rfl

private theorem sourceAvoidsInput_substituteInputs
    {innerInputs outerInputs prefixGates suffixGates : Nat}
    (target : Fin outerInputs)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingAvoids :
      ∀ index, sourceAvoidsInput target (binding index))
    (source : Source innerInputs suffixGates) :
    sourceAvoidsInput target (source.substituteInputs binding) := by
  cases source with
  | input index =>
      exact (sourceAvoidsInput_weakenGates target
        (binding index) suffixGates).2 (bindingAvoids index)
  | constant value => trivial
  | gate index => trivial

private theorem gateAvoidsInput_substituteInputs
    {innerInputs outerInputs prefixGates suffixGates : Nat}
    (target : Fin outerInputs)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingAvoids :
      ∀ index, sourceAvoidsInput target (binding index))
    (gate : Gate innerInputs suffixGates) :
    gateAvoidsInput target (gate.substituteInputs binding) := by
  constructor
  · exact sourceAvoidsInput_substituteInputs target binding
      bindingAvoids gate.left
  · exact sourceAvoidsInput_substituteInputs target binding
      bindingAvoids gate.right

private theorem programAvoidsInput_appendSubstituted
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (target : Fin outerInputs)
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingAvoids :
      ∀ index, sourceAvoidsInput target (binding index))
    (suffix : Program innerInputs suffixGates)
    (initialAvoids : programAvoidsInput target initial) :
    programAvoidsInput target
      (initial.appendSubstituted binding suffix) := by
  induction suffix with
  | empty => exact initialAvoids
  | snoc earlier gate ih =>
      exact ⟨ih, gateAvoidsInput_substituteInputs target binding
        bindingAvoids gate⟩

private theorem appendCandidateProgram_avoidsInput
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (target : Fin outerInputs)
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingAvoids :
      ∀ index, sourceAvoidsInput target (binding index))
    (candidate : Candidate innerInputs suffixGates outputs)
    (initialAvoids : programAvoidsInput target initial) :
    programAvoidsInput target
      (appendCandidateProgram initial binding candidate) := by
  exact programAvoidsInput_appendSubstituted target initial binding
    bindingAvoids candidate.program initialAvoids

private theorem appendCandidateSource_avoidsInput
    {outerInputs innerInputs prefixGates suffixGates outputs : Nat}
    (target : Fin outerInputs)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (bindingAvoids :
      ∀ index, sourceAvoidsInput target (binding index))
    (candidate : Candidate innerInputs suffixGates outputs)
    (output : Fin outputs) :
    sourceAvoidsInput target
      (appendCandidateSource binding candidate output) := by
  exact sourceAvoidsInput_substituteInputs target binding bindingAvoids
    (candidate.directWireWord.source output)

private theorem nonFinalCarrierSource_avoidsFinal
    {inputs gates prefixGates : Nat}
    (slot : CarrierSlot inputs gates) (notFinal : slot ≠ .finalLock) :
    sourceAvoidsInput (finalLockSlot inputs gates)
      (Source.input slot.encode :
        Source (carrierWidth inputs gates) prefixGates) := by
  exact finalLock_fresh slot notFinal

private theorem primarySource_avoidsFinal
    {inputs gates prefixGates : Nat} (index : Fin inputs) :
    sourceAvoidsInput (finalLockSlot inputs gates)
      (Source.input (primarySlot (gates := gates) index) :
        Source (carrierWidth inputs gates) prefixGates) := by
  simpa [CarrierSlot.encode] using
    (nonFinalCarrierSource_avoidsFinal
      (prefixGates := prefixGates)
      (CarrierSlot.primary index) (by simp))

private theorem traceSource_avoidsFinal
    {inputs gates prefixGates : Nat} (index : Fin gates) :
    sourceAvoidsInput (finalLockSlot inputs gates)
      (Source.input (traceSlot (inputs := inputs) index) :
        Source (carrierWidth inputs gates) prefixGates) := by
  simpa [CarrierSlot.encode] using
    (nonFinalCarrierSource_avoidsFinal
      (prefixGates := prefixGates)
      (CarrierSlot.trace index) (by simp))

private theorem occurrenceSource_avoidsFinal
    {inputs gates prefixGates : Nat} (index : Fin (2 * gates)) :
    sourceAvoidsInput (finalLockSlot inputs gates)
      (Source.input (occurrenceSlot (inputs := inputs) index) :
        Source (carrierWidth inputs gates) prefixGates) := by
  simpa [CarrierSlot.encode] using
    (nonFinalCarrierSource_avoidsFinal
      (prefixGates := prefixGates)
      (CarrierSlot.occurrence index) (by simp))

private theorem sourceLockSource_avoidsFinal
    {inputs gates prefixGates : Nat} (index : Fin (2 * gates)) :
    sourceAvoidsInput (finalLockSlot inputs gates)
      (Source.input (sourceLockSlot (inputs := inputs) index) :
        Source (carrierWidth inputs gates) prefixGates) := by
  simpa [CarrierSlot.encode] using
    (nonFinalCarrierSource_avoidsFinal
      (prefixGates := prefixGates)
      (CarrierSlot.sourceLock index) (by simp))

private theorem traceLockSource_avoidsFinal
    {inputs gates prefixGates : Nat} (index : Fin gates) :
    sourceAvoidsInput (finalLockSlot inputs gates)
      (Source.input (traceLockSlot (inputs := inputs) index) :
        Source (carrierWidth inputs gates) prefixGates) := by
  simpa [CarrierSlot.encode] using
    (nonFinalCarrierSource_avoidsFinal
      (prefixGates := prefixGates)
      (CarrierSlot.traceLock index) (by simp))

private theorem appendSourceMacro_avoidsFinal
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide)
    (initialAvoids :
      programAvoidsInput (finalLockSlot inputs totalGates) initial) :
    let appended :=
      appendSourceMacro initial source priorWithin gate side
    programAvoidsInput (finalLockSlot inputs totalGates)
        appended.program ∧
      sourceAvoidsInput (finalLockSlot inputs totalGates)
        appended.check := by
  cases source with
  | input index =>
      simp only [sourceMacroGateCount]
      let binding : Fin 3 →
          Source (carrierWidth inputs totalGates) prefixGates :=
        binding3
          (Source.input
            (sourceLockSlot (occurrenceCoordinate gate side)))
          (Source.input
            (occurrenceSlot (occurrenceCoordinate gate side)))
          (Source.input (primarySlot (gates := totalGates) index))
      have bindingAvoids :
          ∀ bindingIndex,
            sourceAvoidsInput (finalLockSlot inputs totalGates)
              (binding bindingIndex) := by
        intro bindingIndex
        dsimp only [binding]
        unfold binding3
        split
        · exact sourceLockSource_avoidsFinal _
        · split
          · exact occurrenceSource_avoidsFinal _
          · exact primarySource_avoidsFinal _
      change
        programAvoidsInput (finalLockSlot inputs totalGates)
            (appendCandidateProgram initial binding equalityDirect) ∧
          sourceAvoidsInput (finalLockSlot inputs totalGates)
            (appendCandidateSource binding equalityDirect
              ⟨7, by decide⟩)
      exact ⟨appendCandidateProgram_avoidsInput
          (finalLockSlot inputs totalGates) initial binding bindingAvoids
          equalityDirect initialAvoids,
        appendCandidateSource_avoidsInput
          (finalLockSlot inputs totalGates) binding bindingAvoids
          equalityDirect ⟨7, by decide⟩⟩
  | constant value =>
      cases value with
      | false =>
          simp only [sourceMacroGateCount]
          let binding : Fin 2 →
              Source (carrierWidth inputs totalGates) prefixGates :=
            binding2
              (Source.input
                (sourceLockSlot (occurrenceCoordinate gate side)))
              (Source.input
                (occurrenceSlot (occurrenceCoordinate gate side)))
          have bindingAvoids :
              ∀ bindingIndex,
                sourceAvoidsInput (finalLockSlot inputs totalGates)
                  (binding bindingIndex) := by
            intro bindingIndex
            dsimp only [binding]
            unfold binding2
            split
            · exact sourceLockSource_avoidsFinal _
            · exact occurrenceSource_avoidsFinal _
          change
            programAvoidsInput (finalLockSlot inputs totalGates)
                (appendCandidateProgram initial binding
                  constantZeroDirect) ∧
              sourceAvoidsInput (finalLockSlot inputs totalGates)
                (appendCandidateSource binding constantZeroDirect
                  ⟨2, by decide⟩)
          exact ⟨appendCandidateProgram_avoidsInput
              (finalLockSlot inputs totalGates) initial binding
              bindingAvoids constantZeroDirect initialAvoids,
            appendCandidateSource_avoidsInput
              (finalLockSlot inputs totalGates) binding bindingAvoids
              constantZeroDirect ⟨2, by decide⟩⟩
      | true =>
          simp only [sourceMacroGateCount]
          let binding : Fin 2 →
              Source (carrierWidth inputs totalGates) prefixGates :=
            binding2
              (Source.input
                (sourceLockSlot (occurrenceCoordinate gate side)))
              (Source.input
                (occurrenceSlot (occurrenceCoordinate gate side)))
          have bindingAvoids :
              ∀ bindingIndex,
                sourceAvoidsInput (finalLockSlot inputs totalGates)
                  (binding bindingIndex) := by
            intro bindingIndex
            dsimp only [binding]
            unfold binding2
            split
            · exact sourceLockSource_avoidsFinal _
            · exact occurrenceSource_avoidsFinal _
          change
            programAvoidsInput (finalLockSlot inputs totalGates)
                (appendCandidateProgram initial binding
                  constantOneDirect) ∧
              sourceAvoidsInput (finalLockSlot inputs totalGates)
                (appendCandidateSource binding constantOneDirect
                  ⟨1, by decide⟩)
          exact ⟨appendCandidateProgram_avoidsInput
              (finalLockSlot inputs totalGates) initial binding
              bindingAvoids constantOneDirect initialAvoids,
            appendCandidateSource_avoidsInput
              (finalLockSlot inputs totalGates) binding bindingAvoids
              constantOneDirect ⟨1, by decide⟩⟩
  | gate index =>
      simp only [sourceMacroGateCount]
      let binding : Fin 3 →
          Source (carrierWidth inputs totalGates) prefixGates :=
        binding3
          (Source.input
            (sourceLockSlot (occurrenceCoordinate gate side)))
          (Source.input
            (occurrenceSlot (occurrenceCoordinate gate side)))
          (Source.input (traceSlot (inputs := inputs)
            (Fin.castLE priorWithin index)))
      have bindingAvoids :
          ∀ bindingIndex,
            sourceAvoidsInput (finalLockSlot inputs totalGates)
              (binding bindingIndex) := by
        intro bindingIndex
        dsimp only [binding]
        unfold binding3
        split
        · exact sourceLockSource_avoidsFinal _
        · split
          · exact occurrenceSource_avoidsFinal _
          · exact traceSource_avoidsFinal _
      change
        programAvoidsInput (finalLockSlot inputs totalGates)
            (appendCandidateProgram initial binding equalityDirect) ∧
          sourceAvoidsInput (finalLockSlot inputs totalGates)
            (appendCandidateSource binding equalityDirect
              ⟨7, by decide⟩)
      exact ⟨appendCandidateProgram_avoidsInput
          (finalLockSlot inputs totalGates) initial binding bindingAvoids
          equalityDirect initialAvoids,
        appendCandidateSource_avoidsInput
          (finalLockSlot inputs totalGates) binding bindingAvoids
          equalityDirect ⟨7, by decide⟩⟩

private theorem appendTraceMacro_avoidsFinal
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates)
    (initialAvoids :
      programAvoidsInput (finalLockSlot inputs totalGates) initial) :
    let appended := appendTraceMacro initial gate
    programAvoidsInput (finalLockSlot inputs totalGates)
        appended.program ∧
      sourceAvoidsInput (finalLockSlot inputs totalGates)
        appended.check := by
  let binding : Fin 4 →
      Source (carrierWidth inputs totalGates) prefixGates :=
    binding4
      (Source.input (traceLockSlot (inputs := inputs) gate))
      (Source.input (traceSlot (inputs := inputs) gate))
      (Source.input (occurrenceSlot (inputs := inputs)
        (occurrenceCoordinate gate .left)))
      (Source.input (occurrenceSlot (inputs := inputs)
        (occurrenceCoordinate gate .right)))
  have bindingAvoids :
      ∀ bindingIndex,
        sourceAvoidsInput (finalLockSlot inputs totalGates)
          (binding bindingIndex) := by
    intro bindingIndex
    dsimp only [binding]
    unfold binding4
    split
    · exact traceLockSource_avoidsFinal _
    · split
      · exact traceSource_avoidsFinal _
      · split
        · exact occurrenceSource_avoidsFinal _
        · exact occurrenceSource_avoidsFinal _
  change
    programAvoidsInput (finalLockSlot inputs totalGates)
        (appendCandidateProgram initial binding traceDirect) ∧
      sourceAvoidsInput (finalLockSlot inputs totalGates)
        (appendCandidateSource binding traceDirect ⟨15, by decide⟩)
  exact ⟨appendCandidateProgram_avoidsInput
      (finalLockSlot inputs totalGates) initial binding bindingAvoids
      traceDirect initialAvoids,
    appendCandidateSource_avoidsInput
      (finalLockSlot inputs totalGates) binding bindingAvoids
      traceDirect ⟨15, by decide⟩⟩

private theorem macroAssembly_avoidsFinal
    {inputs gates totalGates : Nat}
    (program : Program inputs gates) (within : gates ≤ totalGates) :
    let assembly := macroAssembly program within
    programAvoidsInput (finalLockSlot inputs totalGates)
        assembly.program ∧
      ∀ source, source ∈ assembly.checks →
        sourceAvoidsInput (finalLockSlot inputs totalGates) source := by
  induction program with
  | empty =>
      constructor
      · trivial
      · intro source member
        simp [macroAssembly] at member
  | @snoc gates initial gate ih =>
      let earlierWithin : gates ≤ totalGates :=
        Nat.le_trans (Nat.le_succ gates) within
      let coordinate : Fin totalGates :=
        Fin.castLE within (Fin.last gates)
      let earlier := macroAssembly initial earlierWithin
      let left := appendSourceMacro earlier.program gate.left
        earlierWithin coordinate .left
      let right := appendSourceMacro left.program gate.right
        earlierWithin coordinate .right
      let trace := appendTraceMacro right.program coordinate
      let earlierChecks :=
        ((earlier.checks.map fun source =>
            source.weakenGates (sourceMacroGateCount gate.left)).map
          fun source =>
            source.weakenGates (sourceMacroGateCount gate.right)).map
          fun source => source.weakenGates 18
      let leftCheck :=
        (left.check.weakenGates
          (sourceMacroGateCount gate.right)).weakenGates 18
      let rightCheck := right.check.weakenGates 18
      have earlierAvoids :
          programAvoidsInput (finalLockSlot inputs totalGates)
              earlier.program ∧
            ∀ source, source ∈ earlier.checks →
              sourceAvoidsInput (finalLockSlot inputs totalGates)
                source := by
        exact ih earlierWithin
      have leftAvoids :
          programAvoidsInput (finalLockSlot inputs totalGates)
              left.program ∧
            sourceAvoidsInput (finalLockSlot inputs totalGates)
              left.check :=
        appendSourceMacro_avoidsFinal earlier.program gate.left
          earlierWithin coordinate .left earlierAvoids.1
      have rightAvoids :
          programAvoidsInput (finalLockSlot inputs totalGates)
              right.program ∧
            sourceAvoidsInput (finalLockSlot inputs totalGates)
              right.check :=
        appendSourceMacro_avoidsFinal left.program gate.right
          earlierWithin coordinate .right leftAvoids.1
      have traceAvoids :
          programAvoidsInput (finalLockSlot inputs totalGates)
              trace.program ∧
            sourceAvoidsInput (finalLockSlot inputs totalGates)
              trace.check :=
        appendTraceMacro_avoidsFinal right.program coordinate
          rightAvoids.1
      have earlierChecksAvoid :
          ∀ source, source ∈ earlierChecks →
            sourceAvoidsInput (finalLockSlot inputs totalGates)
              source := by
        intro source member
        dsimp only [earlierChecks] at member
        rcases List.mem_map.mp member with
          ⟨afterRight, afterRightMember, rfl⟩
        rcases List.mem_map.mp afterRightMember with
          ⟨afterLeft, afterLeftMember, rfl⟩
        rcases List.mem_map.mp afterLeftMember with
          ⟨original, originalMember, rfl⟩
        apply (sourceAvoidsInput_weakenGates
          (finalLockSlot inputs totalGates) _ 18).2
        apply (sourceAvoidsInput_weakenGates
          (finalLockSlot inputs totalGates) _
          (sourceMacroGateCount gate.right)).2
        apply (sourceAvoidsInput_weakenGates
          (finalLockSlot inputs totalGates) _
          (sourceMacroGateCount gate.left)).2
        exact earlierAvoids.2 original originalMember
      have leftCheckAvoid :
          sourceAvoidsInput (finalLockSlot inputs totalGates)
            leftCheck := by
        dsimp only [leftCheck]
        apply (sourceAvoidsInput_weakenGates
          (finalLockSlot inputs totalGates) _ 18).2
        apply (sourceAvoidsInput_weakenGates
          (finalLockSlot inputs totalGates) _
          (sourceMacroGateCount gate.right)).2
        exact leftAvoids.2
      have rightCheckAvoid :
          sourceAvoidsInput (finalLockSlot inputs totalGates)
            rightCheck := by
        dsimp only [rightCheck]
        apply (sourceAvoidsInput_weakenGates
          (finalLockSlot inputs totalGates) _ 18).2
        exact rightAvoids.2
      change
        programAvoidsInput (finalLockSlot inputs totalGates)
            trace.program ∧
          ∀ source,
            source ∈
              (earlierChecks ++
                [leftCheck, rightCheck, trace.check]) →
            sourceAvoidsInput (finalLockSlot inputs totalGates) source
      constructor
      · exact traceAvoids.1
      · intro source member
        rcases List.mem_append.mp member with
          earlierMember | newestMember
        · exact earlierChecksAvoid source earlierMember
        · simp only [List.mem_cons, List.not_mem_nil,
            or_false] at newestMember
          rcases newestMember with
            equal | equal | equal
          · subst source
            exact leftCheckAvoid
          · subst source
            exact rightCheckAvoid
          · subst source
            exact traceAvoids.2

private theorem macroCheckSource_avoidsFinal {inputs : Nat}
    (circuit : Circuit inputs)
    (index : Fin (3 * circuit.gateCount)) :
    sourceAvoidsInput (finalLockSlot inputs circuit.gateCount)
      (macroCheckSource circuit index) := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  let lengthEqual :
      assembly.checks.length = 3 * circuit.gateCount :=
    macroAssembly_checks_length circuit.program
      (Nat.le_refl circuit.gateCount)
  change
    sourceAvoidsInput (finalLockSlot inputs circuit.gateCount)
      (assembly.checks.get (Fin.cast lengthEqual.symm index))
  exact (macroAssembly_avoidsFinal circuit.program
    (Nat.le_refl circuit.gateCount)).2 _
      (List.get_mem assembly.checks (Fin.cast lengthEqual.symm index))

private theorem rawBaselineProgram_avoidsFinal {inputs : Nat}
    (circuit : Circuit inputs) :
    programAvoidsInput (finalLockSlot inputs circuit.gateCount)
      (rawBaselineProgram circuit) := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  have assemblyAvoids :
      programAvoidsInput (finalLockSlot inputs circuit.gateCount)
        assembly.program :=
    (macroAssembly_avoidsFinal circuit.program
      (Nat.le_refl circuit.gateCount)).1
  dsimp only [rawBaselineProgram, rawBaselineGateCount]
  exact appendCandidateProgram_avoidsInput
    (finalLockSlot inputs circuit.gateCount) assembly.program
    (macroCheckSource circuit) (macroCheckSource_avoidsFinal circuit)
    (circuitPrefixCandidate circuit) assemblyAvoids

private theorem castProgramGateCount_avoidsInput
    {inputs left right : Nat} (target : Fin inputs)
    (equal : left = right) (program : Program inputs left)
    (avoids : programAvoidsInput target program) :
    programAvoidsInput target (castProgramGateCount equal program) := by
  cases equal
  exact avoids

private theorem baselineProgram_avoidsFinal {inputs : Nat}
    (circuit : Circuit inputs) :
    programAvoidsInput (finalLockSlot inputs circuit.gateCount)
      (baselineProgram circuit) := by
  exact castProgramGateCount_avoidsInput
    (finalLockSlot inputs circuit.gateCount)
    (rawBaselineGateCount_eq_lockedBaselineCount circuit)
    (rawBaselineProgram circuit)
    (rawBaselineProgram_avoidsFinal circuit)

private theorem source_eval_eq_of_avoidsInput
    {inputs gates : Nat} (target : Fin inputs)
    (source : Source inputs gates)
    (avoids : sourceAvoidsInput target source)
    (leftInput rightInput : Valuation inputs)
    (inputEqual :
      ∀ index, index ≠ target → leftInput index = rightInput index)
    (leftGates rightGates : Valuation gates)
    (gatesEqual :
      ∀ index, leftGates index = rightGates index) :
    source.eval leftInput leftGates =
      source.eval rightInput rightGates := by
  cases source with
  | input index => exact inputEqual index avoids
  | constant value => rfl
  | gate index => exact gatesEqual index

private theorem gate_eval_eq_of_avoidsInput
    {inputs gates : Nat} (target : Fin inputs)
    (gate : Gate inputs gates)
    (avoids : gateAvoidsInput target gate)
    (leftInput rightInput : Valuation inputs)
    (inputEqual :
      ∀ index, index ≠ target → leftInput index = rightInput index)
    (leftGates rightGates : Valuation gates)
    (gatesEqual :
      ∀ index, leftGates index = rightGates index) :
    gate.eval leftInput leftGates =
      gate.eval rightInput rightGates := by
  unfold Gate.eval
  rw [source_eval_eq_of_avoidsInput target gate.left avoids.1
    leftInput rightInput inputEqual leftGates rightGates gatesEqual]
  rw [source_eval_eq_of_avoidsInput target gate.right avoids.2
    leftInput rightInput inputEqual leftGates rightGates gatesEqual]

private theorem program_eval_eq_of_avoidsInput
    {inputs gates : Nat} (target : Fin inputs)
    (program : Program inputs gates)
    (avoids : programAvoidsInput target program)
    (leftInput rightInput : Valuation inputs)
    (inputEqual :
      ∀ index, index ≠ target → leftInput index = rightInput index) :
    ∀ gate, program.eval leftInput gate =
      program.eval rightInput gate := by
  induction program with
  | empty =>
      intro gate
      exact Fin.elim0 gate
  | snoc initial gate ih =>
      have initialAvoids :
          programAvoidsInput target initial := avoids.1
      have gateAvoids :
          gateAvoidsInput target gate := avoids.2
      have earlierEqual :
          ∀ earlier,
            initial.eval leftInput earlier =
              initial.eval rightInput earlier :=
        ih initialAvoids
      intro coordinate
      unfold Program.eval Valuation.snoc
      split
      · exact earlierEqual _
      · exact gate_eval_eq_of_avoidsInput target gate gateAvoids
          leftInput rightInput inputEqual
          (initial.eval leftInput) (initial.eval rightInput)
          earlierEqual

/-- Replace only the globally fresh final-lock input of a flat carrier
valuation. -/
def setFinalLockValue {inputs gates : Nat}
    (input : Valuation (carrierWidth inputs gates)) (value : Bool) :
    Valuation (carrierWidth inputs gates) :=
  fun index =>
    if index = finalLockSlot inputs gates then value else input index

@[simp] theorem setFinalLockValue_final {inputs gates : Nat}
    (input : Valuation (carrierWidth inputs gates)) (value : Bool) :
    setFinalLockValue input value (finalLockSlot inputs gates) = value := by
  simp [setFinalLockValue]

theorem setFinalLockValue_nonfinal {inputs gates : Nat}
    (input : Valuation (carrierWidth inputs gates)) (value : Bool)
    (index : Fin (carrierWidth inputs gates))
    (notFinal : index ≠ finalLockSlot inputs gates) :
    setFinalLockValue input value index = input index := by
  simp [setFinalLockValue, notFinal]

/-- Every exposed baseline coordinate is independent of the fresh `z`
coordinate.  This is structural and does not assert global output
distinctness. -/
theorem baselineCandidate_finalLock_irrelevant {inputs : Nat}
    (circuit : Circuit inputs)
    (input : Valuation (carrierWidth inputs circuit.gateCount))
    (leftValue rightValue : Bool)
    (output : Fin (lockedBaselineCount circuit.program)) :
    (baselineCandidate circuit).semantics
        (setFinalLockValue input leftValue) output =
      (baselineCandidate circuit).semantics
        (setFinalLockValue input rightValue) output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [baselineCandidate_output_source]
  change
    (baselineProgram circuit).eval
        (setFinalLockValue input leftValue) output =
      (baselineProgram circuit).eval
        (setFinalLockValue input rightValue) output
  exact program_eval_eq_of_avoidsInput
    (finalLockSlot inputs circuit.gateCount)
    (baselineProgram circuit)
    (baselineProgram_avoidsFinal circuit)
    (setFinalLockValue input leftValue)
    (setFinalLockValue input rightValue)
    (fun index notFinal => by
      rw [setFinalLockValue_nonfinal _ _ index notFinal,
        setFinalLockValue_nonfinal _ _ index notFinal])
    output

end LockedNANDGlobalCandidates
end DirectWire
end PNP
