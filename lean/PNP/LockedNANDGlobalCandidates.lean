/-
Copyright (c) 2026 PNP Labs.

Answer-independent assembly of the complete exposed baseline and four-gate
extension from Section 17 of the pinned legacy manuscript.  The construction
is indexed by an intrinsically topological NAND circuit and uses the exact
`X ⊔ T ⊔ O ⊔ R ⊔ L ⊔ {z}` carrier from `LockedNANDCarrierTrace`.

This file constructs the two typed candidates required by the conditional
threshold boundary, proves their structural interface, and discharges the
global `BaselineDistinct` conditions for the square baseline.  It does not
prove either conditional final-output law, the locked-NAND threshold, a
bitstring encoder, or polynomial runtime.
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

/-- Typed structural result of appending one selected source macro. -/
structure SourceMacroAppend
    (outerInputs prefixGates extraGates : Nat) where
  program : Program outerInputs (prefixGates + extraGates)
  check : Source outerInputs (prefixGates + extraGates)

/-- Append the exact source macro selected by one typed source occurrence. -/
def appendSourceMacro
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

/-- Typed structural result of appending one trace macro. -/
structure TraceMacroAppend
    (outerInputs prefixGates : Nat) where
  program : Program outerInputs (prefixGates + 18)
  check : Source outerInputs (prefixGates + 18)

/-- Append the exact eighteen-gate trace macro. -/
def appendTraceMacro
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

/-- Typed macro program and its three ordered checks per source gate. -/
structure MacroAssembly
    (carrierInputs gateCount : Nat) where
  program : Program carrierInputs gateCount
  checks : List (Source carrierInputs gateCount)

/-- Assemble every selected source and trace macro in source-program order. -/
def macroAssembly
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

/-- Bind the ordered macro checks into the standalone prefix candidate. -/
def macroCheckSource {inputs : Nat} (circuit : Circuit inputs)
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

/-! ## Private semantic support machinery for global BaselineDistinct -/

/-- Two carrier valuations differ at one named coordinate and nowhere else. -/
private def DiffersOnlyAt {inputs : Nat} (target : Fin inputs)
    (left right : Valuation inputs) : Prop :=
  left target ≠ right target ∧
    ∀ index, index ≠ target → left index = right index

/-- One exposed output depends essentially on a named carrier coordinate. -/
private def OutputEssentialAt {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (target : Fin inputs) (output : Fin outputs) : Prop :=
  ∃ left right,
    DiffersOnlyAt target left right ∧
      candidate.semantics left output ≠
        candidate.semantics right output

/-- One exposed output is independent of a named carrier coordinate. -/
private def OutputIrrelevantAt {inputs gates outputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (target : Fin inputs) (output : Fin outputs) : Prop :=
  ∀ left right,
    (∀ index, index ≠ target → left index = right index) →
      candidate.semantics left output =
        candidate.semantics right output

/-- Boolean existential quantification over a concrete finite list. -/
private def anyTrue {alpha : Type} : List alpha → (alpha → Bool) → Bool
  | [], _ => false
  | item :: items, predicate =>
      predicate item || anyTrue items predicate

private theorem anyTrue_sound {alpha : Type} {items : List alpha}
    {predicate : alpha → Bool}
    (checked : anyTrue items predicate = true) :
    ∃ item, item ∈ items ∧ predicate item = true := by
  induction items with
  | nil =>
      exact False.elim (Bool.noConfusion checked)
  | cons head tail ih =>
      change (predicate head || anyTrue tail predicate) = true at checked
      cases headCheck : predicate head with
      | false =>
          rw [headCheck] at checked
          obtain ⟨item, member, itemCheck⟩ := ih checked
          exact ⟨item, List.Mem.tail head member, itemCheck⟩
      | true =>
          exact ⟨head, List.Mem.head _, headCheck⟩

private theorem boolNotEqual_sound (left right : Bool)
    (checked : (!boolEqual left right) = true) :
    left ≠ right := by
  cases left <;> cases right <;> simp [boolEqual] at checked ⊢

private theorem boolEqual_of_not_ne (left right : Bool)
    (notDifferent : ¬ left ≠ right) :
    left = right := by
  cases left <;> cases right <;> simp at notDifferent ⊢

/-- Executable check that two finite valuations differ at exactly one input. -/
private def differsOnlyAtBool {inputs : Nat} (target : Fin inputs)
    (left right : Valuation inputs) : Bool :=
  (!boolEqual (left target) (right target)) &&
    allTrue (allFin inputs) fun index =>
      if index = target then true
      else boolEqual (left index) (right index)

private theorem differsOnlyAtBool_sound {inputs : Nat}
    (target : Fin inputs) (left right : Valuation inputs)
    (checked : differsOnlyAtBool target left right = true) :
    DiffersOnlyAt target left right := by
  have targetCheck := boolAndTrue_left checked
  have remainingChecks := boolAndTrue_right checked
  constructor
  · exact boolNotEqual_sound _ _ targetCheck
  · intro index notTarget
    have indexCheck :=
      allTrue_sound remainingChecks (mem_allFin index)
    rw [if_neg notTarget] at indexCheck
    exact (boolEqual_eq_true_iff _ _).mp indexCheck

/-- Finite checker for essential dependence on one declared local input. -/
private def finiteOutputEssentialCheck
    {row : Type} {inputs gates outputs : Nat}
    (rows : List row) (rowValuation : row → Valuation inputs)
    (candidate : Candidate inputs gates outputs)
    (target : Fin inputs) : Bool :=
  allTrue (allFin outputs) fun output =>
    anyTrue rows fun left =>
      anyTrue rows fun right =>
        differsOnlyAtBool target (rowValuation left)
            (rowValuation right) &&
          (!boolEqual
            (candidate.semantics (rowValuation left) output)
            (candidate.semantics (rowValuation right) output))

private theorem finiteOutputEssentialCheck_sound
    {row : Type} {inputs gates outputs : Nat}
    (rows : List row) (rowValuation : row → Valuation inputs)
    (candidate : Candidate inputs gates outputs)
    (target : Fin inputs)
    (checked :
      finiteOutputEssentialCheck rows rowValuation candidate target = true) :
    ∀ output, OutputEssentialAt candidate target output := by
  intro output
  have outputCheck := allTrue_sound checked (mem_allFin output)
  obtain ⟨left, _leftMember, leftCheck⟩ := anyTrue_sound outputCheck
  obtain ⟨right, _rightMember, pairCheck⟩ := anyTrue_sound leftCheck
  have differsCheck := boolAndTrue_left pairCheck
  have semanticCheck := boolAndTrue_right pairCheck
  exact ⟨rowValuation left, rowValuation right,
    differsOnlyAtBool_sound target _ _ differsCheck,
    boolNotEqual_sound _ _ semanticCheck⟩

private theorem equalityDirect_lockEssential :
    ∀ output,
      OutputEssentialAt equalityDirect ⟨0, by decide⟩ output :=
  finiteOutputEssentialCheck_sound boolRows3 bool3RowValuation
    equalityDirect ⟨0, by decide⟩ (by decide)

private theorem constantOneDirect_lockEssential :
    ∀ output,
      OutputEssentialAt constantOneDirect fin2Zero output :=
  finiteOutputEssentialCheck_sound boolRows2 bool2RowValuation
    constantOneDirect fin2Zero (by decide)

private theorem constantZeroDirect_lockEssential :
    ∀ output,
      OutputEssentialAt constantZeroDirect fin2Zero output :=
  finiteOutputEssentialCheck_sound boolRows2 bool2RowValuation
    constantZeroDirect fin2Zero (by decide)

private theorem traceDirect_lockEssential :
    ∀ output,
      OutputEssentialAt traceDirect ⟨0, by decide⟩ output :=
  finiteOutputEssentialCheck_sound boolRows4 bool4RowValuation
    traceDirect ⟨0, by decide⟩ (by decide)

private theorem prefixAndDirect_leftEssential :
    ∀ output,
      OutputEssentialAt prefixAndDirect fin2Zero output :=
  finiteOutputEssentialCheck_sound boolRows2 bool2RowValuation
    prefixAndDirect fin2Zero (by decide)

private theorem prefixAndDirect_rightEssential :
    ∀ output,
      OutputEssentialAt prefixAndDirect fin2One output :=
  finiteOutputEssentialCheck_sound boolRows2 bool2RowValuation
    prefixAndDirect fin2One (by decide)

private theorem OutputEssentialAt.nonconstant
    {inputs gates outputs : Nat}
    {candidate : Candidate inputs gates outputs}
    {target : Fin inputs} {output : Fin outputs}
    (essential : OutputEssentialAt candidate target output) :
    OutputNonconstant candidate output := by
  obtain ⟨left, right, _differsOnly, semanticDifferent⟩ := essential
  exact ⟨left, right, semanticDifferent⟩

/-- Essential dependence away from a queried coordinate supplies a concrete
    witness that the output is not that positive projection. -/
private theorem OutputEssentialAt.notProjection_of_ne
    {inputs gates outputs : Nat}
    {candidate : Candidate inputs gates outputs}
    {target queried : Fin inputs} {output : Fin outputs}
    (essential : OutputEssentialAt candidate target output)
    (differentCoordinate : target ≠ queried) :
    ∃ valuation,
      candidate.semantics valuation output ≠ valuation queried := by
  obtain ⟨left, right, differsOnly, semanticDifferent⟩ := essential
  have queriedEqual : left queried = right queried :=
    differsOnly.2 queried (Ne.symm differentCoordinate)
  by_cases leftDifferent :
      candidate.semantics left output ≠ left queried
  · exact ⟨left, leftDifferent⟩
  · refine ⟨right, ?_⟩
    intro rightEqual
    apply semanticDifferent
    exact (boolEqual_of_not_ne _ _ leftDifferent).trans
      (queriedEqual.trans rightEqual.symm)

/-- If one function changes at a coordinate and another is independent of it,
    the two functions are semantically distinct. -/
private theorem essential_irrelevant_distinct
    {inputs leftGates rightGates leftOutputs rightOutputs : Nat}
    {left : Candidate inputs leftGates leftOutputs}
    {right : Candidate inputs rightGates rightOutputs}
    {target : Fin inputs}
    {leftOutput : Fin leftOutputs} {rightOutput : Fin rightOutputs}
    (essential : OutputEssentialAt left target leftOutput)
    (irrelevant : OutputIrrelevantAt right target rightOutput) :
    ∃ valuation,
      left.semantics valuation leftOutput ≠
        right.semantics valuation rightOutput := by
  obtain ⟨first, second, differsOnly, leftDifferent⟩ := essential
  have rightEqual :
      right.semantics first rightOutput =
        right.semantics second rightOutput :=
    irrelevant first second differsOnly.2
  by_cases firstDifferent :
      left.semantics first leftOutput ≠
        right.semantics first rightOutput
  · exact ⟨first, firstDifferent⟩
  · refine ⟨second, ?_⟩
    intro secondEqual
    apply leftDifferent
    exact (boolEqual_of_not_ne _ _ firstDifferent).trans
      (rightEqual.trans secondEqual.symm)

private theorem exposeAllGates_outputIrrelevant
    {inputs gates : Nat} (program : Program inputs gates)
    (target : Fin inputs)
    (avoids : programAvoidsInput target program)
    (output : Fin gates) :
    OutputIrrelevantAt (exposeAllGates program) target output := by
  intro left right equalAway
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [exposeAllGates_source]
  change program.eval left output = program.eval right output
  exact program_eval_eq_of_avoidsInput target program avoids
    left right equalAway output

/-- Constructive lifting data for one locally checked macro block. -/
private structure LocalBlockLift
    {outerInputs innerInputs prefixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (innerTarget : Fin innerInputs) (outerTarget : Fin outerInputs) where
  lift : Valuation innerInputs → Valuation outerInputs
  bindingValues : ∀ valuation index,
    (binding index).eval (lift valuation)
        (initial.eval (lift valuation)) =
      valuation index
  targetValue : ∀ valuation,
    lift valuation outerTarget = valuation innerTarget
  preservesDifference : ∀ left right,
    DiffersOnlyAt innerTarget left right →
      DiffersOnlyAt outerTarget (lift left) (lift right)

private def inputLift2 {outerInputs : Nat}
    (first second : Fin outerInputs) (valuation : Valuation 2) :
    Valuation outerInputs :=
  fun index =>
    if index = first then valuation fin2Zero
    else if index = second then valuation fin2One
    else false

private def inputLift3 {outerInputs : Nat}
    (first second third : Fin outerInputs) (valuation : Valuation 3) :
    Valuation outerInputs :=
  fun index =>
    if index = first then valuation ⟨0, by decide⟩
    else if index = second then valuation ⟨1, by decide⟩
    else if index = third then valuation ⟨2, by decide⟩
    else false

private def inputLift4 {outerInputs : Nat}
    (first second third fourth : Fin outerInputs)
    (valuation : Valuation 4) : Valuation outerInputs :=
  fun index =>
    if index = first then valuation ⟨0, by decide⟩
    else if index = second then valuation ⟨1, by decide⟩
    else if index = third then valuation ⟨2, by decide⟩
    else if index = fourth then valuation ⟨3, by decide⟩
    else false

private def inputBinding2Lift
    {outerInputs prefixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (first second : Fin outerInputs) (firstNeSecond : first ≠ second) :
    LocalBlockLift initial
      (binding2 (Source.input first) (Source.input second))
      fin2Zero first where
  lift := inputLift2 first second
  bindingValues := by
    intro valuation index
    by_cases indexZero : index.val = 0
    · have indexEqual : index = fin2Zero := Fin.ext indexZero
      subst index
      change inputLift2 first second valuation first = valuation fin2Zero
      simp [inputLift2]
    · have indexOne : index.val = 1 := by omega
      have indexEqual : index = fin2One := Fin.ext indexOne
      subst index
      change inputLift2 first second valuation second = valuation fin2One
      simp [inputLift2, Ne.symm firstNeSecond]
  targetValue := by
    intro valuation
    simp [inputLift2]
  preservesDifference := by
    intro left right differs
    constructor
    · simpa [inputLift2] using differs.1
    · intro index indexNeFirst
      simp only [inputLift2, if_neg indexNeFirst]
      split
      · rename_i indexEqual
        subst index
        exact differs.2 fin2One (by decide)
      · rfl

private def inputBinding3Lift
    {outerInputs prefixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (first second third : Fin outerInputs)
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (secondNeThird : second ≠ third) :
    LocalBlockLift initial
      (binding3 (Source.input first) (Source.input second)
        (Source.input third))
      ⟨0, by decide⟩ first where
  lift := inputLift3 first second third
  bindingValues := by
    intro valuation index
    by_cases indexZero : index.val = 0
    · have indexEqual : index = ⟨0, by decide⟩ := Fin.ext indexZero
      subst index
      change
        inputLift3 first second third valuation first =
          valuation ⟨0, by decide⟩
      simp [inputLift3]
    · by_cases indexOne : index.val = 1
      · have indexEqual : index = ⟨1, by decide⟩ := Fin.ext indexOne
        subst index
        change
          inputLift3 first second third valuation second =
            valuation ⟨1, by decide⟩
        simp [inputLift3, Ne.symm firstNeSecond]
      · have indexTwo : index.val = 2 := by omega
        have indexEqual : index = ⟨2, by decide⟩ := Fin.ext indexTwo
        subst index
        change
          inputLift3 first second third valuation third =
            valuation ⟨2, by decide⟩
        simp [inputLift3, Ne.symm firstNeThird,
          Ne.symm secondNeThird]
  targetValue := by
    intro valuation
    simp [inputLift3]
  preservesDifference := by
    intro left right differs
    constructor
    · simpa [inputLift3] using differs.1
    · intro index indexNeFirst
      simp only [inputLift3, if_neg indexNeFirst]
      split
      · rename_i indexEqual
        subst index
        exact differs.2 ⟨1, by decide⟩ (by decide)
      · split
        · rename_i indexEqual
          subst index
          exact differs.2 ⟨2, by decide⟩ (by decide)
        · rfl

private def inputBinding4Lift
    {outerInputs prefixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (first second third fourth : Fin outerInputs)
    (firstNeSecond : first ≠ second)
    (firstNeThird : first ≠ third)
    (firstNeFourth : first ≠ fourth)
    (secondNeThird : second ≠ third)
    (secondNeFourth : second ≠ fourth)
    (thirdNeFourth : third ≠ fourth) :
    LocalBlockLift initial
      (binding4 (Source.input first) (Source.input second)
        (Source.input third) (Source.input fourth))
      ⟨0, by decide⟩ first where
  lift := inputLift4 first second third fourth
  bindingValues := by
    intro valuation index
    by_cases indexZero : index.val = 0
    · have indexEqual : index = ⟨0, by decide⟩ := Fin.ext indexZero
      subst index
      change
        inputLift4 first second third fourth valuation first =
          valuation ⟨0, by decide⟩
      simp [inputLift4]
    · by_cases indexOne : index.val = 1
      · have indexEqual : index = ⟨1, by decide⟩ := Fin.ext indexOne
        subst index
        change
          inputLift4 first second third fourth valuation second =
            valuation ⟨1, by decide⟩
        simp [inputLift4, Ne.symm firstNeSecond]
      · by_cases indexTwo : index.val = 2
        · have indexEqual : index = ⟨2, by decide⟩ := Fin.ext indexTwo
          subst index
          change
            inputLift4 first second third fourth valuation third =
              valuation ⟨2, by decide⟩
          simp [inputLift4, Ne.symm firstNeThird,
            Ne.symm secondNeThird]
        · have indexThree : index.val = 3 := by omega
          have indexEqual : index = ⟨3, by decide⟩ :=
            Fin.ext indexThree
          subst index
          change
            inputLift4 first second third fourth valuation fourth =
              valuation ⟨3, by decide⟩
          simp [inputLift4, Ne.symm firstNeFourth,
            Ne.symm secondNeFourth, Ne.symm thirdNeFourth]
  targetValue := by
    intro valuation
    simp [inputLift4]
  preservesDifference := by
    intro left right differs
    constructor
    · simpa [inputLift4] using differs.1
    · intro index indexNeFirst
      simp only [inputLift4, if_neg indexNeFirst]
      split
      · rename_i indexEqual
        subst index
        exact differs.2 ⟨1, by decide⟩ (by decide)
      · split
        · rename_i indexEqual
          subst index
          exact differs.2 ⟨2, by decide⟩ (by decide)
        · split
          · rename_i indexEqual
            subst index
            exact differs.2 ⟨3, by decide⟩ (by decide)
          · rfl

private theorem appendedExpose_prefix_semantics
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (block : Candidate innerInputs suffixGates suffixGates)
    (input : Valuation outerInputs) (output : Fin prefixGates) :
    (exposeAllGates
      (appendCandidateProgram initial binding block)).semantics
        input (Fin.castAdd suffixGates output) =
      (exposeAllGates initial).semantics input output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [exposeAllGates_source, exposeAllGates_source]
  exact Program.eval_appendSubstituted_prefix initial binding
    block.program input output

private theorem appendedExpose_suffix_semantics
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (block : Candidate innerInputs suffixGates suffixGates)
    (blockExposes : ∀ output,
      block.directWireWord.source output = .gate output)
    (input : Valuation outerInputs) (output : Fin suffixGates) :
    (exposeAllGates
      (appendCandidateProgram initial binding block)).semantics
        input (Fin.natAdd prefixGates output) =
      block.semantics
        (fun index =>
          (binding index).eval input (initial.eval input))
        output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [exposeAllGates_source, blockExposes]
  exact Program.eval_appendSubstituted_suffix initial binding
    block.program input output

private theorem appendedExpose_suffix_essential
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (block : Candidate innerInputs suffixGates suffixGates)
    (blockExposes : ∀ output,
      block.directWireWord.source output = .gate output)
    (innerTarget : Fin innerInputs) (outerTarget : Fin outerInputs)
    (lift : LocalBlockLift initial binding innerTarget outerTarget)
    (output : Fin suffixGates)
    (localEssential : OutputEssentialAt block innerTarget output) :
    OutputEssentialAt
      (exposeAllGates (appendCandidateProgram initial binding block))
      outerTarget (Fin.natAdd prefixGates output) := by
  obtain ⟨left, right, differsOnly, semanticDifferent⟩ := localEssential
  refine ⟨lift.lift left, lift.lift right,
    lift.preservesDifference left right differsOnly, ?_⟩
  rw [appendedExpose_suffix_semantics initial binding block blockExposes,
    appendedExpose_suffix_semantics initial binding block blockExposes]
  simpa only [lift.bindingValues] using semanticDifferent

private theorem appendedExpose_prefix_irrelevant
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (block : Candidate innerInputs suffixGates suffixGates)
    (outerTarget : Fin outerInputs)
    (initialAvoids : programAvoidsInput outerTarget initial)
    (output : Fin prefixGates) :
    OutputIrrelevantAt
      (exposeAllGates (appendCandidateProgram initial binding block))
      outerTarget (Fin.castAdd suffixGates output) := by
  intro left right equalAway
  rw [appendedExpose_prefix_semantics,
    appendedExpose_prefix_semantics]
  exact exposeAllGates_outputIrrelevant initial outerTarget
    initialAvoids output left right equalAway

private theorem appendedExpose_prefix_irrelevant_of_irrelevant
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (block : Candidate innerInputs suffixGates suffixGates)
    (outerTarget : Fin outerInputs) (output : Fin prefixGates)
    (irrelevant :
      OutputIrrelevantAt (exposeAllGates initial) outerTarget output) :
    OutputIrrelevantAt
      (exposeAllGates (appendCandidateProgram initial binding block))
      outerTarget (Fin.castAdd suffixGates output) := by
  intro left right equalAway
  rw [appendedExpose_prefix_semantics,
    appendedExpose_prefix_semantics]
  exact irrelevant left right equalAway

private theorem appendedExpose_suffix_irrelevant
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (block : Candidate innerInputs suffixGates suffixGates)
    (blockExposes : ∀ output,
      block.directWireWord.source output = .gate output)
    (outerTarget : Fin outerInputs)
    (bindingIndependent :
      ∀ left right,
        (∀ index, index ≠ outerTarget → left index = right index) →
          ∀ bindingIndex,
            (binding bindingIndex).eval left (initial.eval left) =
              (binding bindingIndex).eval right (initial.eval right))
    (output : Fin suffixGates) :
    OutputIrrelevantAt
      (exposeAllGates (appendCandidateProgram initial binding block))
      outerTarget (Fin.natAdd prefixGates output) := by
  intro left right equalAway
  rw [appendedExpose_suffix_semantics initial binding block blockExposes,
    appendedExpose_suffix_semantics initial binding block blockExposes]
  have boundValues :
      (fun index =>
        (binding index).eval left (initial.eval left)) =
        (fun index =>
          (binding index).eval right (initial.eval right)) := by
    funext bindingIndex
    exact bindingIndependent left right equalAway bindingIndex
  rw [boundValues]

/-- Append one square local macro whose every gate depends on a fresh outer
    lock.  Existing gate outputs retain their conditions, local witnesses lift
    constructively, and the fresh lock separates every cross-block pair. -/
private theorem appendFreshSquareBlock_conditions
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (block : Candidate innerInputs suffixGates suffixGates)
    (blockExposes : ∀ output,
      block.directWireWord.source output = .gate output)
    (innerTarget : Fin innerInputs) (outerTarget : Fin outerInputs)
    (lift : LocalBlockLift initial binding innerTarget outerTarget)
    (initialConditions :
      BaselineOutputConditions (exposeAllGates initial))
    (initialAvoids : programAvoidsInput outerTarget initial)
    (blockConditions : BaselineOutputConditions block)
    (blockEssential :
      ∀ output, OutputEssentialAt block innerTarget output) :
    BaselineOutputConditions
      (exposeAllGates
        (appendCandidateProgram initial binding block)) := by
  have suffixEssential :
      ∀ output,
        OutputEssentialAt
          (exposeAllGates
            (appendCandidateProgram initial binding block)) outerTarget
          (Fin.natAdd prefixGates output) := by
    intro output
    exact appendedExpose_suffix_essential initial binding block
      blockExposes innerTarget outerTarget lift output
      (blockEssential output)
  constructor
  · intro output
    cases finSum_decompose output with
    | inl prefixCase =>
        rcases prefixCase with ⟨prefixOutput, outputEqual⟩
        subst output
        obtain ⟨left, right, different⟩ :=
          initialConditions.nonconstant prefixOutput
        refine ⟨left, right, ?_⟩
        simpa only [appendedExpose_prefix_semantics] using different
    | inr suffixCase =>
        rcases suffixCase with ⟨suffixOutput, outputEqual⟩
        subst output
        exact (suffixEssential suffixOutput).nonconstant
  · intro output queried
    cases finSum_decompose output with
    | inl prefixCase =>
        rcases prefixCase with ⟨prefixOutput, outputEqual⟩
        subst output
        obtain ⟨valuation, different⟩ :=
          initialConditions.notPositiveProjection prefixOutput queried
        refine ⟨valuation, ?_⟩
        simpa only [appendedExpose_prefix_semantics] using different
    | inr suffixCase =>
        rcases suffixCase with ⟨suffixOutput, outputEqual⟩
        subst output
        if targetEqual : outerTarget = queried then
          obtain ⟨localValuation, localDifferent⟩ :=
            blockConditions.notPositiveProjection suffixOutput innerTarget
          refine ⟨lift.lift localValuation, ?_⟩
          rw [appendedExpose_suffix_semantics initial binding block
            blockExposes]
          simp only [lift.bindingValues]
          rw [← targetEqual, lift.targetValue]
          exact localDifferent
        else
          exact (suffixEssential suffixOutput).notProjection_of_ne
            targetEqual
  · intro leftOutput rightOutput outputDifferent
    cases finSum_decompose leftOutput with
    | inl leftPrefixCase =>
        rcases leftPrefixCase with ⟨leftPrefix, leftEqual⟩
        subst leftOutput
        cases finSum_decompose rightOutput with
        | inl rightPrefixCase =>
            rcases rightPrefixCase with ⟨rightPrefix, rightEqual⟩
            subst rightOutput
            have prefixDifferent : leftPrefix ≠ rightPrefix := by
              intro equal
              apply outputDifferent
              exact congrArg (Fin.castAdd suffixGates) equal
            obtain ⟨valuation, different⟩ :=
              initialConditions.pairwiseDistinct prefixDifferent
            refine ⟨valuation, ?_⟩
            simpa only [appendedExpose_prefix_semantics] using different
        | inr rightSuffixCase =>
            rcases rightSuffixCase with ⟨rightSuffix, rightEqual⟩
            subst rightOutput
            obtain ⟨valuation, different⟩ :=
              essential_irrelevant_distinct
                (suffixEssential rightSuffix)
                (appendedExpose_prefix_irrelevant initial binding block
                  outerTarget initialAvoids leftPrefix)
            exact ⟨valuation, fun equal => different equal.symm⟩
    | inr leftSuffixCase =>
        rcases leftSuffixCase with ⟨leftSuffix, leftEqual⟩
        subst leftOutput
        cases finSum_decompose rightOutput with
        | inl rightPrefixCase =>
            rcases rightPrefixCase with ⟨rightPrefix, rightEqual⟩
            subst rightOutput
            exact essential_irrelevant_distinct
              (suffixEssential leftSuffix)
              (appendedExpose_prefix_irrelevant initial binding block
                outerTarget initialAvoids rightPrefix)
        | inr rightSuffixCase =>
            rcases rightSuffixCase with ⟨rightSuffix, rightEqual⟩
            subst rightOutput
            have suffixDifferent : leftSuffix ≠ rightSuffix := by
              intro equal
              apply outputDifferent
              exact congrArg (Fin.natAdd prefixGates) equal
            obtain ⟨localValuation, localDifferent⟩ :=
              blockConditions.pairwiseDistinct suffixDifferent
            refine ⟨lift.lift localValuation, ?_⟩
            rw [appendedExpose_suffix_semantics initial binding block
              blockExposes,
              appendedExpose_suffix_semantics initial binding block
                blockExposes]
            simpa only [lift.bindingValues] using localDifferent

private theorem carrierSlot_encode_ne
    {inputs gates : Nat}
    (slot target : CarrierSlot inputs gates) (different : slot ≠ target) :
    slot.encode ≠ target.encode := by
  intro encodedEqual
  exact different (CarrierSlot.encode_injective encodedEqual)

private theorem carrierInputSource_avoids
    {inputs gates prefixGates : Nat}
    (slot target : CarrierSlot inputs gates) (different : slot ≠ target) :
    sourceAvoidsInput target.encode
      (Source.input slot.encode :
        Source (carrierWidth inputs gates) prefixGates) := by
  exact carrierSlot_encode_ne slot target different

private theorem sourceLockSlot_ne_occurrenceSlot
    {inputs gates : Nat} (lock occurrence : Fin (2 * gates)) :
  sourceLockSlot (inputs := inputs) lock ≠
      occurrenceSlot (inputs := inputs) occurrence := by
  simpa [CarrierSlot.encode] using
    (carrierSlot_encode_ne
      (CarrierSlot.sourceLock lock)
      (CarrierSlot.occurrence occurrence) (by simp))

private theorem sourceLockSlot_ne_primarySlot
    {inputs gates : Nat} (lock : Fin (2 * gates))
    (input : Fin inputs) :
    sourceLockSlot lock ≠ primarySlot (gates := gates) input := by
  simpa [CarrierSlot.encode] using
    (carrierSlot_encode_ne
      (CarrierSlot.sourceLock lock)
      (CarrierSlot.primary input) (by simp))

private theorem sourceLockSlot_ne_traceSlot
    {inputs gates : Nat} (lock : Fin (2 * gates))
    (trace : Fin gates) :
    sourceLockSlot (inputs := inputs) lock ≠
      traceSlot (inputs := inputs) trace := by
  simpa [CarrierSlot.encode] using
    (carrierSlot_encode_ne
      (CarrierSlot.sourceLock lock)
      (CarrierSlot.trace trace) (by simp))

private theorem occurrenceSlot_ne_primarySlot
    {inputs gates : Nat} (occurrence : Fin (2 * gates))
    (input : Fin inputs) :
    occurrenceSlot occurrence ≠ primarySlot (gates := gates) input := by
  simpa [CarrierSlot.encode] using
    (carrierSlot_encode_ne
      (CarrierSlot.occurrence occurrence)
      (CarrierSlot.primary input) (by simp))

private theorem occurrenceSlot_ne_traceSlot
    {inputs gates : Nat} (occurrence : Fin (2 * gates))
    (trace : Fin gates) :
    occurrenceSlot (inputs := inputs) occurrence ≠
      traceSlot (inputs := inputs) trace := by
  simpa [CarrierSlot.encode] using
    (carrierSlot_encode_ne
      (CarrierSlot.occurrence occurrence)
      (CarrierSlot.trace trace) (by simp))

private theorem traceLockSlot_ne_traceSlot
    {inputs gates : Nat} (lock trace : Fin gates) :
    traceLockSlot (inputs := inputs) lock ≠
      traceSlot (inputs := inputs) trace := by
  simpa [CarrierSlot.encode] using
    (carrierSlot_encode_ne
      (CarrierSlot.traceLock lock)
      (CarrierSlot.trace trace) (by simp))

private theorem traceLockSlot_ne_occurrenceSlot
    {inputs gates : Nat} (lock : Fin gates)
    (occurrence : Fin (2 * gates)) :
    traceLockSlot (inputs := inputs) lock ≠
      occurrenceSlot (inputs := inputs) occurrence := by
  simpa [CarrierSlot.encode] using
    (carrierSlot_encode_ne
      (CarrierSlot.traceLock lock)
      (CarrierSlot.occurrence occurrence) (by simp))

private theorem occurrenceSlot_injective {inputs gates : Nat} :
    Function.Injective
      (occurrenceSlot (inputs := inputs) :
        Fin (2 * gates) → Fin (carrierWidth inputs gates)) := by
  intro left right equal
  have decoded := congrArg decodeCarrierSlot equal
  simpa using decoded

private theorem appendSourceMacro_conditions
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide)
    (initialConditions :
      BaselineOutputConditions (exposeAllGates initial))
    (initialAvoids :
      programAvoidsInput
        (sourceLockSlot (occurrenceCoordinate gate side)) initial) :
    BaselineOutputConditions
      (exposeAllGates
        (appendSourceMacro initial source priorWithin gate side).program) := by
  let lock :=
    sourceLockSlot (inputs := inputs) (occurrenceCoordinate gate side)
  let occurrence :=
    occurrenceSlot (inputs := inputs) (occurrenceCoordinate gate side)
  have lockNeOccurrence : lock ≠ occurrence :=
    sourceLockSlot_ne_occurrenceSlot _ _
  cases source with
  | input index =>
      let sourceValue := primarySlot (gates := totalGates) index
      have lockNeSource : lock ≠ sourceValue :=
        sourceLockSlot_ne_primarySlot _ _
      have occurrenceNeSource : occurrence ≠ sourceValue :=
        occurrenceSlot_ne_primarySlot _ _
      change
        BaselineOutputConditions
          (exposeAllGates
            (appendCandidateProgram initial
              (binding3 (.input lock) (.input occurrence)
                (.input sourceValue))
              equalityDirect))
      exact appendFreshSquareBlock_conditions initial
        (binding3 (.input lock) (.input occurrence)
          (.input sourceValue))
        equalityDirect equalityDirect_output_source
        ⟨0, by decide⟩ lock
        (inputBinding3Lift initial lock occurrence sourceValue
          lockNeOccurrence lockNeSource occurrenceNeSource)
        initialConditions initialAvoids
        equalityDirect_baselineOutputConditions
        equalityDirect_lockEssential
  | constant value =>
      cases value with
      | false =>
          change
            BaselineOutputConditions
              (exposeAllGates
                (appendCandidateProgram initial
                  (binding2 (.input lock) (.input occurrence))
                  constantZeroDirect))
          exact appendFreshSquareBlock_conditions initial
            (binding2 (.input lock) (.input occurrence))
            constantZeroDirect constantZeroDirect_output_source
            fin2Zero lock
            (inputBinding2Lift initial lock occurrence lockNeOccurrence)
            initialConditions initialAvoids
            constantZeroDirect_baselineOutputConditions
            constantZeroDirect_lockEssential
      | true =>
          change
            BaselineOutputConditions
              (exposeAllGates
                (appendCandidateProgram initial
                  (binding2 (.input lock) (.input occurrence))
                  constantOneDirect))
          exact appendFreshSquareBlock_conditions initial
            (binding2 (.input lock) (.input occurrence))
            constantOneDirect constantOneDirect_output_source
            fin2Zero lock
            (inputBinding2Lift initial lock occurrence lockNeOccurrence)
            initialConditions initialAvoids
            constantOneDirect_baselineOutputConditions
            constantOneDirect_lockEssential
  | gate index =>
      let sourceValue :=
        traceSlot (inputs := inputs) (Fin.castLE priorWithin index)
      have lockNeSource : lock ≠ sourceValue :=
        sourceLockSlot_ne_traceSlot _ _
      have occurrenceNeSource : occurrence ≠ sourceValue :=
        occurrenceSlot_ne_traceSlot _ _
      change
        BaselineOutputConditions
          (exposeAllGates
            (appendCandidateProgram initial
              (binding3 (.input lock) (.input occurrence)
                (.input sourceValue))
              equalityDirect))
      exact appendFreshSquareBlock_conditions initial
        (binding3 (.input lock) (.input occurrence)
          (.input sourceValue))
        equalityDirect equalityDirect_output_source
        ⟨0, by decide⟩ lock
        (inputBinding3Lift initial lock occurrence sourceValue
          lockNeOccurrence lockNeSource occurrenceNeSource)
        initialConditions initialAvoids
        equalityDirect_baselineOutputConditions
        equalityDirect_lockEssential

private theorem appendTraceMacro_conditions
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates)
    (initialConditions :
      BaselineOutputConditions (exposeAllGates initial))
    (initialAvoids :
      programAvoidsInput (traceLockSlot (inputs := inputs) gate) initial) :
    BaselineOutputConditions
      (exposeAllGates (appendTraceMacro initial gate).program) := by
  let lock := traceLockSlot (inputs := inputs) gate
  let trace := traceSlot (inputs := inputs) gate
  let left :=
    occurrenceSlot (inputs := inputs) (occurrenceCoordinate gate .left)
  let right :=
    occurrenceSlot (inputs := inputs) (occurrenceCoordinate gate .right)
  have lockNeTrace : lock ≠ trace :=
    traceLockSlot_ne_traceSlot _ _
  have lockNeLeft : lock ≠ left :=
    traceLockSlot_ne_occurrenceSlot _ _
  have lockNeRight : lock ≠ right :=
    traceLockSlot_ne_occurrenceSlot _ _
  have traceNeLeft : trace ≠ left :=
    Ne.symm (occurrenceSlot_ne_traceSlot _ _)
  have traceNeRight : trace ≠ right :=
    Ne.symm (occurrenceSlot_ne_traceSlot _ _)
  have leftNeRight : left ≠ right := by
    intro equal
    exact occurrenceCoordinate_left_ne_right gate
      (occurrenceSlot_injective equal)
  change
    BaselineOutputConditions
      (exposeAllGates
        (appendCandidateProgram initial
          (binding4 (.input lock) (.input trace)
            (.input left) (.input right))
          traceDirect))
  exact appendFreshSquareBlock_conditions initial
    (binding4 (.input lock) (.input trace)
      (.input left) (.input right))
    traceDirect traceDirect_output_source
    ⟨0, by decide⟩ lock
    (inputBinding4Lift initial lock trace left right
      lockNeTrace lockNeLeft lockNeRight traceNeLeft traceNeRight
      leftNeRight)
    initialConditions initialAvoids
    traceDirect_baselineOutputConditions
    traceDirect_lockEssential

private theorem appendSourceMacro_avoidsSourceLock
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide)
    (target : Fin (2 * totalGates))
    (lockDifferent : occurrenceCoordinate gate side ≠ target)
    (initialAvoids :
      programAvoidsInput (sourceLockSlot (inputs := inputs) target)
        initial) :
    programAvoidsInput (sourceLockSlot (inputs := inputs) target)
      (appendSourceMacro initial source priorWithin gate side).program := by
  have currentLockAvoids :
      sourceAvoidsInput (sourceLockSlot (inputs := inputs) target)
        (Source.input
          (sourceLockSlot (inputs := inputs)
            (occurrenceCoordinate gate side)) :
          Source (carrierWidth inputs totalGates) prefixGates) := by
    simpa [CarrierSlot.encode] using
      (carrierInputSource_avoids
        (prefixGates := prefixGates)
        (CarrierSlot.sourceLock (occurrenceCoordinate gate side))
        (CarrierSlot.sourceLock target) (by
          intro equal
          exact lockDifferent (CarrierSlot.sourceLock.inj equal)))
  have occurrenceAvoids :
      sourceAvoidsInput (sourceLockSlot (inputs := inputs) target)
        (Source.input
          (occurrenceSlot (inputs := inputs)
            (occurrenceCoordinate gate side)) :
          Source (carrierWidth inputs totalGates) prefixGates) := by
    simpa [CarrierSlot.encode] using
      (carrierInputSource_avoids
        (prefixGates := prefixGates)
        (CarrierSlot.occurrence (occurrenceCoordinate gate side))
        (CarrierSlot.sourceLock target) (by simp))
  cases source with
  | input index =>
      let binding : Fin 3 →
          Source (carrierWidth inputs totalGates) prefixGates :=
        binding3
          (Source.input
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input
            (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input (primarySlot (gates := totalGates) index))
      have bindingAvoids :
          ∀ bindingIndex,
            sourceAvoidsInput
              (sourceLockSlot (inputs := inputs) target)
              (binding bindingIndex) := by
        intro bindingIndex
        dsimp only [binding]
        unfold binding3
        split
        · exact currentLockAvoids
        · split
          · exact occurrenceAvoids
          · simpa [CarrierSlot.encode] using
              (carrierInputSource_avoids
                (prefixGates := prefixGates)
                (CarrierSlot.primary index)
                (CarrierSlot.sourceLock target) (by simp))
      change
        programAvoidsInput (sourceLockSlot (inputs := inputs) target)
          (appendCandidateProgram initial binding equalityDirect)
      exact appendCandidateProgram_avoidsInput
        (sourceLockSlot (inputs := inputs) target)
        initial binding bindingAvoids equalityDirect initialAvoids
  | constant value =>
      let binding : Fin 2 →
          Source (carrierWidth inputs totalGates) prefixGates :=
        binding2
          (Source.input
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input
            (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
      have bindingAvoids :
          ∀ bindingIndex,
            sourceAvoidsInput
              (sourceLockSlot (inputs := inputs) target)
              (binding bindingIndex) := by
        intro bindingIndex
        dsimp only [binding]
        unfold binding2
        split
        · exact currentLockAvoids
        · exact occurrenceAvoids
      cases value with
      | false =>
          change
            programAvoidsInput (sourceLockSlot (inputs := inputs) target)
              (appendCandidateProgram initial binding constantZeroDirect)
          exact appendCandidateProgram_avoidsInput
            (sourceLockSlot (inputs := inputs) target)
            initial binding bindingAvoids constantZeroDirect initialAvoids
      | true =>
          change
            programAvoidsInput (sourceLockSlot (inputs := inputs) target)
              (appendCandidateProgram initial binding constantOneDirect)
          exact appendCandidateProgram_avoidsInput
            (sourceLockSlot (inputs := inputs) target)
            initial binding bindingAvoids constantOneDirect initialAvoids
  | gate index =>
      let binding : Fin 3 →
          Source (carrierWidth inputs totalGates) prefixGates :=
        binding3
          (Source.input
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input
            (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input
            (traceSlot (inputs := inputs)
              (Fin.castLE priorWithin index)))
      have bindingAvoids :
          ∀ bindingIndex,
            sourceAvoidsInput
              (sourceLockSlot (inputs := inputs) target)
              (binding bindingIndex) := by
        intro bindingIndex
        dsimp only [binding]
        unfold binding3
        split
        · exact currentLockAvoids
        · split
          · exact occurrenceAvoids
          · simpa [CarrierSlot.encode] using
              (carrierInputSource_avoids
                (prefixGates := prefixGates)
                (CarrierSlot.trace (Fin.castLE priorWithin index))
                (CarrierSlot.sourceLock target) (by simp))
      change
        programAvoidsInput (sourceLockSlot (inputs := inputs) target)
          (appendCandidateProgram initial binding equalityDirect)
      exact appendCandidateProgram_avoidsInput
        (sourceLockSlot (inputs := inputs) target)
        initial binding bindingAvoids equalityDirect initialAvoids

private theorem appendTraceMacro_avoidsSourceLock
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate : Fin totalGates) (target : Fin (2 * totalGates))
    (initialAvoids :
      programAvoidsInput (sourceLockSlot (inputs := inputs) target)
        initial) :
    programAvoidsInput (sourceLockSlot (inputs := inputs) target)
      (appendTraceMacro initial gate).program := by
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
        sourceAvoidsInput (sourceLockSlot (inputs := inputs) target)
          (binding bindingIndex) := by
    intro bindingIndex
    dsimp only [binding]
    unfold binding4
    split
    · simpa [CarrierSlot.encode] using
        (carrierInputSource_avoids
          (prefixGates := prefixGates)
          (CarrierSlot.traceLock gate)
          (CarrierSlot.sourceLock target) (by simp))
    · split
      · simpa [CarrierSlot.encode] using
          (carrierInputSource_avoids
            (prefixGates := prefixGates)
            (CarrierSlot.trace gate)
            (CarrierSlot.sourceLock target) (by simp))
      · split
        · simpa [CarrierSlot.encode] using
            (carrierInputSource_avoids
              (prefixGates := prefixGates)
              (CarrierSlot.occurrence
                (occurrenceCoordinate gate .left))
              (CarrierSlot.sourceLock target) (by simp))
        · simpa [CarrierSlot.encode] using
            (carrierInputSource_avoids
              (prefixGates := prefixGates)
              (CarrierSlot.occurrence
                (occurrenceCoordinate gate .right))
              (CarrierSlot.sourceLock target) (by simp))
  change
    programAvoidsInput (sourceLockSlot (inputs := inputs) target)
      (appendCandidateProgram initial binding traceDirect)
  exact appendCandidateProgram_avoidsInput
    (sourceLockSlot (inputs := inputs) target)
    initial binding bindingAvoids traceDirect initialAvoids

private theorem appendSourceMacro_avoidsTraceLock
    {inputs priorGates totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (source : Source inputs priorGates)
    (priorWithin : priorGates ≤ totalGates)
    (gate : Fin totalGates) (side : OccurrenceSide)
    (target : Fin totalGates)
    (initialAvoids :
      programAvoidsInput (traceLockSlot (inputs := inputs) target)
        initial) :
    programAvoidsInput (traceLockSlot (inputs := inputs) target)
      (appendSourceMacro initial source priorWithin gate side).program := by
  cases source with
  | input index =>
      let binding : Fin 3 →
          Source (carrierWidth inputs totalGates) prefixGates :=
        binding3
          (Source.input
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input
            (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input (primarySlot (gates := totalGates) index))
      have bindingAvoids :
          ∀ bindingIndex,
            sourceAvoidsInput (traceLockSlot (inputs := inputs) target)
              (binding bindingIndex) := by
        intro bindingIndex
        dsimp only [binding]
        unfold binding3
        split
        · simpa [CarrierSlot.encode] using
            (carrierInputSource_avoids
              (prefixGates := prefixGates)
              (CarrierSlot.sourceLock (occurrenceCoordinate gate side))
              (CarrierSlot.traceLock target) (by simp))
        · split
          · simpa [CarrierSlot.encode] using
              (carrierInputSource_avoids
                (prefixGates := prefixGates)
                (CarrierSlot.occurrence
                  (occurrenceCoordinate gate side))
                (CarrierSlot.traceLock target) (by simp))
          · simpa [CarrierSlot.encode] using
              (carrierInputSource_avoids
                (prefixGates := prefixGates)
                (CarrierSlot.primary index)
                (CarrierSlot.traceLock target) (by simp))
      change
        programAvoidsInput (traceLockSlot (inputs := inputs) target)
          (appendCandidateProgram initial binding equalityDirect)
      exact appendCandidateProgram_avoidsInput
        (traceLockSlot (inputs := inputs) target)
        initial binding bindingAvoids equalityDirect initialAvoids
  | constant value =>
      let binding : Fin 2 →
          Source (carrierWidth inputs totalGates) prefixGates :=
        binding2
          (Source.input
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input
            (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
      have bindingAvoids :
          ∀ bindingIndex,
            sourceAvoidsInput (traceLockSlot (inputs := inputs) target)
              (binding bindingIndex) := by
        intro bindingIndex
        dsimp only [binding]
        unfold binding2
        split
        · simpa [CarrierSlot.encode] using
            (carrierInputSource_avoids
              (prefixGates := prefixGates)
              (CarrierSlot.sourceLock (occurrenceCoordinate gate side))
              (CarrierSlot.traceLock target) (by simp))
        · simpa [CarrierSlot.encode] using
            (carrierInputSource_avoids
              (prefixGates := prefixGates)
              (CarrierSlot.occurrence (occurrenceCoordinate gate side))
              (CarrierSlot.traceLock target) (by simp))
      cases value with
      | false =>
          change
            programAvoidsInput (traceLockSlot (inputs := inputs) target)
              (appendCandidateProgram initial binding constantZeroDirect)
          exact appendCandidateProgram_avoidsInput
            (traceLockSlot (inputs := inputs) target)
            initial binding bindingAvoids constantZeroDirect initialAvoids
      | true =>
          change
            programAvoidsInput (traceLockSlot (inputs := inputs) target)
              (appendCandidateProgram initial binding constantOneDirect)
          exact appendCandidateProgram_avoidsInput
            (traceLockSlot (inputs := inputs) target)
            initial binding bindingAvoids constantOneDirect initialAvoids
  | gate index =>
      let binding : Fin 3 →
          Source (carrierWidth inputs totalGates) prefixGates :=
        binding3
          (Source.input
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input
            (occurrenceSlot (inputs := inputs)
              (occurrenceCoordinate gate side)))
          (Source.input
            (traceSlot (inputs := inputs)
              (Fin.castLE priorWithin index)))
      have bindingAvoids :
          ∀ bindingIndex,
            sourceAvoidsInput (traceLockSlot (inputs := inputs) target)
              (binding bindingIndex) := by
        intro bindingIndex
        dsimp only [binding]
        unfold binding3
        split
        · simpa [CarrierSlot.encode] using
            (carrierInputSource_avoids
              (prefixGates := prefixGates)
              (CarrierSlot.sourceLock (occurrenceCoordinate gate side))
              (CarrierSlot.traceLock target) (by simp))
        · split
          · simpa [CarrierSlot.encode] using
              (carrierInputSource_avoids
                (prefixGates := prefixGates)
                (CarrierSlot.occurrence
                  (occurrenceCoordinate gate side))
                (CarrierSlot.traceLock target) (by simp))
          · simpa [CarrierSlot.encode] using
              (carrierInputSource_avoids
                (prefixGates := prefixGates)
                (CarrierSlot.trace (Fin.castLE priorWithin index))
                (CarrierSlot.traceLock target) (by simp))
      change
        programAvoidsInput (traceLockSlot (inputs := inputs) target)
          (appendCandidateProgram initial binding equalityDirect)
      exact appendCandidateProgram_avoidsInput
        (traceLockSlot (inputs := inputs) target)
        initial binding bindingAvoids equalityDirect initialAvoids

private theorem appendTraceMacro_avoidsTraceLock
    {inputs totalGates prefixGates : Nat}
    (initial : Program (carrierWidth inputs totalGates) prefixGates)
    (gate target : Fin totalGates) (gateDifferent : gate ≠ target)
    (initialAvoids :
      programAvoidsInput (traceLockSlot (inputs := inputs) target)
        initial) :
    programAvoidsInput (traceLockSlot (inputs := inputs) target)
      (appendTraceMacro initial gate).program := by
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
        sourceAvoidsInput (traceLockSlot (inputs := inputs) target)
          (binding bindingIndex) := by
    intro bindingIndex
    dsimp only [binding]
    unfold binding4
    split
    · simpa [CarrierSlot.encode] using
        (carrierInputSource_avoids
          (prefixGates := prefixGates)
          (CarrierSlot.traceLock gate)
          (CarrierSlot.traceLock target) (by
            intro equal
            exact gateDifferent (CarrierSlot.traceLock.inj equal)))
    · split
      · simpa [CarrierSlot.encode] using
          (carrierInputSource_avoids
            (prefixGates := prefixGates)
            (CarrierSlot.trace gate)
            (CarrierSlot.traceLock target) (by simp))
      · split
        · simpa [CarrierSlot.encode] using
            (carrierInputSource_avoids
              (prefixGates := prefixGates)
              (CarrierSlot.occurrence
                (occurrenceCoordinate gate .left))
              (CarrierSlot.traceLock target) (by simp))
        · simpa [CarrierSlot.encode] using
            (carrierInputSource_avoids
              (prefixGates := prefixGates)
              (CarrierSlot.occurrence
                (occurrenceCoordinate gate .right))
              (CarrierSlot.traceLock target) (by simp))
  change
    programAvoidsInput (traceLockSlot (inputs := inputs) target)
      (appendCandidateProgram initial binding traceDirect)
  exact appendCandidateProgram_avoidsInput
    (traceLockSlot (inputs := inputs) target)
    initial binding bindingAvoids traceDirect initialAvoids

private theorem macroAssembly_avoidsSourceLock_after
    {inputs gates totalGates : Nat}
    (program : Program inputs gates) (within : gates ≤ totalGates)
    (targetGate : Fin totalGates) (targetSide : OccurrenceSide)
    (after : gates ≤ targetGate.val) :
    programAvoidsInput
      (sourceLockSlot (inputs := inputs)
        (occurrenceCoordinate targetGate targetSide))
      (macroAssembly program within).program := by
  induction program with
  | empty =>
      trivial
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
      have coordinateNeTarget : coordinate ≠ targetGate := by
        intro equal
        have valueEqual := congrArg Fin.val equal
        change gates = targetGate.val at valueEqual
        omega
      have occurrenceDifferent :
          ∀ side,
            occurrenceCoordinate coordinate side ≠
              occurrenceCoordinate targetGate targetSide := by
        intro side equal
        exact coordinateNeTarget
          (occurrenceCoordinate_injective equal).1
      have earlierAvoids :
          programAvoidsInput
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate targetGate targetSide))
            earlier.program := by
        exact ih earlierWithin (by omega)
      have leftAvoids :
          programAvoidsInput
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate targetGate targetSide))
            left.program :=
        appendSourceMacro_avoidsSourceLock earlier.program gate.left
          earlierWithin coordinate .left
          (occurrenceCoordinate targetGate targetSide)
          (occurrenceDifferent .left) earlierAvoids
      have rightAvoids :
          programAvoidsInput
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate targetGate targetSide))
            right.program :=
        appendSourceMacro_avoidsSourceLock left.program gate.right
          earlierWithin coordinate .right
          (occurrenceCoordinate targetGate targetSide)
          (occurrenceDifferent .right) leftAvoids
      change
        programAvoidsInput
          (sourceLockSlot (inputs := inputs)
            (occurrenceCoordinate targetGate targetSide))
          trace.program
      exact appendTraceMacro_avoidsSourceLock right.program coordinate
        (occurrenceCoordinate targetGate targetSide) rightAvoids

private theorem macroAssembly_avoidsTraceLock_after
    {inputs gates totalGates : Nat}
    (program : Program inputs gates) (within : gates ≤ totalGates)
    (targetGate : Fin totalGates) (after : gates ≤ targetGate.val) :
    programAvoidsInput (traceLockSlot (inputs := inputs) targetGate)
      (macroAssembly program within).program := by
  induction program with
  | empty =>
      trivial
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
      have coordinateNeTarget : coordinate ≠ targetGate := by
        intro equal
        have valueEqual := congrArg Fin.val equal
        change gates = targetGate.val at valueEqual
        omega
      have earlierAvoids :
          programAvoidsInput
            (traceLockSlot (inputs := inputs) targetGate)
            earlier.program := by
        exact ih earlierWithin (by omega)
      have leftAvoids :
          programAvoidsInput
            (traceLockSlot (inputs := inputs) targetGate)
            left.program :=
        appendSourceMacro_avoidsTraceLock earlier.program gate.left
          earlierWithin coordinate .left targetGate earlierAvoids
      have rightAvoids :
          programAvoidsInput
            (traceLockSlot (inputs := inputs) targetGate)
            right.program :=
        appendSourceMacro_avoidsTraceLock left.program gate.right
          earlierWithin coordinate .right targetGate leftAvoids
      change
        programAvoidsInput (traceLockSlot (inputs := inputs) targetGate)
          trace.program
      exact appendTraceMacro_avoidsTraceLock right.program coordinate
        targetGate coordinateNeTarget rightAvoids

private theorem exposeEmpty_conditions {inputs : Nat} :
    BaselineOutputConditions
      (exposeAllGates (Program.empty : Program inputs 0)) := by
  constructor
  · intro output
    exact Fin.elim0 output
  · intro output
    exact Fin.elim0 output
  · intro leftOutput
    exact Fin.elim0 leftOutput

private theorem macroAssembly_conditions
    {inputs gates totalGates : Nat}
    (program : Program inputs gates) (within : gates ≤ totalGates) :
    BaselineOutputConditions
      (exposeAllGates (macroAssembly program within).program) := by
  induction program with
  | empty =>
      exact exposeEmpty_conditions
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
      have earlierConditions :
          BaselineOutputConditions (exposeAllGates earlier.program) :=
        ih earlierWithin
      have earlierAvoidsLeft :
          programAvoidsInput
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate coordinate .left))
            earlier.program :=
        macroAssembly_avoidsSourceLock_after initial earlierWithin
          coordinate .left (Nat.le_refl gates)
      have leftConditions :
          BaselineOutputConditions (exposeAllGates left.program) :=
        appendSourceMacro_conditions earlier.program gate.left
          earlierWithin coordinate .left earlierConditions
          earlierAvoidsLeft
      have earlierAvoidsRight :
          programAvoidsInput
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate coordinate .right))
            earlier.program :=
        macroAssembly_avoidsSourceLock_after initial earlierWithin
          coordinate .right (Nat.le_refl gates)
      have leftAvoidsRight :
          programAvoidsInput
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate coordinate .right))
            left.program :=
        appendSourceMacro_avoidsSourceLock earlier.program gate.left
          earlierWithin coordinate .left
          (occurrenceCoordinate coordinate .right)
          (occurrenceCoordinate_left_ne_right coordinate)
          earlierAvoidsRight
      have rightConditions :
          BaselineOutputConditions (exposeAllGates right.program) :=
        appendSourceMacro_conditions left.program gate.right
          earlierWithin coordinate .right leftConditions
          leftAvoidsRight
      have earlierAvoidsTrace :
          programAvoidsInput (traceLockSlot (inputs := inputs) coordinate)
            earlier.program :=
        macroAssembly_avoidsTraceLock_after initial earlierWithin
          coordinate (Nat.le_refl gates)
      have leftAvoidsTrace :
          programAvoidsInput (traceLockSlot (inputs := inputs) coordinate)
            left.program :=
        appendSourceMacro_avoidsTraceLock earlier.program gate.left
          earlierWithin coordinate .left coordinate earlierAvoidsTrace
      have rightAvoidsTrace :
          programAvoidsInput (traceLockSlot (inputs := inputs) coordinate)
            right.program :=
        appendSourceMacro_avoidsTraceLock left.program gate.right
          earlierWithin coordinate .right coordinate leftAvoidsTrace
      have traceConditions :
          BaselineOutputConditions (exposeAllGates trace.program) :=
        appendTraceMacro_conditions right.program coordinate
          rightConditions rightAvoidsTrace
      change
        BaselineOutputConditions (exposeAllGates trace.program)
      exact traceConditions

private def prependValuation {inputs : Nat} (head : Bool)
    (tail : Valuation inputs) : Valuation (inputs + 1) :=
  fun index =>
    if atHead : index.val = 0 then head
    else tail ⟨index.val - 1, by omega⟩

private theorem prependValuation_zero {inputs : Nat} (head : Bool)
    (tail : Valuation inputs) :
    prependValuation head tail ⟨0, by omega⟩ = head := by
  simp [prependValuation]

private theorem prependValuation_succ {inputs : Nat} (head : Bool)
    (tail : Valuation inputs) (index : Fin inputs) :
    prependValuation head tail index.succ = tail index := by
  simp [prependValuation]

private theorem exposeRenameSucc_semantics
    {inputs gates : Nat} (program : Program inputs gates)
    (head : Bool) (input : Valuation inputs) (output : Fin gates) :
    (exposeAllGates (program.renameInputs Fin.succ)).semantics
        (prependValuation head input) output =
      (exposeAllGates program).semantics input output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [exposeAllGates_source, exposeAllGates_source]
  change
    (program.renameInputs Fin.succ).eval
        (prependValuation head input) output =
      program.eval input output
  rw [Program.eval_renameInputs]
  apply congrArg (fun valuation => program.eval valuation output)
  funext index
  exact prependValuation_succ head input index

private theorem OutputNonconstant.notConstantValue
    {inputs gates outputs : Nat}
    {candidate : Candidate inputs gates outputs}
    {output : Fin outputs}
    (nonconstant : OutputNonconstant candidate output)
    (value : Bool) :
    ∃ valuation, candidate.semantics valuation output ≠ value := by
  obtain ⟨left, right, different⟩ := nonconstant
  by_cases leftDifferent :
      candidate.semantics left output ≠ value
  · exact ⟨left, leftDifferent⟩
  · by_cases rightDifferent :
      candidate.semantics right output ≠ value
    · exact ⟨right, rightDifferent⟩
    · exact False.elim (different
        ((boolEqual_of_not_ne _ _ leftDifferent).trans
          (boolEqual_of_not_ne _ _ rightDifferent).symm))

private theorem exposeRenameSucc_conditions
    {inputs gates : Nat} (program : Program inputs gates)
    (conditions : BaselineOutputConditions (exposeAllGates program)) :
    BaselineOutputConditions
      (exposeAllGates (program.renameInputs Fin.succ)) := by
  constructor
  · intro output
    obtain ⟨left, right, different⟩ :=
      conditions.nonconstant output
    refine ⟨prependValuation false left,
      prependValuation false right, ?_⟩
    simpa only [exposeRenameSucc_semantics] using different
  · intro output queried
    by_cases atHead : queried.val = 0
    · have queriedEqual : queried = ⟨0, by omega⟩ := Fin.ext atHead
      obtain ⟨valuation, different⟩ :=
        OutputNonconstant.notConstantValue
          (conditions.nonconstant output) false
      refine ⟨prependValuation false valuation, ?_⟩
      rw [exposeRenameSucc_semantics, queriedEqual,
        prependValuation_zero]
      exact different
    · let oldIndex : Fin inputs :=
        ⟨queried.val - 1, by omega⟩
      have queriedPositive : 0 < queried.val :=
        Nat.pos_of_ne_zero atHead
      have queriedEqual : queried = oldIndex.succ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        dsimp only [oldIndex]
        omega
      obtain ⟨valuation, different⟩ :=
        conditions.notPositiveProjection output oldIndex
      refine ⟨prependValuation false valuation, ?_⟩
      rw [exposeRenameSucc_semantics, queriedEqual,
        prependValuation_succ]
      exact different
  · intro leftOutput rightOutput outputDifferent
    obtain ⟨valuation, different⟩ :=
      conditions.pairwiseDistinct outputDifferent
    refine ⟨prependValuation false valuation, ?_⟩
    simpa only [exposeRenameSucc_semantics] using different

private theorem sourceRenameSucc_avoidsZero
    {inputs gates : Nat} (source : Source inputs gates) :
    sourceAvoidsInput (⟨0, by omega⟩ : Fin (inputs + 1))
      (source.renameInputs Fin.succ) := by
  cases source with
  | input index =>
      intro equal
      have valueEqual := congrArg Fin.val equal
      simp at valueEqual
  | constant value => trivial
  | gate index => trivial

private theorem programRenameSucc_avoidsZero
    {inputs gates : Nat} (program : Program inputs gates) :
    programAvoidsInput (⟨0, by omega⟩ : Fin (inputs + 1))
      (program.renameInputs Fin.succ) := by
  induction program with
  | empty =>
      trivial
  | snoc initial gate ih =>
      exact ⟨ih,
        sourceRenameSucc_avoidsZero gate.left,
        sourceRenameSucc_avoidsZero gate.right⟩

private theorem prefixConjunction_constant (tailChecks : Nat)
    (value : Bool) :
    prefixConjunction
        (List.ofFn (fun _ : Fin (tailChecks + 1) => value)) =
      value := by
  rw [prefixConjunction_spec]
  cases value with
  | false =>
      rw [List.ofFn_succ]
      rfl
  | true =>
      induction tailChecks with
      | zero => rfl
      | succ tailChecks ih =>
          rw [List.ofFn_succ]
          simp only [allChecks, Bool.true_and]
          exact ih

private def prefixStepValuation (tailChecks : Nat)
    (valuation : Valuation 2) : Valuation (tailChecks + 2) :=
  fun index =>
    if index.val = 0 then valuation fin2One
    else valuation fin2Zero

private theorem prefixStepValuation_zero (tailChecks : Nat)
    (valuation : Valuation 2) :
    prefixStepValuation tailChecks valuation ⟨0, by omega⟩ =
      valuation fin2One := by
  simp [prefixStepValuation]

private theorem prefixStepValuation_succ (tailChecks : Nat)
    (valuation : Valuation 2) (index : Fin (tailChecks + 1)) :
    prefixStepValuation tailChecks valuation index.succ =
      valuation fin2Zero := by
  simp [prefixStepValuation]

private theorem renamedPrefixOutput_step
    (tailChecks : Nat) (valuation : Valuation 2) :
    let earlier := nonemptyPrefixAssembly tailChecks
    (earlier.output.renameInputs Fin.succ).eval
        (prefixStepValuation tailChecks valuation)
        ((earlier.program.renameInputs Fin.succ).eval
          (prefixStepValuation tailChecks valuation)) =
      valuation fin2Zero := by
  let earlier := nonemptyPrefixAssembly tailChecks
  have inputEqual :
      (fun index : Fin (tailChecks + 1) =>
        prefixStepValuation tailChecks valuation index.succ) =
        (fun _ => valuation fin2Zero) := by
    funext index
    exact prefixStepValuation_succ tailChecks valuation index
  have gateEqual :
      ∀ gate,
        (earlier.program.renameInputs Fin.succ).eval
            (prefixStepValuation tailChecks valuation) gate =
          earlier.program.eval (fun _ => valuation fin2Zero) gate := by
    intro gate
    rw [Program.eval_renameInputs]
    exact congrArg (fun input => earlier.program.eval input gate)
      inputEqual
  dsimp only [earlier]
  rw [Source.eval_renameInputs]
  rw [(nonemptyPrefixAssembly tailChecks).output.eval_congr
    (fun index => congrFun inputEqual index) gateEqual]
  have semantic :=
    nonemptyPrefixCandidate_semantics tailChecks
      (fun _ => valuation fin2Zero)
  unfold Candidate.semantics DirectWire.semantics
    DirectWireWord.eval at semantic
  rw [nonemptyPrefixCandidate_output_source] at semantic
  change
    earlier.output.eval (fun _ => valuation fin2Zero)
        (earlier.program.eval fun _ => valuation fin2Zero) =
      prefixConjunction
        (List.ofFn (fun _ : Fin (tailChecks + 1) =>
          valuation fin2Zero)) at semantic
  rw [semantic, prefixConjunction_constant]

private def prefixStepLift (tailChecks : Nat) :
    let earlier := nonemptyPrefixAssembly tailChecks
    let renamedProgram := earlier.program.renameInputs Fin.succ
    let renamedOutput := earlier.output.renameInputs Fin.succ
    let newest : Source (tailChecks + 2) (2 * tailChecks) :=
      .input ⟨0, by omega⟩
    LocalBlockLift renamedProgram
      (binding2 renamedOutput newest) fin2One ⟨0, by omega⟩ := by
  dsimp only
  refine
    { lift := prefixStepValuation tailChecks
      bindingValues := ?_
      targetValue := ?_
      preservesDifference := ?_ }
  · intro valuation index
    by_cases indexZero : index.val = 0
    · have indexEqual : index = fin2Zero := Fin.ext indexZero
      subst index
      change
        ((nonemptyPrefixAssembly tailChecks).output.renameInputs
          Fin.succ).eval
            (prefixStepValuation tailChecks valuation)
            (((nonemptyPrefixAssembly tailChecks).program.renameInputs
              Fin.succ).eval
                (prefixStepValuation tailChecks valuation)) =
          valuation fin2Zero
      exact renamedPrefixOutput_step tailChecks valuation
    · have indexOne : index.val = 1 := by omega
      have indexEqual : index = fin2One := Fin.ext indexOne
      subst index
      change
        prefixStepValuation tailChecks valuation ⟨0, by omega⟩ =
          valuation fin2One
      exact prefixStepValuation_zero tailChecks valuation
  · intro valuation
    exact prefixStepValuation_zero tailChecks valuation
  · intro left right differs
    constructor
    · simpa [prefixStepValuation] using differs.1
    · intro index indexNeZero
      have valueNeZero : index.val ≠ 0 :=
        fun valueEqual => indexNeZero (Fin.ext valueEqual)
      simpa only [prefixStepValuation, if_neg valueNeZero] using
        differs.2 fin2Zero (by decide)

private theorem nonemptyPrefixAssembly_conditions (tailChecks : Nat) :
    BaselineOutputConditions
      (exposeAllGates (nonemptyPrefixAssembly tailChecks).program) := by
  induction tailChecks with
  | zero =>
      exact exposeEmpty_conditions
  | succ tailChecks ih =>
      let earlier := nonemptyPrefixAssembly tailChecks
      let renamedProgram := earlier.program.renameInputs Fin.succ
      let renamedOutput := earlier.output.renameInputs Fin.succ
      let newest : Source (tailChecks + 2) (2 * tailChecks) :=
        .input ⟨0, by omega⟩
      let binding := binding2 renamedOutput newest
      have renamedConditions :
          BaselineOutputConditions (exposeAllGates renamedProgram) :=
        exposeRenameSucc_conditions earlier.program ih
      have renamedAvoids :
          programAvoidsInput (⟨0, by omega⟩ : Fin (tailChecks + 2))
            renamedProgram :=
        programRenameSucc_avoidsZero earlier.program
      change
        BaselineOutputConditions
          (exposeAllGates
            (appendCandidateProgram renamedProgram binding
              prefixAndDirect))
      exact appendFreshSquareBlock_conditions renamedProgram binding
        prefixAndDirect prefixAndDirect_output_source
        fin2One ⟨0, by omega⟩ (prefixStepLift tailChecks)
        renamedConditions renamedAvoids
        prefixAndDirect_baselineOutputConditions
        prefixAndDirect_rightEssential

private theorem exposeRenameSucc_essential
    {inputs gates : Nat} (program : Program inputs gates)
    (target : Fin inputs) (output : Fin gates)
    (essential :
      OutputEssentialAt (exposeAllGates program) target output) :
    OutputEssentialAt
      (exposeAllGates (program.renameInputs Fin.succ))
      target.succ output := by
  obtain ⟨left, right, differs, semanticDifferent⟩ := essential
  refine ⟨prependValuation false left,
    prependValuation false right, ?_, ?_⟩
  · constructor
    · simpa only [prependValuation_succ] using differs.1
    · intro index indexNeTarget
      by_cases atHead : index.val = 0
      · have indexEqual : index = ⟨0, by omega⟩ := Fin.ext atHead
        rw [indexEqual]
        rfl
      · let oldIndex : Fin inputs := ⟨index.val - 1, by omega⟩
        have indexPositive : 0 < index.val :=
          Nat.pos_of_ne_zero atHead
        have indexEqual : index = oldIndex.succ := by
          apply Fin.ext
          simp only [Fin.val_succ]
          dsimp only [oldIndex]
          omega
        have oldNeTarget : oldIndex ≠ target := by
          intro equal
          apply indexNeTarget
          rw [indexEqual, equal]
        rw [indexEqual, prependValuation_succ,
          prependValuation_succ]
        exact differs.2 oldIndex oldNeTarget
  · simpa only [exposeRenameSucc_semantics] using semanticDifferent

private theorem appendedExpose_prefix_essential
    {outerInputs innerInputs prefixGates suffixGates : Nat}
    (initial : Program outerInputs prefixGates)
    (binding : Fin innerInputs → Source outerInputs prefixGates)
    (block : Candidate innerInputs suffixGates suffixGates)
    (target : Fin outerInputs) (output : Fin prefixGates)
    (essential :
      OutputEssentialAt (exposeAllGates initial) target output) :
    OutputEssentialAt
      (exposeAllGates
        (appendCandidateProgram initial binding block))
      target (Fin.castAdd suffixGates output) := by
  obtain ⟨left, right, differs, semanticDifferent⟩ := essential
  refine ⟨left, right, differs, ?_⟩
  simpa only [appendedExpose_prefix_semantics] using semanticDifferent

private def singleTargetValuation {inputs : Nat}
    (target : Fin inputs) (value : Bool) : Valuation inputs :=
  fun index => if index = target then value else true

private theorem prefixConjunction_singleTarget
    {inputs : Nat} (target : Fin inputs) (value : Bool) :
    prefixConjunction
        (List.ofFn (singleTargetValuation target value)) =
      value := by
  cases value with
  | true =>
      have valuationEqual :
          singleTargetValuation target true = (fun _ => true) := by
        funext index
        simp [singleTargetValuation]
      rw [valuationEqual]
      have positive : 0 < inputs :=
        Nat.zero_lt_of_lt target.isLt
      have sizeEqual : inputs - 1 + 1 = inputs := by omega
      have listEqual :
          List.ofFn (fun _ : Fin (inputs - 1 + 1) => true) =
            List.ofFn (fun _ : Fin inputs => true) := by
        simpa using
          list_ofFn_finCast sizeEqual
            (fun _ : Fin inputs => true)
      rw [← listEqual]
      exact prefixConjunction_constant (inputs - 1) true
  | false =>
      cases result :
          prefixConjunction
            (List.ofFn (singleTargetValuation target false)) with
      | false => rfl
      | true =>
          have allTrue :=
            (prefixConjunction_eq_true_iff
              (List.ofFn
                (singleTargetValuation target false))).mp result
          let items :=
            List.ofFn (singleTargetValuation target false)
          have lengthEqual : items.length = inputs := by
            simp [items]
          let position : Fin items.length :=
            Fin.cast lengthEqual.symm target
          have valueEqual : items.get position = false := by
            simp [items, position, singleTargetValuation]
          have member : false ∈ items := by
            rw [← valueEqual]
            exact List.get_mem items position
          exact Bool.noConfusion (allTrue false member)

private theorem renamedPrefixOutput_semantics
    (tailChecks : Nat) (head : Bool)
    (input : Valuation (tailChecks + 1)) :
    let earlier := nonemptyPrefixAssembly tailChecks
    (earlier.output.renameInputs Fin.succ).eval
        (prependValuation head input)
        ((earlier.program.renameInputs Fin.succ).eval
          (prependValuation head input)) =
      prefixConjunction (List.ofFn input) := by
  let earlier := nonemptyPrefixAssembly tailChecks
  have gateEqual :
      ∀ gate,
        (earlier.program.renameInputs Fin.succ).eval
            (prependValuation head input) gate =
          earlier.program.eval input gate := by
    intro gate
    rw [Program.eval_renameInputs]
    apply congrArg (fun valuation => earlier.program.eval valuation gate)
    funext index
    exact prependValuation_succ head input index
  dsimp only [earlier]
  rw [Source.eval_renameInputs]
  rw [(nonemptyPrefixAssembly tailChecks).output.eval_congr
    (fun index => prependValuation_succ head input index) gateEqual]
  have semantic :=
    nonemptyPrefixCandidate_semantics tailChecks input
  unfold Candidate.semantics DirectWire.semantics
    DirectWireWord.eval at semantic
  rw [nonemptyPrefixCandidate_output_source] at semantic
  exact semantic

private def prefixOldTargetValuation (tailChecks : Nat)
    (target : Fin (tailChecks + 1)) (valuation : Valuation 2) :
    Valuation (tailChecks + 2) :=
  prependValuation (valuation fin2One)
    (singleTargetValuation target (valuation fin2Zero))

private def prefixOldTargetLift (tailChecks : Nat)
    (target : Fin (tailChecks + 1)) :
    let earlier := nonemptyPrefixAssembly tailChecks
    let renamedProgram := earlier.program.renameInputs Fin.succ
    let renamedOutput := earlier.output.renameInputs Fin.succ
    let newest : Source (tailChecks + 2) (2 * tailChecks) :=
      .input ⟨0, by omega⟩
    LocalBlockLift renamedProgram
      (binding2 renamedOutput newest) fin2Zero target.succ := by
  dsimp only
  refine
    { lift := prefixOldTargetValuation tailChecks target
      bindingValues := ?_
      targetValue := ?_
      preservesDifference := ?_ }
  · intro valuation index
    by_cases indexZero : index.val = 0
    · have indexEqual : index = fin2Zero := Fin.ext indexZero
      subst index
      change
        ((nonemptyPrefixAssembly tailChecks).output.renameInputs
          Fin.succ).eval
            (prefixOldTargetValuation tailChecks target valuation)
            (((nonemptyPrefixAssembly tailChecks).program.renameInputs
              Fin.succ).eval
                (prefixOldTargetValuation tailChecks target valuation)) =
          valuation fin2Zero
      rw [show prefixOldTargetValuation tailChecks target valuation =
          prependValuation (valuation fin2One)
            (singleTargetValuation target
              (valuation fin2Zero)) from rfl]
      rw [renamedPrefixOutput_semantics,
        prefixConjunction_singleTarget]
    · have indexOne : index.val = 1 := by omega
      have indexEqual : index = fin2One := Fin.ext indexOne
      subst index
      change
        prefixOldTargetValuation tailChecks target valuation
            ⟨0, by omega⟩ =
          valuation fin2One
      exact prependValuation_zero _ _
  · intro valuation
    change
      prefixOldTargetValuation tailChecks target valuation
          target.succ =
        valuation fin2Zero
    rw [show prefixOldTargetValuation tailChecks target valuation =
        prependValuation (valuation fin2One)
          (singleTargetValuation target
            (valuation fin2Zero)) from rfl]
    rw [prependValuation_succ]
    simp [singleTargetValuation]
  · intro left right differs
    constructor
    · change
        prefixOldTargetValuation tailChecks target left target.succ ≠
          prefixOldTargetValuation tailChecks target right target.succ
      rw [show prefixOldTargetValuation tailChecks target left =
          prependValuation (left fin2One)
            (singleTargetValuation target (left fin2Zero)) from rfl,
        show prefixOldTargetValuation tailChecks target right =
          prependValuation (right fin2One)
            (singleTargetValuation target (right fin2Zero)) from rfl,
        prependValuation_succ, prependValuation_succ]
      simpa [singleTargetValuation] using differs.1
    · intro index indexNeTarget
      by_cases atHead : index.val = 0
      · have indexEqual : index = ⟨0, by omega⟩ := Fin.ext atHead
        rw [indexEqual]
        change left fin2One = right fin2One
        exact differs.2 fin2One (by decide)
      · let oldIndex : Fin (tailChecks + 1) :=
          ⟨index.val - 1, by omega⟩
        have indexPositive : 0 < index.val :=
          Nat.pos_of_ne_zero atHead
        have indexEqual : index = oldIndex.succ := by
          apply Fin.ext
          simp only [Fin.val_succ]
          dsimp only [oldIndex]
          omega
        have oldNeTarget : oldIndex ≠ target := by
          intro equal
          apply indexNeTarget
          rw [indexEqual, equal]
        rw [indexEqual]
        change
          singleTargetValuation target (left fin2Zero) oldIndex =
            singleTargetValuation target (right fin2Zero) oldIndex
        simp [singleTargetValuation, oldNeTarget]

private theorem appendedPrefix_oldTargetEssential
    (tailChecks : Nat) (target : Fin (tailChecks + 1))
    (output : Fin 2) :
    let earlier := nonemptyPrefixAssembly tailChecks
    let renamedProgram := earlier.program.renameInputs Fin.succ
    let renamedOutput := earlier.output.renameInputs Fin.succ
    let newest : Source (tailChecks + 2) (2 * tailChecks) :=
      .input ⟨0, by omega⟩
    let binding := binding2 renamedOutput newest
    OutputEssentialAt
      (exposeAllGates
        (appendCandidateProgram renamedProgram binding prefixAndDirect))
      target.succ (Fin.natAdd (2 * tailChecks) output) := by
  dsimp only
  exact appendedExpose_suffix_essential
    ((nonemptyPrefixAssembly tailChecks).program.renameInputs Fin.succ)
    (binding2
      ((nonemptyPrefixAssembly tailChecks).output.renameInputs Fin.succ)
      (.input ⟨0, by omega⟩))
    prefixAndDirect prefixAndDirect_output_source
    fin2Zero target.succ
    (prefixOldTargetLift tailChecks target) output
    (prefixAndDirect_leftEssential output)

private theorem appendedPrefix_newestEssential
    (tailChecks : Nat) (output : Fin 2) :
    let earlier := nonemptyPrefixAssembly tailChecks
    let renamedProgram := earlier.program.renameInputs Fin.succ
    let renamedOutput := earlier.output.renameInputs Fin.succ
    let newest : Source (tailChecks + 2) (2 * tailChecks) :=
      .input ⟨0, by omega⟩
    let binding := binding2 renamedOutput newest
    OutputEssentialAt
      (exposeAllGates
        (appendCandidateProgram renamedProgram binding prefixAndDirect))
      ⟨0, by omega⟩ (Fin.natAdd (2 * tailChecks) output) := by
  dsimp only
  exact appendedExpose_suffix_essential
    ((nonemptyPrefixAssembly tailChecks).program.renameInputs Fin.succ)
    (binding2
      ((nonemptyPrefixAssembly tailChecks).output.renameInputs Fin.succ)
      (.input ⟨0, by omega⟩))
    prefixAndDirect prefixAndDirect_output_source
    fin2One ⟨0, by omega⟩
    (prefixStepLift tailChecks) output
    (prefixAndDirect_rightEssential output)

/-- Every prefix gate depends on both of the two oldest checks.  Under the
    front-insertion recursion these are the final two local input
    coordinates, and they remain common anchors for the entire fold. -/
private theorem nonemptyPrefixAssembly_lastTwoEssential
    (earlierChecks : Nat) :
    let tailChecks := earlierChecks + 1
    let candidate :=
      exposeAllGates (nonemptyPrefixAssembly tailChecks).program
    ∀ output,
      OutputEssentialAt candidate
          (Fin.last (earlierChecks + 1)) output ∧
        OutputEssentialAt candidate
          ⟨earlierChecks, by omega⟩ output := by
  dsimp only
  induction earlierChecks with
  | zero =>
      intro output
      have suffixForm :
          ∃ localOutput : Fin 2,
            output = Fin.natAdd 0 localOutput := by
        exact ⟨Fin.cast (by omega) output, Fin.ext (by simp)⟩
      obtain ⟨localOutput, outputEqual⟩ := suffixForm
      subst output
      constructor
      · have targetEqual :
            fin1Zero.succ = Fin.last 1 := Fin.ext rfl
        rw [← targetEqual]
        simpa [nonemptyPrefixAssembly] using
          appendedPrefix_oldTargetEssential 0 fin1Zero localOutput
      · simpa [nonemptyPrefixAssembly] using
          appendedPrefix_newestEssential 0 localOutput
  | succ earlierChecks ih =>
      let oldAssembly :=
        nonemptyPrefixAssembly (earlierChecks + 1)
      let renamedProgram := oldAssembly.program.renameInputs Fin.succ
      let renamedOutput := oldAssembly.output.renameInputs Fin.succ
      let newest :
          Source (earlierChecks + 3) (2 * (earlierChecks + 1)) :=
        .input ⟨0, by omega⟩
      let binding := binding2 renamedOutput newest
      intro output
      cases finSum_decompose output with
      | inl prefixCase =>
          rcases prefixCase with ⟨oldOutput, outputEqual⟩
          subst output
          obtain ⟨oldLastEssential, oldSecondEssential⟩ :=
            ih oldOutput
          have renamedLastEssential :=
            exposeRenameSucc_essential oldAssembly.program
              (Fin.last (earlierChecks + 1)) oldOutput
              oldLastEssential
          have renamedSecondEssential :=
            exposeRenameSucc_essential oldAssembly.program
              ⟨earlierChecks, by omega⟩ oldOutput
              oldSecondEssential
          constructor
          · simpa [oldAssembly, renamedProgram, renamedOutput, newest,
              binding, nonemptyPrefixAssembly] using
              appendedExpose_prefix_essential renamedProgram binding
                prefixAndDirect
                (Fin.last (earlierChecks + 1)).succ oldOutput
                renamedLastEssential
          · simpa [oldAssembly, renamedProgram, renamedOutput, newest,
              binding, nonemptyPrefixAssembly] using
              appendedExpose_prefix_essential renamedProgram binding
                prefixAndDirect
                (⟨earlierChecks, by omega⟩ :
                  Fin (earlierChecks + 2)).succ oldOutput
                renamedSecondEssential
      | inr suffixCase =>
          rcases suffixCase with ⟨localOutput, outputEqual⟩
          subst output
          constructor
          · simpa [oldAssembly, renamedProgram, renamedOutput, newest,
              binding, nonemptyPrefixAssembly] using
              appendedPrefix_oldTargetEssential
                (earlierChecks + 1)
                (Fin.last (earlierChecks + 1)) localOutput
          · have targetEqual :
                (⟨earlierChecks, by omega⟩ :
                  Fin (earlierChecks + 2)).succ =
                  (⟨earlierChecks + 1, by omega⟩ :
                    Fin (earlierChecks + 3)) := Fin.ext rfl
            have anchorEssential :=
              appendedPrefix_oldTargetEssential
                (earlierChecks + 1)
                ⟨earlierChecks, by omega⟩ localOutput
            rw [targetEqual] at anchorEssential
            simpa [oldAssembly, renamedProgram, renamedOutput, newest,
              binding, nonemptyPrefixAssembly] using
              anchorEssential

/-! ## Realizing arbitrary distinguished-check valuations -/

private def sourceCheckIndex {gates : Nat}
    (occurrence : Fin (2 * gates)) : Fin (3 * gates) :=
  ⟨occurrence.val + occurrence.val / 2, by omega⟩

private def traceCheckIndex {gates : Nat}
    (gate : Fin gates) : Fin (3 * gates) :=
  ⟨3 * gate.val + 2, by omega⟩

private theorem sourceCheckIndex_left {gates : Nat}
    (gate : Fin gates) :
    sourceCheckIndex (occurrenceCoordinate gate .left) =
      ⟨3 * gate.val, by omega⟩ := by
  apply Fin.ext
  simp [sourceCheckIndex, occurrenceCoordinate]
  omega

private theorem sourceCheckIndex_right {gates : Nat}
    (gate : Fin gates) :
    sourceCheckIndex (occurrenceCoordinate gate .right) =
      ⟨3 * gate.val + 1, by omega⟩ := by
  apply Fin.ext
  simp [sourceCheckIndex, occurrenceCoordinate]
  omega

private def checkCarrierValuation {inputs gates : Nat}
    (program : Program inputs gates) (input : Valuation inputs)
    (checks : Valuation (3 * gates)) :
    CarrierValuation inputs gates :=
  let coherent := coherentExtension program input
  { primary := coherent.primary
    trace := coherent.trace
    occurrence := coherent.occurrence
    sourceLock := fun occurrence => checks (sourceCheckIndex occurrence)
    traceLock := fun gate => checks (traceCheckIndex gate)
    finalLock := coherent.finalLock }

private theorem sourceCheck_coherentLock
    {inputs gates : Nat} (source : Source inputs gates)
    (lock : Bool) (input : Valuation inputs)
    (trace : Valuation gates) :
    sourceCheck source lock (source.eval input trace) input trace =
      lock := by
  cases source with
  | input index =>
      rw [sourceCheck, equalityMacro_distinguished_spec]
      simp [Source.eval, boolEq_eq_true_iff]
  | constant value =>
      cases value with
      | false =>
          rw [sourceCheck, constantZeroMacro_distinguished_spec]
          cases lock <;> rfl
      | true =>
          rw [sourceCheck, constantOneMacro_distinguished_spec]
          cases lock <;> rfl
  | gate index =>
      rw [sourceCheck, equalityMacro_distinguished_spec]
      simp [Source.eval, boolEq_eq_true_iff]

private theorem traceCheck_coherentLock
    (lock left right : Bool) :
    traceCheck lock (boolNand left right) left right = lock := by
  rw [traceCheck, traceMacro_distinguished_spec]
  simp [boolEq_eq_true_iff]

private theorem checkCarrierValuation_restrict
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) (input : Valuation inputs)
    (checks : Valuation (3 * (gates + 1))) :
    (checkCarrierValuation (.snoc initial gate) input checks).restrict =
      checkCarrierValuation initial input
        (fun index => checks (Fin.castAdd 3 index)) := by
  apply CarrierValuation.ext
  · rfl
  · funext index
    exact Program.eval_snoc_castSucc initial gate input index
  · funext index
    exact coherentOccurrences_snoc_earlier initial gate input index
  · funext index
    apply congrArg checks
    apply Fin.ext
    rfl
  · funext index
    apply congrArg checks
    apply Fin.ext
    rfl
  · rfl

private theorem gateChecks_checkCarrierValuation
    {inputs gates : Nat} (initial : Program inputs gates)
    (gate : Gate inputs gates) (input : Valuation inputs)
    (checks : Valuation (3 * (gates + 1))) :
    gateChecks gate
        (checkCarrierValuation (.snoc initial gate) input checks) =
      [checks ⟨3 * gates, by omega⟩,
       checks ⟨3 * gates + 1, by omega⟩,
       checks ⟨3 * gates + 2, by omega⟩] := by
  unfold gateChecks
  simp only [checkCarrierValuation, coherentExtension,
    CarrierValuation.sourceLockAt, CarrierValuation.occurrenceAt,
    coherentOccurrences_snoc_left,
    coherentOccurrences_snoc_right, Program.eval_snoc_castSucc,
    sourceCheckIndex_left, sourceCheckIndex_right]
  rw [sourceCheck_coherentLock, sourceCheck_coherentLock]
  rw [Program.eval_snoc_last]
  unfold Gate.eval
  rw [traceCheck_coherentLock]
  congr 2

private theorem listOfFn_add_three (count : Nat)
    (valuation : Valuation (count + 3)) :
    List.ofFn
          (fun index : Fin count =>
            valuation (Fin.castAdd 3 index)) ++
        [valuation ⟨count, by omega⟩,
         valuation ⟨count + 1, by omega⟩,
         valuation ⟨count + 2, by omega⟩] =
      List.ofFn valuation := by
  apply List.ext_getElem
  · simp
  · intro index leftWithin rightWithin
    rw [List.getElem_ofFn]
    by_cases inPrefix : index < count
    · simp [inPrefix]
    · have cases : index = count ∨
          index = count + 1 ∨ index = count + 2 := by
        simp only [List.length_append, List.length_ofFn,
          List.length_cons, List.length_nil] at leftWithin
        omega
      rcases cases with equal | equal | equal
      · subst index
        simp
      · subst index
        simp
      · subst index
        simp

private theorem distinguishedChecks_checkCarrierValuation
    {inputs gates : Nat} (program : Program inputs gates)
    (input : Valuation inputs) (checks : Valuation (3 * gates)) :
    distinguishedChecks program
        (checkCarrierValuation program input checks) =
      List.ofFn checks := by
  induction program with
  | empty =>
      rfl
  | @snoc gates initial gate ih =>
      rw [distinguishedChecks,
        checkCarrierValuation_restrict,
        ih,
        gateChecks_checkCarrierValuation]
      simpa [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
        listOfFn_add_three (3 * gates) checks

private def checkRealization {inputs : Nat}
    (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount)) :
    Valuation (carrierWidth inputs circuit.gateCount) :=
  flattenCarrier
    (checkCarrierValuation circuit.program (fun _ => false) checks)

private theorem macroCheckSource_checkRealization
    {inputs : Nat} (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount))
    (index : Fin (3 * circuit.gateCount)) :
    let assembly :=
      macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
    (macroCheckSource circuit index).eval
        (checkRealization circuit checks)
        (assembly.program.eval (checkRealization circuit checks)) =
      checks index := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  let realized := checkRealization circuit checks
  have sourceValues :
      List.ofFn (fun index =>
          (macroCheckSource circuit index).eval realized
            (assembly.program.eval realized)) =
        checkSourceValues assembly.program assembly.checks realized :=
    macroCheckSource_values circuit realized
  have assemblyValues :
      checkSourceValues assembly.program assembly.checks realized =
        distinguishedChecks circuit.program
          (checkCarrierValuation circuit.program (fun _ => false)
            checks) := by
    rw [macroAssembly_check_values]
    rw [show unflattenCarrier realized =
        checkCarrierValuation circuit.program (fun _ => false)
          checks by
      dsimp only [realized, checkRealization]
      exact unflatten_flatten _]
    rw [restrictCarrier_refl]
  have listEqual :
      List.ofFn (fun index =>
          (macroCheckSource circuit index).eval realized
            (assembly.program.eval realized)) =
        List.ofFn checks := by
    rw [sourceValues, assemblyValues,
      distinguishedChecks_checkCarrierValuation]
  have pointEqual := congrArg
    (fun items => items[index.val]?) listEqual
  simpa [realized] using pointEqual

private theorem exposeRenameInputs_semantics
    {fromInputs toInputs gates : Nat}
    (program : Program fromInputs gates)
    (rename : Fin fromInputs → Fin toInputs)
    (input : Valuation toInputs) (output : Fin gates) :
    (exposeAllGates (program.renameInputs rename)).semantics
        input output =
      (exposeAllGates program).semantics
        (fun index => input (rename index)) output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [exposeAllGates_source, exposeAllGates_source]
  change
    (program.renameInputs rename).eval input output =
      program.eval (fun index => input (rename index)) output
  exact Program.eval_renameInputs program rename input output

private theorem exposeRenameCast_conditions
    {leftInputs rightInputs gates : Nat}
    (equal : leftInputs = rightInputs)
    (program : Program leftInputs gates)
    (conditions : BaselineOutputConditions (exposeAllGates program)) :
    BaselineOutputConditions
      (exposeAllGates (program.renameInputs (Fin.cast equal))) := by
  cases equal
  constructor
  · intro output
    obtain ⟨left, right, different⟩ :=
      conditions.nonconstant output
    refine ⟨left, right, ?_⟩
    rw [exposeRenameInputs_semantics, exposeRenameInputs_semantics]
    have leftEqual :
        (fun index => left (Fin.cast rfl index)) = left := by
      funext index
      apply congrArg left
      apply Fin.ext
      rfl
    have rightEqual :
        (fun index => right (Fin.cast rfl index)) = right := by
      funext index
      apply congrArg right
      apply Fin.ext
      rfl
    rw [leftEqual, rightEqual]
    exact different
  · intro output input
    obtain ⟨valuation, different⟩ :=
      conditions.notPositiveProjection output input
    refine ⟨valuation, ?_⟩
    rw [exposeRenameInputs_semantics]
    have valuationEqual :
        (fun index => valuation (Fin.cast rfl index)) = valuation := by
      funext index
      apply congrArg valuation
      apply Fin.ext
      rfl
    rw [valuationEqual]
    exact different
  · intro leftOutput rightOutput outputDifferent
    obtain ⟨valuation, different⟩ :=
      conditions.pairwiseDistinct outputDifferent
    refine ⟨valuation, ?_⟩
    rw [exposeRenameInputs_semantics, exposeRenameInputs_semantics]
    have valuationEqual :
        (fun index => valuation (Fin.cast rfl index)) = valuation := by
      funext index
      apply congrArg valuation
      apply Fin.ext
      rfl
    rw [valuationEqual]
    exact different

private theorem exposeRenameCast_essential
    {leftInputs rightInputs gates : Nat}
    (equal : leftInputs = rightInputs)
    (program : Program leftInputs gates)
    (target : Fin leftInputs) (output : Fin gates)
    (essential :
      OutputEssentialAt (exposeAllGates program) target output) :
    OutputEssentialAt
      (exposeAllGates (program.renameInputs (Fin.cast equal)))
      (Fin.cast equal target) output := by
  cases equal
  obtain ⟨left, right, differs, semanticDifferent⟩ := essential
  refine ⟨left, right, differs, ?_⟩
  rw [exposeRenameInputs_semantics, exposeRenameInputs_semantics]
  have leftEqual :
      (fun index => left (Fin.cast rfl index)) = left := by
    funext index
    apply congrArg left
    apply Fin.ext
    rfl
  have rightEqual :
      (fun index => right (Fin.cast rfl index)) = right := by
    funext index
    apply congrArg right
    apply Fin.ext
    rfl
  rw [leftEqual, rightEqual]
  exact semanticDifferent

private theorem nonemptyPrefixAssembly_lastTwoEssential_of_pos
    (tailChecks : Nat) (positive : 0 < tailChecks) :
    ∀ output,
      OutputEssentialAt
          (exposeAllGates
            (nonemptyPrefixAssembly tailChecks).program)
          (Fin.last tailChecks) output ∧
        OutputEssentialAt
          (exposeAllGates
            (nonemptyPrefixAssembly tailChecks).program)
          ⟨tailChecks - 1, by omega⟩ output := by
  cases tailChecks with
  | zero =>
      exact False.elim (Nat.not_lt_zero 0 positive)
  | succ tailChecks =>
      intro output
      obtain ⟨lastEssential, secondEssential⟩ :=
        nonemptyPrefixAssembly_lastTwoEssential tailChecks output
      constructor
      · exact lastEssential
      · have targetEqual :
            (⟨tailChecks, by omega⟩ : Fin (tailChecks + 2)) =
              ⟨tailChecks + 1 - 1, by omega⟩ := by
          apply Fin.ext
          simp
        rw [← targetEqual]
        exact secondEssential

private theorem circuitPrefixProgram_conditions {inputs : Nat}
    (circuit : Circuit inputs) :
    BaselineOutputConditions
      (exposeAllGates (circuitPrefixCandidate circuit).program) := by
  change
    BaselineOutputConditions
      (exposeAllGates
        ((nonemptyPrefixAssembly (checkTailCount circuit)).program.renameInputs
            (fun index =>
              Fin.cast (checkTailCount_add_one circuit) index)))
  exact exposeRenameCast_conditions
    (checkTailCount_add_one circuit)
    (nonemptyPrefixAssembly (checkTailCount circuit)).program
    (nonemptyPrefixAssembly_conditions (checkTailCount circuit))

private def rightAnchorCheck {inputs : Nat}
    (circuit : Circuit inputs) :
    Fin (3 * circuit.gateCount) :=
  ⟨3 * circuit.gateCount - 2, by
    have positive : 0 < circuit.gateCount :=
      Nat.zero_lt_of_lt circuit.outputGate.isLt
    omega⟩

private def traceAnchorCheck {inputs : Nat}
    (circuit : Circuit inputs) :
    Fin (3 * circuit.gateCount) :=
  ⟨3 * circuit.gateCount - 1, by
    have positive : 0 < circuit.gateCount :=
      Nat.zero_lt_of_lt circuit.outputGate.isLt
    omega⟩

private theorem circuitPrefixProgram_anchorEssential
    {inputs : Nat} (circuit : Circuit inputs)
    (output : Fin (2 * checkTailCount circuit)) :
    OutputEssentialAt
        (exposeAllGates (circuitPrefixCandidate circuit).program)
        (traceAnchorCheck circuit) output ∧
      OutputEssentialAt
        (exposeAllGates (circuitPrefixCandidate circuit).program)
        (rightAnchorCheck circuit) output := by
  have gatesPositive : 0 < circuit.gateCount :=
    Nat.zero_lt_of_lt circuit.outputGate.isLt
  have tailPositive : 0 < checkTailCount circuit := by
    unfold checkTailCount
    omega
  obtain ⟨traceEssential, rightEssential⟩ :=
    nonemptyPrefixAssembly_lastTwoEssential_of_pos
      (checkTailCount circuit) tailPositive output
  have renamedTrace :=
    exposeRenameCast_essential
      (checkTailCount_add_one circuit)
      (nonemptyPrefixAssembly (checkTailCount circuit)).program
      (Fin.last (checkTailCount circuit)) output traceEssential
  have renamedRight :=
    exposeRenameCast_essential
      (checkTailCount_add_one circuit)
      (nonemptyPrefixAssembly (checkTailCount circuit)).program
      ⟨checkTailCount circuit - 1, by omega⟩ output rightEssential
  have prefixProgramEqual :
      (circuitPrefixCandidate circuit).program =
        (nonemptyPrefixAssembly
            (checkTailCount circuit)).program.renameInputs
          (fun index =>
            Fin.cast (checkTailCount_add_one circuit) index) := rfl
  have traceTargetEqual :
      Fin.cast (checkTailCount_add_one circuit)
          (Fin.last (checkTailCount circuit)) =
        traceAnchorCheck circuit := by
    apply Fin.ext
    simp [traceAnchorCheck, checkTailCount]
  have rightTargetEqual :
      Fin.cast (checkTailCount_add_one circuit)
          ⟨checkTailCount circuit - 1, by omega⟩ =
        rightAnchorCheck circuit := by
    apply Fin.ext
    simp [rightAnchorCheck, checkTailCount]
    omega
  rw [traceTargetEqual] at renamedTrace
  rw [rightTargetEqual] at renamedRight
  rw [prefixProgramEqual]
  constructor
  · exact renamedTrace
  · exact renamedRight

private def lastGateCoordinate {inputs : Nat}
    (circuit : Circuit inputs) : Fin circuit.gateCount :=
  ⟨circuit.gateCount - 1, by
    have positive : 0 < circuit.gateCount :=
      Nat.zero_lt_of_lt circuit.outputGate.isLt
    omega⟩

private def rightAnchorLock {inputs : Nat}
    (circuit : Circuit inputs) :
    Fin (carrierWidth inputs circuit.gateCount) :=
  sourceLockSlot
    (occurrenceCoordinate (lastGateCoordinate circuit) .right)

private def traceAnchorLock {inputs : Nat}
    (circuit : Circuit inputs) :
    Fin (carrierWidth inputs circuit.gateCount) :=
  traceLockSlot (inputs := inputs) (lastGateCoordinate circuit)

private theorem sourceCheckIndex_injective {gates : Nat} :
    Function.Injective
      (sourceCheckIndex :
        Fin (2 * gates) → Fin (3 * gates)) := by
  intro left right equal
  apply Fin.ext
  have valueEqual := congrArg Fin.val equal
  dsimp only [sourceCheckIndex] at valueEqual
  omega

private theorem traceCheckIndex_injective {gates : Nat} :
    Function.Injective
      (traceCheckIndex : Fin gates → Fin (3 * gates)) := by
  intro left right equal
  apply Fin.ext
  have valueEqual := congrArg Fin.val equal
  dsimp only [traceCheckIndex] at valueEqual
  omega

private theorem finalRight_sourceCheckIndex {inputs : Nat}
    (circuit : Circuit inputs) :
    sourceCheckIndex
        (occurrenceCoordinate (lastGateCoordinate circuit) .right) =
      rightAnchorCheck circuit := by
  have positive : 0 < circuit.gateCount :=
    Nat.zero_lt_of_lt circuit.outputGate.isLt
  rw [sourceCheckIndex_right]
  apply Fin.ext
  simp [lastGateCoordinate, rightAnchorCheck]
  omega

private theorem finalTrace_traceCheckIndex {inputs : Nat}
    (circuit : Circuit inputs) :
    traceCheckIndex (lastGateCoordinate circuit) =
      traceAnchorCheck circuit := by
  have positive : 0 < circuit.gateCount :=
    Nat.zero_lt_of_lt circuit.outputGate.isLt
  apply Fin.ext
  simp [traceCheckIndex, lastGateCoordinate, traceAnchorCheck]
  omega

private theorem traceCheckIndex_ne_rightAnchor {inputs : Nat}
    (circuit : Circuit inputs) (gate : Fin circuit.gateCount) :
    traceCheckIndex gate ≠ rightAnchorCheck circuit := by
  intro equal
  have valueEqual := congrArg Fin.val equal
  simp [traceCheckIndex, rightAnchorCheck] at valueEqual
  have gateWithin := gate.isLt
  omega

private theorem sourceCheckIndex_ne_traceAnchor {inputs : Nat}
    (circuit : Circuit inputs)
    (occurrence : Fin (2 * circuit.gateCount)) :
    sourceCheckIndex occurrence ≠ traceAnchorCheck circuit := by
  intro equal
  have valueEqual := congrArg Fin.val equal
  simp [sourceCheckIndex, traceAnchorCheck] at valueEqual
  have occurrenceWithin := occurrence.isLt
  have gatesPositive : 0 < circuit.gateCount :=
    Nat.zero_lt_of_lt circuit.outputGate.isLt
  omega

private theorem checkRealization_rightValue {inputs : Nat}
    (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount)) :
    checkRealization circuit checks (rightAnchorLock circuit) =
      checks (rightAnchorCheck circuit) := by
  rw [checkRealization, rightAnchorLock, flattenCarrier_sourceLock]
  exact congrArg checks (finalRight_sourceCheckIndex circuit)

private theorem checkRealization_traceValue {inputs : Nat}
    (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount)) :
    checkRealization circuit checks (traceAnchorLock circuit) =
      checks (traceAnchorCheck circuit) := by
  rw [checkRealization, traceAnchorLock, flattenCarrier_traceLock]
  exact congrArg checks (finalTrace_traceCheckIndex circuit)

private theorem checkRealization_primaryValue {inputs : Nat}
    (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount))
    (coordinate : Fin inputs) :
    checkRealization circuit checks
        (primarySlot (gates := circuit.gateCount) coordinate) =
      false := by
  rw [checkRealization, flattenCarrier_primary]
  rfl

private theorem checkRealization_gateValue {inputs : Nat}
    (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount))
    (coordinate : Fin circuit.gateCount) :
    checkRealization circuit checks
        (traceSlot (inputs := inputs) coordinate) =
      circuit.program.eval (fun _ => false) coordinate := by
  rw [checkRealization, flattenCarrier_trace]
  rfl

private theorem checkRealization_occurrenceValue {inputs : Nat}
    (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount))
    (coordinate : Fin (2 * circuit.gateCount)) :
    checkRealization circuit checks
        (occurrenceSlot (inputs := inputs) coordinate) =
      coherentOccurrences circuit.program (fun _ => false) coordinate := by
  rw [checkRealization, flattenCarrier_occurrence]
  rfl

private theorem checkRealization_sourceLockValue {inputs : Nat}
    (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount))
    (coordinate : Fin (2 * circuit.gateCount)) :
    checkRealization circuit checks
        (sourceLockSlot (inputs := inputs) coordinate) =
      checks (sourceCheckIndex coordinate) := by
  rw [checkRealization, flattenCarrier_sourceLock]
  rfl

private theorem checkRealization_traceLockValue {inputs : Nat}
    (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount))
    (coordinate : Fin circuit.gateCount) :
    checkRealization circuit checks
        (traceLockSlot (inputs := inputs) coordinate) =
      checks (traceCheckIndex coordinate) := by
  rw [checkRealization, flattenCarrier_traceLock]
  rfl

private theorem checkRealization_finalValue {inputs : Nat}
    (circuit : Circuit inputs)
    (checks : Valuation (3 * circuit.gateCount)) :
    checkRealization circuit checks
        (finalLockSlot inputs circuit.gateCount) =
      true := by
  rw [checkRealization, flattenCarrier_finalLock]
  rfl

private theorem checkRealization_differsOnlyAtRight
    {inputs : Nat} (circuit : Circuit inputs)
    (left right : Valuation (3 * circuit.gateCount))
    (differs : DiffersOnlyAt (rightAnchorCheck circuit) left right) :
    DiffersOnlyAt (rightAnchorLock circuit)
      (checkRealization circuit left)
      (checkRealization circuit right) := by
  constructor
  · rw [checkRealization_rightValue, checkRealization_rightValue]
    exact differs.1
  · intro index indexNeTarget
    generalize slotEqual : decodeCarrierSlot index = slot
    have encoded : slot.encode = index := by
      rw [← slotEqual]
      exact encode_decode index
    rw [← encoded] at indexNeTarget ⊢
    cases slot with
    | primary coordinate =>
        rw [show (CarrierSlot.primary coordinate).encode =
            primarySlot (gates := circuit.gateCount) coordinate from rfl,
          checkRealization_primaryValue,
          checkRealization_primaryValue]
    | trace coordinate =>
        rw [show (CarrierSlot.trace coordinate).encode =
            traceSlot (inputs := inputs) coordinate from rfl,
          checkRealization_gateValue,
          checkRealization_gateValue]
    | occurrence coordinate =>
        rw [show (CarrierSlot.occurrence coordinate).encode =
            occurrenceSlot (inputs := inputs) coordinate from rfl,
          checkRealization_occurrenceValue,
          checkRealization_occurrenceValue]
    | sourceLock coordinate =>
        rw [show (CarrierSlot.sourceLock coordinate).encode =
            sourceLockSlot (inputs := inputs) coordinate from rfl,
          checkRealization_sourceLockValue,
          checkRealization_sourceLockValue]
        change
          left (sourceCheckIndex coordinate) =
            right (sourceCheckIndex coordinate)
        apply differs.2
        intro checkEqual
        have coordinateEqual :
            coordinate =
              occurrenceCoordinate (lastGateCoordinate circuit) .right :=
          sourceCheckIndex_injective
            (checkEqual.trans
              (finalRight_sourceCheckIndex circuit).symm)
        change
          (CarrierSlot.sourceLock coordinate).encode ≠
            rightAnchorLock circuit at indexNeTarget
        apply indexNeTarget
        simp [rightAnchorLock, CarrierSlot.encode, coordinateEqual]
    | traceLock coordinate =>
        rw [show (CarrierSlot.traceLock coordinate).encode =
            traceLockSlot (inputs := inputs) coordinate from rfl,
          checkRealization_traceLockValue,
          checkRealization_traceLockValue]
        change
          left (traceCheckIndex coordinate) =
            right (traceCheckIndex coordinate)
        exact differs.2 (traceCheckIndex coordinate)
          (traceCheckIndex_ne_rightAnchor circuit coordinate)
    | finalLock =>
        rw [show (CarrierSlot.finalLock :
              CarrierSlot inputs circuit.gateCount).encode =
            finalLockSlot inputs circuit.gateCount from rfl,
          checkRealization_finalValue,
          checkRealization_finalValue]

private theorem checkRealization_differsOnlyAtTrace
    {inputs : Nat} (circuit : Circuit inputs)
    (left right : Valuation (3 * circuit.gateCount))
    (differs : DiffersOnlyAt (traceAnchorCheck circuit) left right) :
    DiffersOnlyAt (traceAnchorLock circuit)
      (checkRealization circuit left)
      (checkRealization circuit right) := by
  constructor
  · rw [checkRealization_traceValue, checkRealization_traceValue]
    exact differs.1
  · intro index indexNeTarget
    generalize slotEqual : decodeCarrierSlot index = slot
    have encoded : slot.encode = index := by
      rw [← slotEqual]
      exact encode_decode index
    rw [← encoded] at indexNeTarget ⊢
    cases slot with
    | primary coordinate =>
        rw [show (CarrierSlot.primary coordinate).encode =
            primarySlot (gates := circuit.gateCount) coordinate from rfl,
          checkRealization_primaryValue,
          checkRealization_primaryValue]
    | trace coordinate =>
        rw [show (CarrierSlot.trace coordinate).encode =
            traceSlot (inputs := inputs) coordinate from rfl,
          checkRealization_gateValue,
          checkRealization_gateValue]
    | occurrence coordinate =>
        rw [show (CarrierSlot.occurrence coordinate).encode =
            occurrenceSlot (inputs := inputs) coordinate from rfl,
          checkRealization_occurrenceValue,
          checkRealization_occurrenceValue]
    | sourceLock coordinate =>
        rw [show (CarrierSlot.sourceLock coordinate).encode =
            sourceLockSlot (inputs := inputs) coordinate from rfl,
          checkRealization_sourceLockValue,
          checkRealization_sourceLockValue]
        change
          left (sourceCheckIndex coordinate) =
            right (sourceCheckIndex coordinate)
        exact differs.2 (sourceCheckIndex coordinate)
          (sourceCheckIndex_ne_traceAnchor circuit coordinate)
    | traceLock coordinate =>
        rw [show (CarrierSlot.traceLock coordinate).encode =
            traceLockSlot (inputs := inputs) coordinate from rfl,
          checkRealization_traceLockValue,
          checkRealization_traceLockValue]
        change
          left (traceCheckIndex coordinate) =
            right (traceCheckIndex coordinate)
        apply differs.2
        intro checkEqual
        have coordinateEqual :
            coordinate = lastGateCoordinate circuit :=
          traceCheckIndex_injective
            (checkEqual.trans
              (finalTrace_traceCheckIndex circuit).symm)
        change
          (CarrierSlot.traceLock coordinate).encode ≠
            traceAnchorLock circuit at indexNeTarget
        apply indexNeTarget
        simp [traceAnchorLock, CarrierSlot.encode, coordinateEqual]
    | finalLock =>
        rw [show (CarrierSlot.finalLock :
              CarrierSlot inputs circuit.gateCount).encode =
            finalLockSlot inputs circuit.gateCount from rfl,
          checkRealization_finalValue,
          checkRealization_finalValue]

private def circuitPrefixRightLift {inputs : Nat}
    (circuit : Circuit inputs) :
    let assembly :=
      macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
    LocalBlockLift assembly.program (macroCheckSource circuit)
      (rightAnchorCheck circuit) (rightAnchorLock circuit) where
  lift := checkRealization circuit
  bindingValues := by
    intro checks index
    exact macroCheckSource_checkRealization circuit checks index
  targetValue := by
    intro checks
    exact checkRealization_rightValue circuit checks
  preservesDifference := by
    intro left right differs
    exact checkRealization_differsOnlyAtRight circuit left right differs

private def circuitPrefixTraceLift {inputs : Nat}
    (circuit : Circuit inputs) :
    let assembly :=
      macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
    LocalBlockLift assembly.program (macroCheckSource circuit)
      (traceAnchorCheck circuit) (traceAnchorLock circuit) where
  lift := checkRealization circuit
  bindingValues := by
    intro checks index
    exact macroCheckSource_checkRealization circuit checks index
  targetValue := by
    intro checks
    exact checkRealization_traceValue circuit checks
  preservesDifference := by
    intro left right differs
    exact checkRealization_differsOnlyAtTrace circuit left right differs

private theorem rawBaselinePrefix_anchorEssential
    {inputs : Nat} (circuit : Circuit inputs)
    (output : Fin (2 * checkTailCount circuit)) :
    OutputEssentialAt
        (exposeAllGates (rawBaselineProgram circuit))
        (traceAnchorLock circuit)
        (Fin.natAdd (macroGateCount circuit.program) output) ∧
      OutputEssentialAt
        (exposeAllGates (rawBaselineProgram circuit))
        (rightAnchorLock circuit)
        (Fin.natAdd (macroGateCount circuit.program) output) := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  obtain ⟨traceEssential, rightEssential⟩ :=
    circuitPrefixProgram_anchorEssential circuit output
  constructor
  · change
      OutputEssentialAt
        (exposeAllGates
          (appendCandidateProgram assembly.program
            (macroCheckSource circuit)
            (exposeAllGates
              (circuitPrefixCandidate circuit).program)))
        (traceAnchorLock circuit)
        (Fin.natAdd (macroGateCount circuit.program) output)
    exact appendedExpose_suffix_essential assembly.program
      (macroCheckSource circuit)
      (exposeAllGates (circuitPrefixCandidate circuit).program)
      (exposeAllGates_source _)
      (traceAnchorCheck circuit) (traceAnchorLock circuit)
      (circuitPrefixTraceLift circuit) output traceEssential
  · change
      OutputEssentialAt
        (exposeAllGates
          (appendCandidateProgram assembly.program
            (macroCheckSource circuit)
            (exposeAllGates
              (circuitPrefixCandidate circuit).program)))
        (rightAnchorLock circuit)
        (Fin.natAdd (macroGateCount circuit.program) output)
    exact appendedExpose_suffix_essential assembly.program
      (macroCheckSource circuit)
      (exposeAllGates (circuitPrefixCandidate circuit).program)
      (exposeAllGates_source _)
      (rightAnchorCheck circuit) (rightAnchorLock circuit)
      (circuitPrefixRightLift circuit) output rightEssential

private theorem rawBaselinePrefix_pairwiseDistinct
    {inputs : Nat} (circuit : Circuit inputs)
    {leftOutput rightOutput :
      Fin (2 * checkTailCount circuit)}
    (different : leftOutput ≠ rightOutput) :
    ∃ valuation,
      (exposeAllGates (rawBaselineProgram circuit)).semantics
          valuation
          (Fin.natAdd (macroGateCount circuit.program) leftOutput) ≠
        (exposeAllGates (rawBaselineProgram circuit)).semantics
          valuation
          (Fin.natAdd (macroGateCount circuit.program) rightOutput) := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  obtain ⟨checks, semanticDifferent⟩ :=
    (circuitPrefixProgram_conditions circuit).pairwiseDistinct different
  refine ⟨checkRealization circuit checks, ?_⟩
  change
    (exposeAllGates
      (appendCandidateProgram assembly.program
        (macroCheckSource circuit)
        (exposeAllGates
          (circuitPrefixCandidate circuit).program))).semantics
        (checkRealization circuit checks)
        (Fin.natAdd (macroGateCount circuit.program) leftOutput) ≠
      (exposeAllGates
        (appendCandidateProgram assembly.program
          (macroCheckSource circuit)
          (exposeAllGates
            (circuitPrefixCandidate circuit).program))).semantics
        (checkRealization circuit checks)
        (Fin.natAdd (macroGateCount circuit.program) rightOutput)
  rw [appendedExpose_suffix_semantics assembly.program
      (macroCheckSource circuit)
      (exposeAllGates (circuitPrefixCandidate circuit).program)
      (exposeAllGates_source _),
    appendedExpose_suffix_semantics assembly.program
      (macroCheckSource circuit)
      (exposeAllGates (circuitPrefixCandidate circuit).program)
      (exposeAllGates_source _)]
  have sourceValues :
      (fun index =>
        (macroCheckSource circuit index).eval
          (checkRealization circuit checks)
          (assembly.program.eval (checkRealization circuit checks))) =
        checks := by
    funext index
    exact macroCheckSource_checkRealization circuit checks index
  rw [sourceValues]
  exact semanticDifferent

private theorem macroAssembly_snoc_output_anchorIrrelevant
    {inputs gates : Nat}
    (initial : Program inputs gates) (gate : Gate inputs gates)
    (output : Fin (macroGateCount (initial.snoc gate))) :
    OutputIrrelevantAt
        (exposeAllGates
          (macroAssembly (initial.snoc gate)
            (Nat.le_refl (gates + 1))).program)
        (traceLockSlot (inputs := inputs) (Fin.last gates)) output ∨
      OutputIrrelevantAt
        (exposeAllGates
          (macroAssembly (initial.snoc gate)
            (Nat.le_refl (gates + 1))).program)
        (sourceLockSlot (inputs := inputs)
          (occurrenceCoordinate (Fin.last gates) .right)) output := by
  let earlierWithin : gates ≤ gates + 1 := Nat.le_succ gates
  let coordinate : Fin (gates + 1) := Fin.last gates
  let earlier := macroAssembly initial earlierWithin
  let left := appendSourceMacro earlier.program gate.left
    earlierWithin coordinate .left
  let right := appendSourceMacro left.program gate.right
    earlierWithin coordinate .right
  let trace := appendTraceMacro right.program coordinate
  let traceLock := traceLockSlot (inputs := inputs) coordinate
  let rightLock :=
    sourceLockSlot (inputs := inputs)
      (occurrenceCoordinate coordinate .right)
  have earlierAvoidsTrace :
      programAvoidsInput traceLock earlier.program := by
    exact macroAssembly_avoidsTraceLock_after initial earlierWithin
      coordinate (Nat.le_refl gates)
  have leftAvoidsTrace :
      programAvoidsInput traceLock left.program := by
    exact appendSourceMacro_avoidsTraceLock earlier.program gate.left
      earlierWithin coordinate .left coordinate earlierAvoidsTrace
  have rightAvoidsTrace :
      programAvoidsInput traceLock right.program := by
    exact appendSourceMacro_avoidsTraceLock left.program gate.right
      earlierWithin coordinate .right coordinate leftAvoidsTrace
  let traceBinding : Fin 4 →
      Source (carrierWidth inputs (gates + 1))
        (((macroGateCount initial +
            sourceMacroGateCount gate.left) +
          sourceMacroGateCount gate.right)) :=
    binding4
      (.input traceLock)
      (.input (traceSlot (inputs := inputs) coordinate))
      (.input (occurrenceSlot (inputs := inputs)
        (occurrenceCoordinate coordinate .left)))
      (.input (occurrenceSlot (inputs := inputs)
        (occurrenceCoordinate coordinate .right)))
  have traceBindingIndependent :
      ∀ first second,
        (∀ index, index ≠ rightLock → first index = second index) →
          ∀ bindingIndex,
            (traceBinding bindingIndex).eval first
                (right.program.eval first) =
              (traceBinding bindingIndex).eval second
                (right.program.eval second) := by
    intro first second equalAway bindingIndex
    dsimp only [traceBinding]
    unfold binding4
    split
    · apply equalAway
      simpa [traceLock, rightLock, CarrierSlot.encode] using
        (carrierSlot_encode_ne
          (CarrierSlot.traceLock coordinate)
          (CarrierSlot.sourceLock
            (occurrenceCoordinate coordinate .right)) (by simp))
    · split
      · apply equalAway
        simpa [rightLock, CarrierSlot.encode] using
          (carrierSlot_encode_ne
            (CarrierSlot.trace coordinate)
            (CarrierSlot.sourceLock
              (occurrenceCoordinate coordinate .right)) (by simp))
      · split
        · apply equalAway
          simpa [rightLock, CarrierSlot.encode] using
            (carrierSlot_encode_ne
              (CarrierSlot.occurrence
                (occurrenceCoordinate coordinate .left))
              (CarrierSlot.sourceLock
                (occurrenceCoordinate coordinate .right)) (by simp))
        · apply equalAway
          simpa [rightLock, CarrierSlot.encode] using
            (carrierSlot_encode_ne
              (CarrierSlot.occurrence
                (occurrenceCoordinate coordinate .right))
              (CarrierSlot.sourceLock
                (occurrenceCoordinate coordinate .right)) (by simp))
  change
    OutputIrrelevantAt (exposeAllGates trace.program)
        traceLock output ∨
      OutputIrrelevantAt (exposeAllGates trace.program)
        rightLock output
  cases finSum_decompose output with
  | inl prefixCase =>
      rcases prefixCase with ⟨prefixOutput, outputEqual⟩
      subst output
      apply Or.inl
      change
        OutputIrrelevantAt
          (exposeAllGates
            (appendCandidateProgram right.program traceBinding traceDirect))
          traceLock (Fin.castAdd 18 prefixOutput)
      exact appendedExpose_prefix_irrelevant right.program traceBinding
        traceDirect traceLock rightAvoidsTrace prefixOutput
  | inr suffixCase =>
      rcases suffixCase with ⟨suffixOutput, outputEqual⟩
      subst output
      apply Or.inr
      change
        OutputIrrelevantAt
          (exposeAllGates
            (appendCandidateProgram right.program traceBinding traceDirect))
          rightLock
          (Fin.natAdd
            (((macroGateCount initial +
                sourceMacroGateCount gate.left) +
              sourceMacroGateCount gate.right))
            suffixOutput)
      exact appendedExpose_suffix_irrelevant right.program traceBinding
        traceDirect traceDirect_output_source rightLock
        traceBindingIndependent suffixOutput

private theorem macroAssembly_output_anchorIrrelevant
    {inputs : Nat} (circuit : Circuit inputs)
    (output : Fin (macroGateCount circuit.program)) :
    let assembly :=
      macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
    OutputIrrelevantAt (exposeAllGates assembly.program)
        (traceAnchorLock circuit) output ∨
      OutputIrrelevantAt (exposeAllGates assembly.program)
        (rightAnchorLock circuit) output := by
  rcases circuit with ⟨gateCount, program, outputGate⟩
  cases program with
  | empty =>
      exact Fin.elim0 outputGate
  | @snoc gates initial gate =>
      have coordinateEqual :
          (⟨gates, by omega⟩ : Fin (gates + 1)) =
            Fin.last gates := by
        apply Fin.ext
        rfl
      change
        OutputIrrelevantAt
            (exposeAllGates
              (macroAssembly (initial.snoc gate)
                (Nat.le_refl (gates + 1))).program)
            (traceLockSlot (inputs := inputs) ⟨gates, by omega⟩)
            output ∨
          OutputIrrelevantAt
            (exposeAllGates
              (macroAssembly (initial.snoc gate)
                (Nat.le_refl (gates + 1))).program)
            (sourceLockSlot (inputs := inputs)
              (occurrenceCoordinate
                (⟨gates, by omega⟩ : Fin (gates + 1)) .right))
            output
      rw [coordinateEqual]
      exact macroAssembly_snoc_output_anchorIrrelevant initial gate output

private theorem rawBaselineMacro_anchorIrrelevant
    {inputs : Nat} (circuit : Circuit inputs)
    (output : Fin (macroGateCount circuit.program)) :
    OutputIrrelevantAt
        (exposeAllGates (rawBaselineProgram circuit))
        (traceAnchorLock circuit)
        (Fin.castAdd (2 * checkTailCount circuit) output) ∨
      OutputIrrelevantAt
        (exposeAllGates (rawBaselineProgram circuit))
        (rightAnchorLock circuit)
        (Fin.castAdd (2 * checkTailCount circuit) output) := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  obtain traceIrrelevant | rightIrrelevant :=
    macroAssembly_output_anchorIrrelevant circuit output
  · apply Or.inl
    change
      OutputIrrelevantAt
        (exposeAllGates
          (appendCandidateProgram assembly.program
            (macroCheckSource circuit)
            (exposeAllGates
              (circuitPrefixCandidate circuit).program)))
        (traceAnchorLock circuit)
        (Fin.castAdd (2 * checkTailCount circuit) output)
    exact appendedExpose_prefix_irrelevant_of_irrelevant
      assembly.program (macroCheckSource circuit)
      (exposeAllGates (circuitPrefixCandidate circuit).program)
      (traceAnchorLock circuit) output traceIrrelevant
  · apply Or.inr
    change
      OutputIrrelevantAt
        (exposeAllGates
          (appendCandidateProgram assembly.program
            (macroCheckSource circuit)
            (exposeAllGates
              (circuitPrefixCandidate circuit).program)))
        (rightAnchorLock circuit)
        (Fin.castAdd (2 * checkTailCount circuit) output)
    exact appendedExpose_prefix_irrelevant_of_irrelevant
      assembly.program (macroCheckSource circuit)
      (exposeAllGates (circuitPrefixCandidate circuit).program)
      (rightAnchorLock circuit) output rightIrrelevant

private theorem rightAnchorLock_ne_traceAnchorLock
    {inputs : Nat} (circuit : Circuit inputs) :
    rightAnchorLock circuit ≠ traceAnchorLock circuit := by
  simpa [rightAnchorLock, traceAnchorLock, CarrierSlot.encode] using
    (carrierSlot_encode_ne
      (CarrierSlot.sourceLock
        (occurrenceCoordinate (lastGateCoordinate circuit) .right))
      (CarrierSlot.traceLock (lastGateCoordinate circuit)) (by simp))

private theorem rawBaseline_macro_semantics
    {inputs : Nat} (circuit : Circuit inputs)
    (input : Valuation (carrierWidth inputs circuit.gateCount))
    (output : Fin (macroGateCount circuit.program)) :
    (exposeAllGates (rawBaselineProgram circuit)).semantics input
        (Fin.castAdd (2 * checkTailCount circuit) output) =
      (exposeAllGates
        (macroAssembly circuit.program
          (Nat.le_refl circuit.gateCount)).program).semantics
        input output := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  change
    (exposeAllGates
      (appendCandidateProgram assembly.program
        (macroCheckSource circuit)
        (exposeAllGates
          (circuitPrefixCandidate circuit).program))).semantics input
        (Fin.castAdd (2 * checkTailCount circuit) output) =
      (exposeAllGates assembly.program).semantics input output
  exact appendedExpose_prefix_semantics assembly.program
    (macroCheckSource circuit)
    (exposeAllGates (circuitPrefixCandidate circuit).program)
    input output

private theorem rawBaseline_conditions
    {inputs : Nat} (circuit : Circuit inputs) :
    BaselineOutputConditions
      (exposeAllGates (rawBaselineProgram circuit)) := by
  let assembly :=
    macroAssembly circuit.program (Nat.le_refl circuit.gateCount)
  have macroConditions :
      BaselineOutputConditions (exposeAllGates assembly.program) :=
    macroAssembly_conditions circuit.program
      (Nat.le_refl circuit.gateCount)
  constructor
  · intro output
    cases finSum_decompose output with
    | inl macroCase =>
        rcases macroCase with ⟨macroOutput, outputEqual⟩
        subst output
        obtain ⟨left, right, semanticDifferent⟩ :=
          macroConditions.nonconstant macroOutput
        refine ⟨left, right, ?_⟩
        rw [rawBaseline_macro_semantics,
          rawBaseline_macro_semantics]
        exact semanticDifferent
    | inr prefixCase =>
        rcases prefixCase with ⟨prefixOutput, outputEqual⟩
        subst output
        exact
          (rawBaselinePrefix_anchorEssential circuit prefixOutput).1.nonconstant
  · intro output queried
    cases finSum_decompose output with
    | inl macroCase =>
        rcases macroCase with ⟨macroOutput, outputEqual⟩
        subst output
        obtain ⟨valuation, semanticDifferent⟩ :=
          macroConditions.notPositiveProjection macroOutput queried
        refine ⟨valuation, ?_⟩
        rw [rawBaseline_macro_semantics]
        exact semanticDifferent
    | inr prefixCase =>
        rcases prefixCase with ⟨prefixOutput, outputEqual⟩
        subst output
        obtain ⟨traceEssential, rightEssential⟩ :=
          rawBaselinePrefix_anchorEssential circuit prefixOutput
        by_cases queriedTrace :
            queried = traceAnchorLock circuit
        · exact rightEssential.notProjection_of_ne (by
            rw [queriedTrace]
            exact rightAnchorLock_ne_traceAnchorLock circuit)
        · exact traceEssential.notProjection_of_ne (Ne.symm queriedTrace)
  · intro leftOutput rightOutput outputDifferent
    cases finSum_decompose leftOutput with
    | inl leftMacroCase =>
        rcases leftMacroCase with ⟨leftMacro, leftEqual⟩
        subst leftOutput
        cases finSum_decompose rightOutput with
        | inl rightMacroCase =>
            rcases rightMacroCase with ⟨rightMacro, rightEqual⟩
            subst rightOutput
            have macroDifferent : leftMacro ≠ rightMacro := by
              intro equal
              apply outputDifferent
              exact congrArg
                (Fin.castAdd (2 * checkTailCount circuit)) equal
            obtain ⟨valuation, semanticDifferent⟩ :=
              macroConditions.pairwiseDistinct macroDifferent
            refine ⟨valuation, ?_⟩
            rw [rawBaseline_macro_semantics,
              rawBaseline_macro_semantics]
            exact semanticDifferent
        | inr rightPrefixCase =>
            rcases rightPrefixCase with ⟨rightPrefix, rightEqual⟩
            subst rightOutput
            obtain ⟨traceEssential, rightEssential⟩ :=
              rawBaselinePrefix_anchorEssential circuit rightPrefix
            obtain traceIrrelevant | rightIrrelevant :=
              rawBaselineMacro_anchorIrrelevant circuit leftMacro
            · obtain ⟨valuation, semanticDifferent⟩ :=
                essential_irrelevant_distinct traceEssential
                  traceIrrelevant
              exact ⟨valuation, fun equal =>
                semanticDifferent equal.symm⟩
            · obtain ⟨valuation, semanticDifferent⟩ :=
                essential_irrelevant_distinct rightEssential
                  rightIrrelevant
              exact ⟨valuation, fun equal =>
                semanticDifferent equal.symm⟩
    | inr leftPrefixCase =>
        rcases leftPrefixCase with ⟨leftPrefix, leftEqual⟩
        subst leftOutput
        cases finSum_decompose rightOutput with
        | inl rightMacroCase =>
            rcases rightMacroCase with ⟨rightMacro, rightEqual⟩
            subst rightOutput
            obtain ⟨traceEssential, rightEssential⟩ :=
              rawBaselinePrefix_anchorEssential circuit leftPrefix
            obtain traceIrrelevant | rightIrrelevant :=
              rawBaselineMacro_anchorIrrelevant circuit rightMacro
            · exact essential_irrelevant_distinct traceEssential
                traceIrrelevant
            · exact essential_irrelevant_distinct rightEssential
                rightIrrelevant
        | inr rightPrefixCase =>
            rcases rightPrefixCase with ⟨rightPrefix, rightEqual⟩
            subst rightOutput
            have prefixDifferent : leftPrefix ≠ rightPrefix := by
              intro equal
              apply outputDifferent
              exact congrArg
                (Fin.natAdd (macroGateCount circuit.program)) equal
            exact rawBaselinePrefix_pairwiseDistinct circuit
              prefixDifferent

private theorem exposeCastProgram_conditions
    {inputs leftGates rightGates : Nat}
    (equal : leftGates = rightGates)
    (program : Program inputs leftGates)
    (conditions :
      BaselineOutputConditions (exposeAllGates program)) :
    BaselineOutputConditions
      (exposeAllGates (castProgramGateCount equal program)) := by
  cases equal
  exact conditions

/-- Every exposed output of the complete locked-NAND baseline is
semantically nonconstant. -/
theorem baselineCandidate_outputNonconstant
    {inputs : Nat} (circuit : Circuit inputs) :
    ∀ output, OutputNonconstant (baselineCandidate circuit) output := by
  exact
    (exposeCastProgram_conditions
      (rawBaselineGateCount_eq_lockedBaselineCount circuit)
      (rawBaselineProgram circuit)
      (rawBaseline_conditions circuit)).nonconstant

/-- No exposed output of the complete locked-NAND baseline is a positive
projection of any carrier input. -/
theorem baselineCandidate_outputNotPositiveProjection
    {inputs : Nat} (circuit : Circuit inputs) :
    ∀ output,
      OutputNotPositiveProjection (baselineCandidate circuit) output := by
  exact
    (exposeCastProgram_conditions
      (rawBaselineGateCount_eq_lockedBaselineCount circuit)
      (rawBaselineProgram circuit)
      (rawBaseline_conditions circuit)).notPositiveProjection

/-- Distinct exposed coordinates of the complete locked-NAND baseline compute
distinct Boolean functions. -/
theorem baselineCandidate_outputPairwiseDistinct
    {inputs : Nat} (circuit : Circuit inputs) :
    OutputPairwiseDistinct (baselineCandidate circuit) := by
  exact
    (exposeCastProgram_conditions
      (rawBaselineGateCount_eq_lockedBaselineCount circuit)
      (rawBaselineProgram circuit)
      (rawBaseline_conditions circuit)).pairwiseDistinct

/-- The complete locked-NAND baseline satisfies all three semantic conditions
required by the exhaustive direct-wire lower bound. -/
theorem baselineCandidate_outputConditions
    {inputs : Nat} (circuit : Circuit inputs) :
    BaselineOutputConditions (baselineCandidate circuit) := by
  exact exposeCastProgram_conditions
    (rawBaselineGateCount_eq_lockedBaselineCount circuit)
    (rawBaselineProgram circuit)
    (rawBaseline_conditions circuit)

/-- The reference minimum of the square complete baseline is exactly its
source-derived gate count. -/
theorem baselineCandidate_referenceMinimum
    {inputs : Nat} (circuit : Circuit inputs) :
    referenceMinimum
        (Implementation.mk (lockedBaselineCount circuit.program)
          (baselineCandidate circuit)) =
      lockedBaselineCount circuit.program := by
  exact referenceMinimum_eq_gateCount_of_squareBaseline
    (baselineCandidate circuit)
    (baselineCandidate_outputConditions circuit)

end LockedNANDGlobalCandidates
end DirectWire
end PNP
