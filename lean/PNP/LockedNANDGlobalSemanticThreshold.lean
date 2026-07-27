/-
Copyright (c) 2026 PNP Labs.

Whole-carrier satisfiable final-lock separation and the resulting typed
locked-NAND semantic threshold.  The candidates remain the answer-independent
objects constructed in LockedNANDGlobalCandidates; satisfiability is used only
to prove their semantic branch laws.
-/

import PNP.LockedNANDGlobalUnsatisfiableFinalZero

namespace PNP
namespace DirectWire
namespace LockedNANDGlobalCandidates

open LockedNANDTrace

/-! ## Whole-carrier final-lock witnesses -/

/-- Replace only the fresh final-lock field of a tagged carrier valuation. -/
private def withFinalLock {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates) (value : Bool) :
    CarrierValuation inputs gates :=
  { primary := valuation.primary
    trace := valuation.trace
    occurrence := valuation.occurrence
    sourceLock := valuation.sourceLock
    traceLock := valuation.traceLock
    finalLock := value }

private theorem withFinalLock_restrict
    {inputs gates : Nat}
    (valuation : CarrierValuation inputs (gates + 1))
    (value : Bool) :
    (withFinalLock valuation value).restrict =
      withFinalLock valuation.restrict value := by
  rfl

private theorem gateChecks_withFinalLock
    {inputs gates : Nat} (gate : Gate inputs gates)
    (valuation : CarrierValuation inputs (gates + 1))
    (value : Bool) :
    gateChecks gate (withFinalLock valuation value) =
      gateChecks gate valuation := by
  rfl

private theorem distinguishedChecks_withFinalLock
    {inputs gates : Nat} (program : Program inputs gates)
    (valuation : CarrierValuation inputs gates) (value : Bool) :
    distinguishedChecks program (withFinalLock valuation value) =
      distinguishedChecks program valuation := by
  induction program with
  | empty => rfl
  | @snoc gates initial gate ih =>
      rw [distinguishedChecks, distinguishedChecks,
        withFinalLock_restrict, ih, gateChecks_withFinalLock]

private theorem tracePredicate_withFinalLock
    {inputs gates : Nat} (program : Program inputs gates)
    (valuation : CarrierValuation inputs gates) (value : Bool) :
    tracePredicate program (withFinalLock valuation value) =
      tracePredicate program valuation := by
  unfold tracePredicate
  rw [distinguishedChecks_withFinalLock]

/-- Flattening a tagged final-lock replacement agrees with the flat
replacement operation used by the baseline-independence theorem. -/
private theorem flattenCarrier_withFinalLock
    {inputs gates : Nat}
    (valuation : CarrierValuation inputs gates) (value : Bool) :
    flattenCarrier (withFinalLock valuation value) =
      setFinalLockValue (flattenCarrier valuation) value := by
  funext slot
  rw [← encode_decode slot]
  cases decoded : decodeCarrierSlot slot with
  | primary index =>
      rw [setFinalLockValue_nonfinal]
      · simp [flattenCarrier, withFinalLock, CarrierSlot.encode]
      · exact finalLock_fresh (.primary index) (by simp)
  | trace index =>
      rw [setFinalLockValue_nonfinal]
      · simp [flattenCarrier, withFinalLock, CarrierSlot.encode]
      · exact finalLock_fresh (.trace index) (by simp)
  | occurrence index =>
      rw [setFinalLockValue_nonfinal]
      · simp [flattenCarrier, withFinalLock, CarrierSlot.encode]
      · exact finalLock_fresh (.occurrence index) (by simp)
  | sourceLock index =>
      rw [setFinalLockValue_nonfinal]
      · simp [flattenCarrier, withFinalLock, CarrierSlot.encode]
      · exact finalLock_fresh (.sourceLock index) (by simp)
  | traceLock index =>
      rw [setFinalLockValue_nonfinal]
      · simp [flattenCarrier, withFinalLock, CarrierSlot.encode]
      · exact finalLock_fresh (.traceLock index) (by simp)
  | finalLock =>
      simp [flattenCarrier, withFinalLock, CarrierSlot.encode,
        setFinalLockValue]

private theorem fullCandidate_final_on_of_accepted
    {inputs : Nat} (circuit : Circuit inputs)
    (valuation : CarrierValuation inputs circuit.gateCount)
    (accepted :
      tracePredicate circuit.program valuation = true)
    (outputTrue : valuation.trace circuit.outputGate = true) :
    (fullCandidate circuit).semantics
        (flattenCarrier (withFinalLock valuation true))
        (conditionalFinalOutput
          (lockedBaselineCount circuit.program)) =
      true := by
  rw [fullCandidate_final_semantics_flatten, finalConjunction4_spec]
  rw [tracePredicate_withFinalLock]
  simp [withFinalLock, accepted, outputTrue]

private theorem fullCandidate_final_off
    {inputs : Nat} (circuit : Circuit inputs)
    (valuation : CarrierValuation inputs circuit.gateCount) :
    (fullCandidate circuit).semantics
        (flattenCarrier (withFinalLock valuation false))
        (conditionalFinalOutput
          (lockedBaselineCount circuit.program)) =
      false := by
  rw [fullCandidate_final_semantics_flatten, finalConjunction4_spec]
  simp [withFinalLock]

/-! ## The three satisfiable final-output conditions -/

/-- A satisfying trace makes the final coordinate depend essentially on the
fresh final lock, so it is nonconstant on the whole carrier. -/
theorem fullCandidate_final_nonconstant_of_satisfiable
    {inputs : Nat} (circuit : Circuit inputs)
    (isSatisfiable : circuit.Satisfiable) :
    OutputNonconstant (fullCandidate circuit)
      (conditionalFinalOutput
        (lockedBaselineCount circuit.program)) := by
  obtain ⟨valuation, accepted, outputTrue⟩ :=
    (satisfiable_iff_trace_extension circuit).1 isSatisfiable
  refine ⟨flattenCarrier (withFinalLock valuation true),
    flattenCarrier (withFinalLock valuation false), ?_⟩
  rw [fullCandidate_final_on_of_accepted circuit valuation
      accepted outputTrue,
    fullCandidate_final_off circuit valuation]
  decide

/-- In the satisfiable branch the final coordinate is not any positive
carrier-input projection.  The fresh-lock coordinate itself is separated by a
valuation whose output-trace bit is false; every other coordinate is separated
by toggling only the fresh final lock around one satisfying trace. -/
theorem fullCandidate_final_notPositiveProjection_of_satisfiable
    {inputs : Nat} (circuit : Circuit inputs)
    (isSatisfiable : circuit.Satisfiable) :
    OutputNotPositiveProjection (fullCandidate circuit)
      (conditionalFinalOutput
        (lockedBaselineCount circuit.program)) := by
  intro coordinate
  by_cases coordinateFinal :
      coordinate = finalLockSlot inputs circuit.gateCount
  · subst coordinate
    let witness :
        Valuation (carrierWidth inputs circuit.gateCount) :=
      fun index =>
        if index = finalLockSlot inputs circuit.gateCount
        then true else false
    have traceNotFinal :
        traceSlot (inputs := inputs) circuit.outputGate ≠
          finalLockSlot inputs circuit.gateCount := by
      exact finalLock_fresh (.trace circuit.outputGate) (by simp)
    refine ⟨witness, ?_⟩
    rw [fullCandidate_final_semantics_conjunction]
    simp [witness, traceNotFinal]
  · obtain ⟨valuation, accepted, outputTrue⟩ :=
      (satisfiable_iff_trace_extension circuit).1 isSatisfiable
    cases coordinateValue :
        flattenCarrier valuation coordinate with
    | false =>
        refine
          ⟨flattenCarrier (withFinalLock valuation true), ?_⟩
        rw [fullCandidate_final_on_of_accepted circuit valuation
            accepted outputTrue,
          flattenCarrier_withFinalLock,
          setFinalLockValue_nonfinal _ _ coordinate coordinateFinal,
          coordinateValue]
        decide
    | true =>
        refine
          ⟨flattenCarrier (withFinalLock valuation false), ?_⟩
        rw [fullCandidate_final_off circuit valuation,
          flattenCarrier_withFinalLock,
          setFinalLockValue_nonfinal _ _ coordinate coordinateFinal,
          coordinateValue]
        decide

/-- No exposed baseline coordinate computes the satisfiable final function.
The baseline is independent of the fresh lock, whereas the final coordinate
toggles when that lock is changed around a satisfying trace. -/
theorem fullCandidate_final_distinctFromBaseline_of_satisfiable
    {inputs : Nat} (circuit : Circuit inputs)
    (isSatisfiable : circuit.Satisfiable)
    (output : Fin (lockedBaselineCount circuit.program)) :
    ∃ valuation,
      (fullCandidate circuit).semantics valuation
          (baselineOutputEmbedding output) ≠
        (fullCandidate circuit).semantics valuation
          (conditionalFinalOutput
            (lockedBaselineCount circuit.program)) := by
  obtain ⟨valuation, accepted, outputTrue⟩ :=
    (satisfiable_iff_trace_extension circuit).1 isSatisfiable
  let onInput := flattenCarrier (withFinalLock valuation true)
  let offInput := flattenCarrier (withFinalLock valuation false)
  have baselineSame :
      (baselineCandidate circuit).semantics onInput output =
        (baselineCandidate circuit).semantics offInput output := by
    unfold onInput offInput
    rw [flattenCarrier_withFinalLock, flattenCarrier_withFinalLock]
    exact baselineCandidate_finalLock_irrelevant circuit
      (flattenCarrier valuation) true false output
  cases baselineOn :
      (baselineCandidate circuit).semantics onInput output with
  | false =>
      refine ⟨onInput, ?_⟩
      rw [fullCandidate_initial_semantics, baselineOn,
        fullCandidate_final_on_of_accepted circuit valuation
          accepted outputTrue]
      decide
  | true =>
      have baselineOff :
          (baselineCandidate circuit).semantics offInput output =
            true := by
        rw [← baselineSame, baselineOn]
      refine ⟨offInput, ?_⟩
      rw [fullCandidate_initial_semantics, baselineOff,
        fullCandidate_final_off circuit valuation]
      decide

/-- The real full candidate supplies the final satisfiable field required by
the six-field conditional threshold package. -/
theorem fullCandidate_satisfiableFinalConditions
    {inputs : Nat} (circuit : Circuit inputs)
    (isSatisfiable : circuit.Satisfiable) :
    ConditionalFinalOutputSatConditions
      (fullCandidate circuit) := by
  exact
    { nonconstant :=
        fullCandidate_final_nonconstant_of_satisfiable
          circuit isSatisfiable
      notPositiveProjection :=
        fullCandidate_final_notPositiveProjection_of_satisfiable
          circuit isSatisfiable
      distinctFromBaseline :=
        fullCandidate_final_distinctFromBaseline_of_satisfiable
          circuit isSatisfiable }

/-! ## Complete typed semantic threshold package -/

/-- All six conditional-boundary fields, instantiated by the same
answer-independent candidates for every finite topological NAND circuit. -/
def fullCandidateThresholdPremises
    {inputs : Nat} (circuit : Circuit inputs) :
    ConditionalThresholdBoundaryPremises
      circuit.Satisfiable
      (carrierWidth inputs circuit.gateCount)
      (lockedBaselineCount circuit.program) :=
  { baselineCandidate := baselineCandidate circuit
    fullCandidate := fullCandidate circuit
    baselineConditions := baselineCandidate_outputConditions circuit
    initialOutputsPreserved := fullCandidate_initial_semantics circuit
    unsatisfiableFinalZero :=
      fullCandidate_final_eq_false_of_unsatisfiable circuit
    satisfiableFinalConditions :=
      fullCandidate_satisfiableFinalConditions circuit }

/-- In the satisfiable branch the exhaustive minimum retains all `B` baseline
functions and at least one genuinely new final function, while the displayed
construction supplies the `B + 4` upper bound. -/
theorem fullCandidate_referenceMinimum_bounds_of_satisfiable
    {inputs : Nat} (circuit : Circuit inputs)
    (isSatisfiable : circuit.Satisfiable) :
    lockedBaselineCount circuit.program + 1 ≤
        referenceMinimum
          (Implementation.mk
            (lockedBaselineCount circuit.program + 4)
            (fullCandidate circuit)) ∧
      referenceMinimum
          (Implementation.mk
            (lockedBaselineCount circuit.program + 4)
            (fullCandidate circuit)) ≤
        lockedBaselineCount circuit.program + 4 := by
  exact
    ConditionalThresholdBoundaryPremises.fullMinimum_bounds_of_satisfiable
      (fullCandidateThresholdPremises circuit) isSatisfiable

/-- The four displayed final gates bound the exhaustive residual slack of the
real full candidate for every source circuit. -/
theorem fullCandidate_residualSlack_le_four
    {inputs : Nat} (circuit : Circuit inputs) :
    residualSlack
        (Implementation.mk
          (lockedBaselineCount circuit.program + 4)
          (fullCandidate circuit)) ≤
      4 := by
  exact
    ConditionalThresholdBoundaryPremises.fullResidualSlack_le_four
      (fullCandidateThresholdPremises circuit)

/-- Boolean existential quantification over a concrete finite list. -/
private def anyTrue {alpha : Type} :
    List alpha → (alpha → Bool) → Bool
  | [], _ => false
  | item :: items, predicate =>
      predicate item || anyTrue items predicate

private theorem anyTrue_sound
    {alpha : Type} {items : List alpha}
    {predicate : alpha → Bool}
    (checked : anyTrue items predicate = true) :
    ∃ item, item ∈ items ∧ predicate item = true := by
  induction items with
  | nil =>
      simp [anyTrue] at checked
  | cons head tail ih =>
      cases headChecked : predicate head with
      | false =>
          have tailChecked : anyTrue tail predicate = true := by
            simpa [anyTrue, headChecked] using checked
          obtain ⟨item, member, itemChecked⟩ := ih tailChecked
          exact ⟨item, List.Mem.tail head member, itemChecked⟩
      | true =>
          exact ⟨head, List.Mem.head tail, headChecked⟩

private theorem anyTrue_complete
    {alpha : Type} {items : List alpha}
    {predicate : alpha → Bool} {item : alpha}
    (member : item ∈ items) (checked : predicate item = true) :
    anyTrue items predicate = true := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      cases member with
      | head =>
          simp [anyTrue, checked]
      | tail _ tailMember =>
          cases headChecked : predicate head with
          | false =>
              simpa [anyTrue, headChecked] using
                ih tailMember
          | true =>
              simp [anyTrue, headChecked]

private def circuitSatisfiableBool
    {inputs : Nat} (circuit : Circuit inputs) : Bool :=
  anyTrue (allBoolTuples inputs) fun input =>
    circuit.program.eval input.toValuation circuit.outputGate

private theorem circuitSatisfiableBool_eq_true_iff
    {inputs : Nat} (circuit : Circuit inputs) :
    circuitSatisfiableBool circuit = true ↔
      circuit.Satisfiable := by
  constructor
  · intro checked
    obtain ⟨input, _member, outputTrue⟩ :=
      anyTrue_sound checked
    exact ⟨input.toValuation, outputTrue⟩
  · rintro ⟨input, outputTrue⟩
    let tuple := BoolTuple.ofFn input
    have tupleOutputTrue :
        circuit.program.eval tuple.toValuation
            circuit.outputGate =
          true := by
      exact
        (circuit.program.eval_input_congr
          (fun index =>
            BoolTuple.toValuation_ofFn input index)
          circuit.outputGate).trans outputTrue
    exact anyTrue_complete (mem_allBoolTuples tuple)
      tupleOutputTrue

/-- Constructive finite decidability of source-circuit satisfiability.  This
is exhaustive finite search and carries no polynomial-runtime claim. -/
private def circuitSatisfiableDecidable
    {inputs : Nat} (circuit : Circuit inputs) :
    Decidable circuit.Satisfiable :=
  if checked : circuitSatisfiableBool circuit = true then
    isTrue ((circuitSatisfiableBool_eq_true_iff circuit).1 checked)
  else
    isFalse (fun isSatisfiable =>
      checked
        ((circuitSatisfiableBool_eq_true_iff circuit).2
          isSatisfiable))

/-- The typed semantic threshold: a source circuit is satisfiable exactly
when the exhaustive minimum of its answer-independent full candidate exceeds
the source-derived baseline. -/
theorem fullCandidate_satisfiable_iff_referenceMinimum_ge_succ
    {inputs : Nat} (circuit : Circuit inputs) :
    circuit.Satisfiable ↔
      lockedBaselineCount circuit.program + 1 ≤
        referenceMinimum
          (Implementation.mk
            (lockedBaselineCount circuit.program + 4)
            (fullCandidate circuit)) := by
  letI : Decidable circuit.Satisfiable :=
    circuitSatisfiableDecidable circuit
  exact
    ConditionalThresholdBoundaryPremises.satisfiable_iff_minimum_ge_succ
      (fullCandidateThresholdPremises circuit)

end LockedNANDGlobalCandidates
end DirectWire
end PNP
