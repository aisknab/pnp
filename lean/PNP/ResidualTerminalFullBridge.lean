/-
Copyright (c) 2026 PNP Labs.

The full-mode terminal bridge for whole direct-wire implementations.  A
terminal full realization carries the complete multi-output semantics of the
whole implementation together with its actual gate count.  The independently
stated terminal-minimum specification is characterized by the exhaustive
reference minimum, and every cheaper whole-span realization gives a genuine
strict equivalent gain.

This is the direct-wire specialization of the pinned manuscript's terminal
RW-MuBridge and whole-span policy.  It does not model quotient carriers,
proper supports, saturation, BCELReady, PCCOracle, ZeroSlack, or a polynomial
route for finding the reference-minimum witness.
-/

import PNP.ResidualGainStopping

namespace PNP
namespace DirectWire

/-- A closed full-mode realization of the complete semantics of `current`.
    Unlike a projected or sampled comparison, the equivalence field covers
    every input and every output coordinate. -/
structure TerminalFullRealization {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  implementation : Implementation inputs outputs
  equivalent :
    Equivalent implementation.candidate.program
      implementation.candidate.directWireWord
      current.candidate.program current.candidate.directWireWord

/-- Regard the supplied whole implementation as its own terminal full
    realization.  No gate is inserted or removed. -/
def terminalize {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    TerminalFullRealization current :=
  { implementation := current
    equivalent :=
      Equivalent.refl current.candidate.program
        current.candidate.directWireWord }

@[simp] theorem terminalize_implementation {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (terminalize current).implementation = current := rfl

/-- Terminalization preserves the whole implementation's exact gate count. -/
theorem terminalize_gateCount {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    (terminalize current).implementation.gateCount = current.gateCount := rfl

/-- Forget the terminal wrapper and recover the represented whole
    implementation. -/
def TerminalFullRealization.realize {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    (realization : TerminalFullRealization current) :
    Implementation inputs outputs :=
  realization.implementation

@[simp] theorem TerminalFullRealization.realize_gateCount
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (realization : TerminalFullRealization current) :
    realization.realize.gateCount = realization.implementation.gateCount := rfl

/-- Realizing a terminal full word preserves the complete multi-output
    semantics recorded by the bridge. -/
theorem TerminalFullRealization.realize_equivalent
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (realization : TerminalFullRealization current) :
    Equivalent realization.realize.candidate.program
      realization.realize.candidate.directWireWord
      current.candidate.program current.candidate.directWireWord :=
  realization.equivalent

/-- Pointwise form of complete terminal realization semantics. -/
theorem TerminalFullRealization.realize_semantics
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (realization : TerminalFullRealization current)
    (input : Valuation inputs) (output : Fin outputs) :
    realization.realize.candidate.semantics input output =
      current.candidate.semantics input output :=
  realization.equivalent input output

/-- A number is a terminal full minimum when it is attained by a complete
    realization and lower-bounds every complete realization.  This definition
    is independent of `referenceMinimum`. -/
def IsTerminalFullMinimum {inputs outputs : Nat}
    (current : Implementation inputs outputs) (gateCount : Nat) : Prop :=
  (∃ realization : TerminalFullRealization current,
      realization.implementation.gateCount = gateCount) ∧
    ∀ realization : TerminalFullRealization current,
      gateCount ≤ realization.implementation.gateCount

/-- The exhaustive reference implementation, reified as a terminal full
    realization. -/
def referenceMinimumTerminalFullRealization {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    TerminalFullRealization current :=
  { implementation := referenceMinimumImplementation current
    equivalent := referenceMinimumImplementation_equivalent current }

theorem referenceMinimumTerminalFullRealization_gateCount
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (referenceMinimumTerminalFullRealization current).implementation.gateCount =
      referenceMinimum current :=
  referenceMinimumImplementation_gateCount_eq_referenceMinimum current

/-- The terminal full minimum is read from the concrete reference realization;
    its universal specification is proved separately below. -/
def terminalFullMinimum {inputs outputs : Nat}
    (current : Implementation inputs outputs) : Nat :=
  (referenceMinimumTerminalFullRealization current).implementation.gateCount

/-- Direct-wire terminal MuBridge: the terminal full minimum and the whole
    implementation's exhaustive semantic minimum are the same integer. -/
theorem terminalFullMinimum_eq_referenceMinimum
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    terminalFullMinimum current = referenceMinimum current :=
  referenceMinimumTerminalFullRealization_gateCount current

/-- The terminal full minimum is attained and is a lower bound against every
    complete terminal realization. -/
theorem terminalFullMinimum_spec {inputs outputs : Nat}
    (current : Implementation inputs outputs) :
    IsTerminalFullMinimum current (terminalFullMinimum current) := by
  constructor
  · exact ⟨referenceMinimumTerminalFullRealization current, rfl⟩
  · intro realization
    rw [terminalFullMinimum_eq_referenceMinimum]
    exact referenceMinimum_le_of_equivalent current
      realization.implementation.candidate realization.equivalent

/-- The independently stated terminal-minimum specification has exactly one
    value. -/
theorem isTerminalFullMinimum_iff_eq_terminalFullMinimum
    {inputs outputs gateCount : Nat}
    (current : Implementation inputs outputs) :
    IsTerminalFullMinimum current gateCount ↔
      gateCount = terminalFullMinimum current := by
  constructor
  · intro minimum
    obtain ⟨realization, realizationSize⟩ := minimum.1
    apply Nat.le_antisymm
    · exact minimum.2 (referenceMinimumTerminalFullRealization current)
    · have lowerBound := (terminalFullMinimum_spec current).2 realization
      rw [realizationSize] at lowerBound
      exact lowerBound
  · intro equal
    rw [equal]
    exact terminalFullMinimum_spec current

/-- Equivalent report-facing characterization using the whole-circuit
    reference minimum. -/
theorem isTerminalFullMinimum_iff_eq_referenceMinimum
    {inputs outputs gateCount : Nat}
    (current : Implementation inputs outputs) :
    IsTerminalFullMinimum current gateCount ↔
      gateCount = referenceMinimum current := by
  constructor
  · intro minimum
    exact
      ((isTerminalFullMinimum_iff_eq_terminalFullMinimum current).mp minimum).trans
        (terminalFullMinimum_eq_referenceMinimum current)
  · intro equal
    exact
      (isTerminalFullMinimum_iff_eq_terminalFullMinimum current).mpr
        (equal.trans (terminalFullMinimum_eq_referenceMinimum current).symm)

/-- A whole-span residual witness is a complete terminal realization that is
    strictly cheaper than the supplied implementation. -/
structure WholeSpanResidualWitness {inputs outputs : Nat}
    (current : Implementation inputs outputs) where
  realization : TerminalFullRealization current
  cheaper : realization.implementation.gateCount < current.gateCount

/-- Positive residual slack supplies the reference-minimum whole-span witness.
    This existence proof is semantic and exhaustive, not a polynomial route. -/
def referenceMinimumWholeSpanWitnessOfPositive
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (positive : 0 < residualSlack current) :
    WholeSpanResidualWitness current :=
  { realization := referenceMinimumTerminalFullRealization current
    cheaper :=
      (referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos
        positive).smaller }

/-- Every whole-span witness is a genuine strict equivalent gain. -/
def WholeSpanResidualWitness.strictEquivalentGain
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (witness : WholeSpanResidualWitness current) :
    StrictEquivalentGain current witness.realization.implementation :=
  { smaller := witness.cheaper
    equivalent := witness.realization.equivalent }

/-- The whole-span policy routes every cheaper full realization to strict
    descent in the same residual measure used by the gain chain. -/
theorem WholeSpanResidualWitness.strictResidualDescent
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (witness : WholeSpanResidualWitness current) :
    residualSlack witness.realization.implementation < residualSlack current :=
  witness.strictEquivalentGain.strictResidualDescent

/-- Positive residual slack is exactly the existence of a complete cheaper
    whole-span realization. -/
theorem residualSlack_pos_iff_exists_wholeSpanResidualWitness
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    0 < residualSlack current ↔ Nonempty (WholeSpanResidualWitness current) := by
  constructor
  · intro positive
    exact ⟨referenceMinimumWholeSpanWitnessOfPositive positive⟩
  · rintro ⟨witness⟩
    exact (residualSlack_pos_iff_exists_strictEquivalentGain current).mpr
      ⟨witness.realization.implementation, witness.strictEquivalentGain⟩

/-- Zero residual slack is exactly the absence of any complete cheaper
    whole-span realization. -/
theorem residualSlack_eq_zero_iff_no_wholeSpanResidualWitness
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    residualSlack current = 0 ↔
      ¬Nonempty (WholeSpanResidualWitness current) := by
  constructor
  · intro slackZero witness
    have positive :=
      (residualSlack_pos_iff_exists_wholeSpanResidualWitness current).mpr witness
    rw [slackZero] at positive
    exact Nat.not_lt_zero 0 positive
  · intro noWitness
    apply Nat.eq_zero_of_not_pos
    intro positive
    exact noWitness
      ((residualSlack_pos_iff_exists_wholeSpanResidualWitness current).mp positive)

end DirectWire
end PNP
