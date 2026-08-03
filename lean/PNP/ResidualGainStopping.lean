/-
Copyright (c) 2026 PNP Labs.

Semantic stopping criteria for strict equivalent-gain chains.  This module
reconstructs the whole-span stopping boundary used by the pinned manuscript:
positive reference residual slack is exactly the existence of some strictly
smaller equivalent implementation, while global absence of such an
implementation is exactly zero slack and semantic minimality.

The reference-minimum implementation is used only as a mathematical witness.
Nothing here enumerates a polynomial candidate family, implements PCCOracle or
ZeroSlack, turns a listed scan failure into global absence, or proves a runtime
bound for the exhaustive reference definitions.
-/

import PNP.ResidualGainChain

namespace PNP
namespace DirectWire

/-- The implementation selected by the exhaustive reference construction has
    exactly the reference-minimum gate count. -/
theorem referenceMinimumImplementation_gateCount_eq_referenceMinimum
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    (referenceMinimumImplementation current).gateCount =
      referenceMinimum current := by
  rfl

/-- The exhaustive reference implementation preserves the complete
    multi-output semantics of the supplied implementation. -/
theorem referenceMinimumImplementation_equivalent
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    Equivalent
      (referenceMinimumImplementation current).candidate.program
      (referenceMinimumImplementation current).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord := by
  exact equivalentBool_sound (referenceMinimumWitness_equivalent current)

/-- The exhaustive reference implementation is semantically minimum among all
    finite direct-wire implementations of the same interface. -/
theorem referenceMinimumImplementation_isSemanticallyMinimum
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    IsSemanticallyMinimum (referenceMinimumImplementation current) := by
  intro gateCount candidate equivalent
  rw [referenceMinimumImplementation_gateCount_eq_referenceMinimum]
  apply referenceMinimum_le_of_equivalent current candidate
  exact Equivalent.trans equivalent
    (referenceMinimumImplementation_equivalent current)

/-- The exhaustive reference implementation itself has zero residual slack. -/
theorem referenceMinimumImplementation_residualSlack_eq_zero
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    residualSlack (referenceMinimumImplementation current) = 0 :=
  (residualSlack_eq_zero_iff_minimum
    (referenceMinimumImplementation current)).mpr
      (referenceMinimumImplementation_isSemanticallyMinimum current)

/-- Positive residual slack supplies a whole-span strict equivalent gain.  The
    witness is the semantic reference minimum, not a polynomial route. -/
theorem referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos
    {inputs outputs : Nat} {current : Implementation inputs outputs}
    (positive : 0 < residualSlack current) :
    StrictEquivalentGain current (referenceMinimumImplementation current) := by
  constructor
  · rw [referenceMinimumImplementation_gateCount_eq_referenceMinimum]
    apply Nat.lt_of_not_ge
    intro currentWithinMinimum
    have slackZero : residualSlack current = 0 := by
      unfold residualSlack
      exact natSub_eq_zero_of_le current.gateCount
        (referenceMinimum current) currentWithinMinimum
    rw [slackZero] at positive
    exact Nat.not_lt_zero 0 positive
  · exact referenceMinimumImplementation_equivalent current

/-- A finite direct-wire implementation has positive residual slack exactly
    when some strictly smaller semantically equivalent implementation exists. -/
theorem residualSlack_pos_iff_exists_strictEquivalentGain
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    0 < residualSlack current ↔
      ∃ next : Implementation inputs outputs,
        StrictEquivalentGain current next := by
  constructor
  · intro positive
    exact
      ⟨referenceMinimumImplementation current,
        referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos
          positive⟩
  · rintro ⟨next, gain⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le (residualSlack next))
      gain.strictResidualDescent

/-- Zero residual slack is exactly global absence of a strict equivalent gain.
    The quantifier ranges over every finite direct-wire implementation, not a
    caller-supplied candidate list. -/
theorem residualSlack_eq_zero_iff_forall_not_strictEquivalentGain
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    residualSlack current = 0 ↔
      ∀ next : Implementation inputs outputs,
        ¬StrictEquivalentGain current next := by
  constructor
  · intro slackZero next gain
    have descent := gain.strictResidualDescent
    rw [slackZero] at descent
    exact Nat.not_lt_zero _ descent
  · intro noGain
    cases slackValue : residualSlack current with
    | zero => rfl
    | succ slack =>
        have positive : 0 < residualSlack current := by
          rw [slackValue]
          exact Nat.zero_lt_succ slack
        obtain ⟨next, gain⟩ :=
          (residualSlack_pos_iff_exists_strictEquivalentGain current).mp positive
        exact False.elim (noGain next gain)

/-- Semantic minimality is exactly global absence of a strict equivalent gain. -/
theorem isSemanticallyMinimum_iff_forall_not_strictEquivalentGain
    {inputs outputs : Nat} (current : Implementation inputs outputs) :
    IsSemanticallyMinimum current ↔
      ∀ next : Implementation inputs outputs,
        ¬StrictEquivalentGain current next := by
  constructor
  · intro minimum
    exact
      (residualSlack_eq_zero_iff_forall_not_strictEquivalentGain current).mp
        ((residualSlack_eq_zero_iff_minimum current).mpr minimum)
  · intro noGain
    exact
      (residualSlack_eq_zero_iff_minimum current).mp
        ((residualSlack_eq_zero_iff_forall_not_strictEquivalentGain current).mpr
          noGain)

/-- A verified chain endpoint has zero slack once global absence of any further
    strict equivalent gain is proved.  This theorem does not infer the premise
    from a finite scan. -/
theorem StrictGainChain.end_residualSlack_eq_zero_of_no_strictEquivalentGain
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (_valid : StrictGainChain current chain)
    (noGain : ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain (gainChainEnd current chain) next) :
    residualSlack (gainChainEnd current chain) = 0 :=
  (residualSlack_eq_zero_iff_forall_not_strictEquivalentGain
    (gainChainEnd current chain)).mpr noGain

/-- A verified globally maximal gain chain packages its endpoint as an exact
    minimum equivalent implementation of its starting point. -/
def StrictGainChain.end_exactMinimumResult_of_no_strictEquivalentGain
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (valid : StrictGainChain current chain)
    (noGain : ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain (gainChainEnd current chain) next) :
    ExactMinimumResult current :=
  { result := gainChainEnd current chain
    equivalent := valid.end_equivalent
    minimum :=
      (isSemanticallyMinimum_iff_forall_not_strictEquivalentGain
        (gainChainEnd current chain)).mpr noGain }

/-- Executable chain acceptance has the same semantic zero-slack stopping
    consequence once global no-gain evidence is separately proved. -/
theorem strictGainChainBool_end_residualSlack_eq_zero_of_no_strictEquivalentGain
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (checked : strictGainChainBool current chain = true)
    (noGain : ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain (gainChainEnd current chain) next) :
    residualSlack (gainChainEnd current chain) = 0 := by
  have valid : StrictGainChain current chain :=
    (strictGainChainBool_eq_true_iff current chain).mp checked
  exact valid.end_residualSlack_eq_zero_of_no_strictEquivalentGain noGain

/-- Executable chain acceptance packages a globally maximal endpoint as an
    exact minimum result.  The Boolean checker validates only the disclosed
    chain; the global no-gain premise remains a theorem obligation. -/
def strictGainChainBool_end_exactMinimumResult_of_no_strictEquivalentGain
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (checked : strictGainChainBool current chain = true)
    (noGain : ∀ next : Implementation inputs outputs,
      ¬StrictEquivalentGain (gainChainEnd current chain) next) :
    ExactMinimumResult current := by
  have valid : StrictGainChain current chain :=
    (strictGainChainBool_eq_true_iff current chain).mp checked
  exact valid.end_exactMinimumResult_of_no_strictEquivalentGain noGain

end DirectWire
end PNP
