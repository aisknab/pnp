/-
Copyright (c) 2026 PNP Labs.

Finite chains of independently verified strict equivalent NAND gains.  This
module proves the residual-slack iteration bound used by the PCCMin argument,
but it neither generates a gain nor turns search failure into global
minimality.  The executable checker inherits the exact finite truth-table
comparison from `ResidualRoutes`; no polynomial-runtime claim is made here.
-/

import PNP.ResidualRoutes

namespace PNP
namespace DirectWire

/-- Every implementation in `chain` is a strict equivalent gain over the
    implementation immediately before it. -/
def StrictGainChain {inputs outputs : Nat} :
    Implementation inputs outputs →
      List (Implementation inputs outputs) → Prop
  | _current, [] => True
  | current, next :: remaining =>
      StrictEquivalentGain current next ∧ StrictGainChain next remaining

/-- Executably validate every adjacent gain in a finite implementation chain. -/
def strictGainChainBool {inputs outputs : Nat} :
    Implementation inputs outputs →
      List (Implementation inputs outputs) → Bool
  | _current, [] => true
  | current, next :: remaining =>
      strictEquivalentGainBool current next &&
        strictGainChainBool next remaining

/-- The implementation reached after applying every entry in a gain chain. -/
def gainChainEnd {inputs outputs : Nat} :
    Implementation inputs outputs →
      List (Implementation inputs outputs) → Implementation inputs outputs
  | current, [] => current
  | _current, next :: remaining => gainChainEnd next remaining

/-- The Boolean chain checker recognizes exactly proof-bearing strict gain
    chains. -/
theorem strictGainChainBool_eq_true_iff {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (chain : List (Implementation inputs outputs)) :
    strictGainChainBool current chain = true ↔
      StrictGainChain current chain := by
  induction chain generalizing current with
  | nil =>
      constructor
      · intro _checked
        exact True.intro
      · intro _valid
        rfl
  | cons next remaining ih =>
      constructor
      · intro checked
        change
          (strictEquivalentGainBool current next &&
            strictGainChainBool next remaining) = true at checked
        cases firstCheck : strictEquivalentGainBool current next with
        | false =>
            rw [firstCheck] at checked
            exact False.elim (Bool.noConfusion checked)
        | true =>
            rw [firstCheck] at checked
            exact
              ⟨strictEquivalentGainBool_sound firstCheck,
                (ih next).mp checked⟩
      · intro valid
        change
          (strictEquivalentGainBool current next &&
            strictGainChainBool next remaining) = true
        rw [strictEquivalentGainBool_complete valid.1,
          (ih next).mpr valid.2]
        rfl

/-- A valid gain chain preserves the complete multi-output Boolean semantics
    of its starting implementation. -/
theorem StrictGainChain.end_equivalent {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (valid : StrictGainChain current chain) :
    Equivalent
      (gainChainEnd current chain).candidate.program
      (gainChainEnd current chain).candidate.directWireWord
      current.candidate.program current.candidate.directWireWord := by
  induction chain generalizing current with
  | nil =>
      exact Equivalent.refl current.candidate.program
        current.candidate.directWireWord
  | cons next remaining ih =>
      exact Equivalent.trans (ih valid.2) valid.1.equivalent

/-- The exhaustive semantic reference minimum is invariant across an entire
    valid gain chain. -/
theorem StrictGainChain.end_referenceMinimum_eq {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (valid : StrictGainChain current chain) :
    referenceMinimum (gainChainEnd current chain) = referenceMinimum current :=
  referenceMinimum_invariant (gainChainEnd current chain) current
    valid.end_equivalent

/-- Exact aggregate descent inequality: the final residual slack plus the
    number of verified gains never exceeds the initial residual slack. -/
theorem StrictGainChain.end_residualSlack_add_length_le
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (valid : StrictGainChain current chain) :
    residualSlack (gainChainEnd current chain) + chain.length ≤
      residualSlack current := by
  induction chain generalizing current with
  | nil => exact Nat.le_refl (residualSlack current)
  | cons next remaining ih =>
      calc
        residualSlack (gainChainEnd next remaining) +
            (remaining.length + 1) =
            (residualSlack (gainChainEnd next remaining) +
              remaining.length) + 1 :=
          (Nat.add_assoc
            (residualSlack (gainChainEnd next remaining))
            remaining.length 1).symm
        _ ≤ residualSlack next + 1 :=
          Nat.add_le_add_right (ih valid.2) 1
        _ ≤ residualSlack current :=
          Nat.succ_le_of_lt valid.1.strictResidualDescent

/-- The number of verified gains is bounded by the initial residual slack. -/
theorem StrictGainChain.length_le_residualSlack {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (valid : StrictGainChain current chain) :
    chain.length ≤ residualSlack current :=
  Nat.le_trans
    (Nat.le_add_left chain.length
      (residualSlack (gainChainEnd current chain)))
    valid.end_residualSlack_add_length_le

/-- Executable chain acceptance implies the same residual-slack iteration
    bound. -/
theorem strictGainChainBool_length_le_residualSlack
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (checked : strictGainChainBool current chain = true) :
    chain.length ≤ residualSlack current :=
  ((strictGainChainBool_eq_true_iff current chain).mp checked).length_le_residualSlack

/-- Any disclosed starting slack bound transports directly to the number of
    accepted gain steps. -/
theorem strictGainChainBool_length_le_of_residualSlack_le
    {inputs outputs bound : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (checked : strictGainChainBool current chain = true)
    (slackBound : residualSlack current ≤ bound) :
    chain.length ≤ bound :=
  Nat.le_trans (strictGainChainBool_length_le_residualSlack checked) slackBound

/-- A semantically minimum starting implementation admits no nonempty strict
    gain chain. -/
theorem StrictGainChain.eq_nil_of_residualSlack_eq_zero
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (valid : StrictGainChain current chain)
    (slackZero : residualSlack current = 0) :
    chain = [] := by
  apply List.eq_nil_of_length_eq_zero
  apply Nat.eq_zero_of_le_zero
  rw [← slackZero]
  exact valid.length_le_residualSlack

/-- The executable form also cannot accept a nonempty chain from zero slack. -/
theorem strictGainChainBool_eq_nil_of_residualSlack_eq_zero
    {inputs outputs : Nat}
    {current : Implementation inputs outputs}
    {chain : List (Implementation inputs outputs)}
    (checked : strictGainChainBool current chain = true)
    (slackZero : residualSlack current = 0) :
    chain = [] := by
  have valid : StrictGainChain current chain :=
    (strictGainChainBool_eq_true_iff current chain).mp checked
  exact valid.eq_nil_of_residualSlack_eq_zero slackZero

end DirectWire
end PNP
