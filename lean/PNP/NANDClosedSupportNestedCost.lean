import PNP.NANDClosedSupportNestedProfile

/-!
Computed full and quotient reference minima grow by at most the physical
difference between nested closed supports. The comparisons are constructed
from the actual minima, not supplied by callers. Reference search remains
exhaustive; no polynomial bound or global saturation theorem is asserted.
-/

namespace PNP.DirectWire.ClosedSupportNestedGain

variable {inputs outputs fields : Nat}

theorem full_minimum_extension_bound (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep large).fullMinimum ≤
      (snapshot target keep small).fullMinimum + (difference target keep small large).gateCount := by
  let full := terminalFullProfileMinimumRealization
    (WireProfileAmbient.model target keep).ambientProfileSystem
    (ClosedSupportObservation.implementation target keep small)
  have lower := terminalFullProfileMinimum_le
    (extendFullComparison target keep small large included full)
  change (snapshot target keep large).fullMinimum ≤
    full.realization.implementation.gateCount + (difference target keep small large).gateCount at lower
  have count : full.realization.implementation.gateCount =
      (snapshot target keep small).fullMinimum :=
    terminalFullProfileMinimumRealization_gateCount _ _
  rw [count] at lower
  exact lower

theorem quotient_minimum_extension_bound (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep large).quotientMinimum ≤
      (snapshot target keep small).quotientMinimum + (difference target keep small large).gateCount := by
  let comparison := terminalQuotientProfileMinimumComparison
    (WireProfileAmbient.model target keep).ambientProfileSystem
    (WireProfileAmbient.model target keep).projection
    (ClosedSupportObservation.implementation target keep small)
  have lower := terminalQuotientProfileMinimum_le
    (extendQuotientComparison target keep small large included comparison)
  change (snapshot target keep large).quotientMinimum ≤
    comparison.realization.implementation.gateCount +
      (difference target keep small large).gateCount at lower
  have count : comparison.realization.implementation.gateCount =
      (snapshot target keep small).quotientMinimum :=
    terminalQuotientProfileMinimumComparison_gateCount _ _ _
  rw [count] at lower
  exact lower

theorem full_minimum_cost_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep large).fullMinimum + (snapshot target keep small).supportSize ≤
      (snapshot target keep small).fullMinimum + (snapshot target keep large).supportSize := by
  have bound := full_minimum_extension_bound target keep small large included
  have partition := support_count_decomposition target keep small large included
  omega

theorem quotient_minimum_cost_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep large).quotientMinimum + (snapshot target keep small).supportSize ≤
      (snapshot target keep small).quotientMinimum + (snapshot target keep large).supportSize := by
  have bound := quotient_minimum_extension_bound target keep small large included
  have partition := support_count_decomposition target keep small large included
  omega

theorem full_slack_le (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep small).fullSlack ≤ (snapshot target keep large).fullSlack := by
  have balance := full_minimum_cost_balance target keep small large included
  change (snapshot target keep small).supportSize - (snapshot target keep small).fullMinimum ≤
    (snapshot target keep large).supportSize - (snapshot target keep large).fullMinimum
  omega

theorem quotient_slack_le (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large) :
    (snapshot target keep small).supportSize - (snapshot target keep small).quotientMinimum ≤
      (snapshot target keep large).supportSize - (snapshot target keep large).quotientMinimum := by
  have balance := quotient_minimum_cost_balance target keep small large included
  omega

theorem full_minimum_le_support (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (seed : Seed target) :
    (snapshot target keep seed).fullMinimum ≤ (snapshot target keep seed).supportSize := by
  let self : TerminalFullCarrierRealization
      (WireProfileAmbient.model target keep).ambientProfileSystem
      (ClosedSupportObservation.implementation target keep seed) :=
    { realization := terminalize (ClosedSupportObservation.implementation target keep seed)
      profileEqual := fun _ => rfl }
  exact terminalFullProfileMinimum_le self

theorem quotient_minimum_le_full (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (seed : Seed target) :
    (snapshot target keep seed).quotientMinimum ≤ (snapshot target keep seed).fullMinimum := by
  let full := terminalFullProfileMinimumRealization
    (WireProfileAmbient.model target keep).ambientProfileSystem
    (ClosedSupportObservation.implementation target keep seed)
  let comparison : TerminalQuotientComparison
      (WireProfileAmbient.model target keep).ambientProfileSystem
      (WireProfileAmbient.model target keep).projection
      (ClosedSupportObservation.implementation target keep seed) :=
    { realization := full.realization
      keptProfileEqual := fun field _ => full.profileEqual field }
  exact terminalQuotientProfileMinimum_le comparison

theorem slack_decomposition (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (seed : Seed target) :
    (snapshot target keep seed).fullSlack + (snapshot target keep seed).projectionDefect =
      (snapshot target keep seed).supportSize - (snapshot target keep seed).quotientMinimum := by
  have fullBound := full_minimum_le_support target keep seed
  have quotientBound := quotient_minimum_le_full target keep seed
  change ((snapshot target keep seed).supportSize - (snapshot target keep seed).fullMinimum) +
      ((snapshot target keep seed).fullMinimum - (snapshot target keep seed).quotientMinimum) =
    (snapshot target keep seed).supportSize - (snapshot target keep seed).quotientMinimum
  omega

theorem positive_iff_quotient_slack (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (seed : Seed target) :
    (0 < (snapshot target keep seed).fullSlack ∨
      0 < (snapshot target keep seed).projectionDefect) ↔
        0 < (snapshot target keep seed).supportSize - (snapshot target keep seed).quotientMinimum := by
  have sum := slack_decomposition target keep seed
  constructor
  · intro positive
    rcases positive with fullPositive | defectPositive
    · omega
    · omega
  · intro positive
    by_cases fullPositive : 0 < (snapshot target keep seed).fullSlack
    · exact Or.inl fullPositive
    · apply Or.inr
      omega

theorem positive_mono (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (included : Included target keep small large)
    (positive : 0 < (snapshot target keep small).fullSlack ∨
      0 < (snapshot target keep small).projectionDefect) :
    0 < (snapshot target keep large).fullSlack ∨
      0 < (snapshot target keep large).projectionDefect := by
  apply (positive_iff_quotient_slack target keep large).mpr
  exact Nat.lt_of_lt_of_le ((positive_iff_quotient_slack target keep small).mp positive)
    (quotient_slack_le target keep small large included)

end PNP.DirectWire.ClosedSupportNestedGain
