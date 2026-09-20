import PNP.NANDClosedSupportNestedCost

/-!
Computed nested-support positivity for arbitrary wire carriers, keep masks
and finite record seeds. Seed inclusion derives the needed physical inclusion.

Legacy anchor: the positive-slack preservation dependency of RW-SaturatePositive
and transparentSaturationCostBalanced. This proves a comparison between already
completed dependency-closed supports. It does not prove that completing an
arbitrary raw support preserves its initial slack, that each intermediate
saturation event is transparent, or that nontransparent events have complete
routes. Full manuscript profile roles, global SaturatePositive, BCELReady,
ZeroSlack and polynomial PCCMin remain open.
-/

namespace PNP.DirectWire.ClosedSupportNestedGain

variable {inputs outputs fields : Nat}

theorem included_of_seed_subset (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (within : ∀ record, record ∈ small → record ∈ large) :
    Included target keep small large := by
  intro gate selected
  let system := terminalCandidateSaturationSystem target.implementation.candidate
    (WireProfileAmbient.model target keep)
  have member : TerminalPrimitiveRecord.gate gate ∈ terminalSaturateRecords system small :=
    (terminalGateSelected_eq_true_iff
      (ClosedSupportObservation.records target keep small) gate).mp selected
  have generated := (mem_terminalSaturateRecords_iff system small (.gate gate)).mp member
  have larger := terminalSaturate_monotone system
    (fun record => record ∈ small) (fun record => record ∈ large)
    within (.gate gate) generated
  exact (terminalGateSelected_eq_true_iff
    (ClosedSupportObservation.records target keep large) gate).mpr
    ((mem_terminalSaturateRecords_iff system large (.gate gate)).mpr larger)

theorem seed_full_cost_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (within : ∀ record, record ∈ small → record ∈ large) :
    (snapshot target keep large).fullMinimum + (snapshot target keep small).supportSize ≤
      (snapshot target keep small).fullMinimum + (snapshot target keep large).supportSize :=
  full_minimum_cost_balance target keep small large
    (included_of_seed_subset target keep small large within)

theorem seed_quotient_cost_balance (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (within : ∀ record, record ∈ small → record ∈ large) :
    (snapshot target keep large).quotientMinimum + (snapshot target keep small).supportSize ≤
      (snapshot target keep small).quotientMinimum + (snapshot target keep large).supportSize :=
  quotient_minimum_cost_balance target keep small large
    (included_of_seed_subset target keep small large within)

theorem seed_full_slack_le (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (within : ∀ record, record ∈ small → record ∈ large) :
    (snapshot target keep small).fullSlack ≤ (snapshot target keep large).fullSlack :=
  full_slack_le target keep small large (included_of_seed_subset target keep small large within)

theorem seed_positive (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (small large : Seed target)
    (within : ∀ record, record ∈ small → record ∈ large)
    (positive : 0 < (snapshot target keep small).fullSlack ∨
      0 < (snapshot target keep small).projectionDefect) :
    0 < (snapshot target keep large).fullSlack ∨
      0 < (snapshot target keep large).projectionDefect :=
  positive_mono target keep small large (included_of_seed_subset target keep small large within) positive

theorem append_positive (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) (seed extra : Seed target)
    (positive : 0 < (snapshot target keep seed).fullSlack ∨
      0 < (snapshot target keep seed).projectionDefect) :
    0 < (snapshot target keep (seed ++ extra)).fullSlack ∨
      0 < (snapshot target keep (seed ++ extra)).projectionDefect :=
  seed_positive target keep seed (seed ++ extra)
    (fun _ member => List.mem_append_left extra member) positive

end PNP.DirectWire.ClosedSupportNestedGain
