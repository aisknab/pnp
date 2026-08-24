import PNP.PCCMinRankOrderedOracle

namespace PNP
namespace DirectWire

/-- Identity normalizer fixture used only to exercise oracle composition. -/
def pccMinRankOrderedIdentityFixtureNormalizer : PCCMinTotalNormalizer where
  normalize := fun current =>
    .normal
      { result := current
        equivalent := Equivalent.refl
          current.candidate.program current.candidate.directWireWord
        gateCount_le := Nat.le_refl current.gateCount }

/-- HResolve exact fixture.  Later stages are uninhabited and therefore cannot
be evaluated. -/
def pccMinHResolveExactFixturePlan {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (exact : ExactMinimumResult current) :
    PCCMinRankOrderedOraclePlan current where
  NoHereditary := Empty
  NoBudget := Empty
  hResolve := .exact exact
  budgetResolve := fun impossible => nomatch impossible
  selectorPlan := fun impossible => nomatch impossible

/-- HResolve gain fixture. -/
def pccMinHResolveGainFixturePlan {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next) :
    PCCMinRankOrderedOraclePlan current where
  NoHereditary := Empty
  NoBudget := Empty
  hResolve := .gain next gain
  budgetResolve := fun impossible => nomatch impossible
  selectorPlan := fun impossible => nomatch impossible

/-- BudgetResolve exact fixture reached through an actual NoHereditary value. -/
def pccMinBudgetResolveExactFixturePlan {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (exact : ExactMinimumResult current) :
    PCCMinRankOrderedOraclePlan current where
  NoHereditary := Unit
  NoBudget := Empty
  hResolve := .noRoute ()
  budgetResolve := fun _ => .exact exact
  selectorPlan := fun _ impossible => nomatch impossible

/-- BudgetResolve gain fixture reached through an actual NoHereditary value. -/
def pccMinBudgetResolveGainFixturePlan {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next) :
    PCCMinRankOrderedOraclePlan current where
  NoHereditary := Unit
  NoBudget := Empty
  hResolve := .noRoute ()
  budgetResolve := fun _ => .gain next gain
  selectorPlan := fun _ impossible => nomatch impossible

/-- Two nonempty rank rows whose first realizer produces a gain. -/
def pccMinEarlyRankGainFixtureSelectorPlan {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next)
    (zeroSlack : ZeroSlackResult current) :
    PCCMinRankedSelectorPlan current where
  rankCount := 2
  Selector := Unit
  Bot := Unit
  selectorsAt := fun _ => [()]
  realize := fun _ _ => .gain next gain
  zeroSlackOfSilence := fun _ => zeroSlack

/-- Two nonempty rank rows whose first row is blocked and whose second row
produces a gain. -/
def pccMinLaterRankGainFixtureSelectorPlan {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next)
    (zeroSlack : ZeroSlackResult current) :
    PCCMinRankedSelectorPlan current where
  rankCount := 2
  Selector := Unit
  Bot := Unit
  selectorsAt := fun _ => [()]
  realize := fun rank _ =>
    if rank.val = 0 then .blocked () else .gain next gain
  zeroSlackOfSilence := fun _ => zeroSlack

/-- Two complete silent rows. -/
def pccMinSilentFixtureSelectorPlan {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (zeroSlack : ZeroSlackResult current) :
    PCCMinRankedSelectorPlan current where
  rankCount := 2
  Selector := Unit
  Bot := Unit
  selectorsAt := fun _ => [()]
  realize := fun _ _ => .blocked ()
  zeroSlackOfSilence := fun _ => zeroSlack

/-- Wrap one supplied selector plan behind proof-bearing negative resolver
outcomes. -/
def pccMinSelectorFixtureOraclePlan {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (selectors : PCCMinRankedSelectorPlan current) :
    PCCMinRankOrderedOraclePlan current where
  NoHereditary := Unit
  NoBudget := Unit
  hResolve := .noRoute ()
  budgetResolve := fun _ => .noRoute ()
  selectorPlan := fun _ _ => selectors

/-- Exhaustive reference fixture used only to exercise a total builder.  Its
reference-minimum operation is not a polynomial PCCOracle construction. -/
def pccMinRankOrderedReferenceFixtureBuilder :
    PCCMinRankOrderedOracleBuilder where
  build := fun current =>
    if positive : 0 < residualSlack current then
      { NoHereditary := Empty
        NoBudget := Empty
        hResolve := .gain (referenceMinimumImplementation current)
          (referenceMinimumImplementation_strictEquivalentGain_of_residualSlack_pos
            positive)
        budgetResolve := fun impossible => nomatch impossible
        selectorPlan := fun impossible => nomatch impossible }
    else
      { NoHereditary := Unit
        NoBudget := Unit
        hResolve := .noRoute ()
        budgetResolve := fun _ => .noRoute ()
        selectorPlan := fun _ _ =>
          { rankCount := 0
            Selector := Unit
            Bot := Unit
            selectorsAt := fun rank => nomatch rank
            realize := fun rank => nomatch rank
            zeroSlackOfSilence := fun _ =>
              { minimum :=
                  (residualSlack_eq_zero_iff_minimum current).mp
                    (Nat.eq_zero_of_not_pos positive) } } }

example {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (exact : ExactMinimumResult current) :
    (pccMinHResolveExactFixturePlan current exact).route = .exact exact := by
  rfl

example {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next) :
    (pccMinHResolveGainFixturePlan current next gain).route =
      .gain next gain := by
  rfl

example {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (exact : ExactMinimumResult current) :
    (pccMinBudgetResolveExactFixturePlan current exact).route = .exact exact := by
  rfl

example {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next) :
    (pccMinBudgetResolveGainFixturePlan current next gain).route =
      .gain next gain := by
  rfl

example {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next)
    (zeroSlack : ZeroSlackResult current) :
    (pccMinSelectorFixtureOraclePlan current
      (pccMinEarlyRankGainFixtureSelectorPlan current next gain zeroSlack)).route =
        .gain next gain := by
  rfl

example {inputs outputs : Nat}
    (current next : Implementation inputs outputs)
    (gain : StrictEquivalentGain current next)
    (zeroSlack : ZeroSlackResult current) :
    (pccMinSelectorFixtureOraclePlan current
      (pccMinLaterRankGainFixtureSelectorPlan current next gain zeroSlack)).route =
        .gain next gain := by
  rfl

example {inputs outputs : Nat}
    (current : Implementation inputs outputs)
    (zeroSlack : ZeroSlackResult current) :
    (pccMinSelectorFixtureOraclePlan current
      (pccMinSilentFixtureSelectorPlan current zeroSlack)).route =
        .zeroSlack zeroSlack := by
  rfl

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    let execution := runPCCMinNormalizeRankOrderedOracleLoop
      pccMinRankOrderedIdentityFixtureNormalizer
      pccMinRankOrderedReferenceFixtureBuilder current
    Equivalent
        execution.result.candidate.program
        execution.result.candidate.directWireWord
        current.candidate.program current.candidate.directWireWord ∧
      IsSemanticallyMinimum execution.result ∧
      execution.result.gateCount = referenceMinimum current ∧
      residualSlack execution.result = 0 ∧
      execution.gainIterations <= residualSlack current :=
  pccmin_normalize_rank_ordered_oracle_loop_checked_complete
    pccMinRankOrderedIdentityFixtureNormalizer
    pccMinRankOrderedReferenceFixtureBuilder current

end DirectWire
end PNP
