# Rank-ordered PCCOracle orchestration

M191 reconstructs the control-flow order in Section 16.1 of the pinned
manuscript. It replaces the single opaque-oracle input at the M190 boundary
with separated proof-bearing stages:

1. HResolve returns an exact minimum, a strict equivalent gain, or a typed
   NoHereditary value.
2. BudgetResolve is invoked only from that actual NoHereditary value and
   returns an exact minimum, a strict equivalent gain, or a typed NoBudget
   value.
3. Only after both negative resolver outcomes does the oracle scan arbitrary
   finite selector rows through the complete canonical `allFin` rank list.
4. Every selector returns either a checked strict gain or a typed blocker.
5. ZeroSlack is available only through an explicit closure that consumes a
   blocker equation for every selector in every rank row.

The central types are `PCCMinResolverOutcome`,
`PCCMinRankedRealizerOutcome`, `PCCMinRankedSelectorPlan`,
`PCCMinRankOrderedOraclePlan`, and `PCCMinRankOrderedOracleBuilder`.
`scanPCCMinSelectorRow` preserves exact row membership,
`scanPCCMinRankList` preserves exact rank membership, and
`scanPCCMinRankedSelectors` discharges rank completeness with `mem_allFin`.
There is no unresolved outcome at any stage.

`PCCMinRankOrderedOracleBuilder.toTotalOracle` converts those separated stages
into the M189 total-oracle interface.
`runPCCMinNormalizeRankOrderedOracleLoop` then reuses the M190 normalizer
composition. The public endpoint
`PNP.DirectWire.pccmin_normalize_rank_ordered_oracle_loop_checked_complete`
returns an implementation that:

- is semantically equivalent to the original implementation;
- is globally semantically minimum;
- has the exhaustive reference-minimum gate count;
- has zero residual slack; and
- is reached after no more strict-gain iterations than the starting residual
  slack.

## Exact claim boundary

This milestone does not construct the normalizer, HResolve, BudgetResolve,
rank rows, selector universe, realizer, typed blocker semantics, or ZeroSlack
closure. In particular, `zeroSlackOfSilence` is an explicit load-bearing
mathematical input; complete iteration control does not prove the implication
from silence to global minimality.

The regression's total builder uses exhaustive reference minimization only as
a semantic fixture. It is not a polynomial algorithm. M191 proves no
encoded-size bound, polynomial runtime, unconditional ZeroSlack, concrete
PCCMin implementation, SAT algorithm, or root theorem. It closes no fixed
risk-weighted checkpoint and no global gate.

## Verification

The focused checks are:

```text
lake build PNP.PCCMinRankOrderedOracle
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinRankOrderedOracleAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinRankOrderedOracle.lean
node --test audits/lean-pccmin-rank-ordered-oracle0.test.mjs
```

The regression covers HResolve exact and gain, BudgetResolve exact and gain,
a gain in the first rank, a gain after a blocked earlier rank, complete
selector silence, and composition with the recursive loop. The focused axiom
transcript contains no project-specific axiom, `sorryAx`, or
`Classical.choice`; the executable list scans use only Lean's standard
`propext` and `Quot.sound` foundations where their library membership proofs
require them.
