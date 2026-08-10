# BN3 joint-realizability gap

Status: **finite candidate-derived repair earned; global milestone not earned**

This finding audits the pinned legacy report at tag
`final-pnp-proof-report-docs-hardened-7072f8d-sealed`, Section
“BN3: simultaneous finite request envelopes,” especially theorem
`BN3-SimultaneousEnvelope` and the fields `requestPredicatesStable` and
`jointSideTightRealizability`.

## Finding

The legacy prose uses side-tight BN2 bases to assert a stable request system
whose atom identities and activation predicates work across every proper cut.
The current Lean reconstruction proves local, cut-indexed side-tight basis
existence or a proof-bearing first local failure.  That premise alone does not
construct a cross-cut-stable selection of bases or request identities.

The historical checker does not close this edge.  In
`pcc-pack-sufficiency0.mjs` at the pinned tag, the generated package sets
`jointSideTightRealizability: true` and the checker tests that Boolean field.
It does not implement a request-envelope constructor or prove its semantics.
The repository's historical
`report-bindings/direct-bindings/BN3_DIRECT_BINDING_GAP_SEED.json` independently
classifies BN3 as a `uniformity-gap-surface`, sets
`fullHistoricalBN3TheoremDischarged` to `false`, and cites the
finite-to-unbounded gap.

## Kernel-checkable boundary witness

`lean-regression/PNPBN3JointRealizabilityGap.lean` gives a minimal logical
model with two cuts and two bases.  Each cut has a realizing basis, but the two
realizations are forced to differ, so no cross-cut-stable realizing family
exists.  Lean proves:

```text
PNP.DirectWire.BN3Gap.twoCut_perCutRealizable
PNP.DirectWire.BN3Gap.twoCut_noStableRealizingFamily
PNP.DirectWire.BN3Gap.perCutRealizable_not_uniformly_sufficient
```

This is not a counterexample to a circuit-specific BN3 theorem. It is a
countermodel to the inference from per-cut existence alone.

`PNP.ResidualTerminalBN3RequestEnvelope` now supplies a finite
candidate-derived repair after the computed BCEL anchor-nucleus classifier
succeeds. It derives one canonical request-atom list, exact monotone and stable
membership predicates, singleton minimal consumers, duplicate-free exact
incidence, and one canonical full/quotient side-tight basis family. The repair
does not use the historical assertion Boolean or a caller certificate.

## Remaining global repair

An earning proof for `global-zeroslack-pccmin` must still provide, without a
caller certificate, assertion Boolean, exact-minimization oracle, or
finite-instance list:

1. a route-complete construction reaching the successful finite nucleus for
   every encoded residual candidate or returning a globally consuming route;
2. BN4–BN6 and selector/realizer closure consuming the finite BN3 envelope;
3. a proof that the global route system strictly decreases the fixed RankWF;
4. a concrete polynomial enumeration and runtime bound in the repository's
   finite-machine complexity model, replacing the current all-subsets scan.

Only then can global ZeroSlack and polynomial PCCMin consume the finite result.
Until that repair exists,
`PNP.Main.zero_slack_complete` and `PNP.Main.pccmin_polynomial_exact` must
remain absent and the publication milestone must remain unearned.
