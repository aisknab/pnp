# BN3 joint-realizability gap

Status: **missing obligation; milestone not earned**

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

This is not a counterexample to a future circuit-specific BN3 theorem.  It is
a countermodel to the inference from per-cut existence alone.  A valid repair
must add and prove the missing candidate-derived coherence lemma.

## Required repair

An earning proof for `global-zeroslack-pccmin` must provide, without a caller
certificate, assertion Boolean, exact-minimization oracle, or finite-instance
list:

1. one canonical request-atom identity space derived from every encoded
   residual candidate;
2. stable monotone request predicates across all proper cuts and transports;
3. a jointly side-tight realization theorem connecting those identities to
   the existing BN2 carrier bases;
4. exact, duplicate-free incidence accounting for every cut;
5. a concrete polynomial enumeration and runtime bound in the repository's
   finite-machine complexity model.

Only then can BN4–BN6, selector completeness, Realizer/HB closure, global
ZeroSlack, and polynomial PCCMin consume the result.  Until that repair exists,
`PNP.Main.zero_slack_complete` and `PNP.Main.pccmin_polynomial_exact` must
remain absent and the publication milestone must remain unearned.
