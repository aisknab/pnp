# M178 proof-bearing Budget ZeroSlack sidecar

## Evidence-led selection

The pinned manuscript's Sections 8.3 and 16 require the `NoBudget` result
consumed by `ZeroSlack` to be a strong BudgetResolve sidecar whose exact and
gain routes have semantic meaning.  The current reconstruction already has an
exhaustive terminal-derived budget-envelope resolver over the complete
canonical support-seed universe, but `ZeroSlack.BudgetSidecarCertificate`
still stores three uninterpreted strings.  This leaves an avoidable gap between
the checked resolver and the proposition consumed by the report-facing
certificate.

M178 replaces those strings with one proof-bearing checked boundary.  The
certificate carries an arbitrary finite direct-wire candidate, its
candidate-derived saturation model, supplied natural resource caps, and an
equation showing that the existing exhaustive search found no feasible
canonical support.  Exact and gain route soundness are derived from the
existing kernel theorems rather than accepted as handles or caller flags.

## Legacy anchor and dependency edge

- Legacy anchor: report Section 8.3, `BudgetResolve`, especially the exact,
  gain, and strong `NoBudget` outputs; report Section 16, where `ZeroSlack`
  consumes that sidecar.
- Closed edge: checked terminal budget-envelope resolution -> proof-bearing
  `BudgetSidecarCertificate` -> the structured `ZeroSlackCertificate`.
- Unbounded abstraction: arbitrary natural input, gate, output, and profile
  widths; every canonical terminal support seed for the supplied finite
  candidate; arbitrary supplied natural gate and saturated-record caps.

## Exact theorem target

For every `BudgetSidecarCertificate`, prove
`PNP.budget_zeroslack_sidecar_checked_complete`: the failed exhaustive search
excludes the computed budget predicate for every governed canonical support,
excludes every feasible support witness, and preserves the existing semantic
minimum and strict-equivalent-gain meanings for any explicit exact or gain
route.

The certificate must not carry a Boolean success flag, string proof handle,
caller-supplied candidate family, or caller-supplied exact/gain soundness
proof.  Its accepted negative proposition is recovered from
`findTerminalBudgetFeasibleSupport_eq_none_iff`.

## Claim boundary and downstream blockers

The budget caps remain supplied, and exhaustive support enumeration,
saturation, and reference minimization may be exponential.  M178 does not
formalize the manuscript's BUD grammar or B0--B4 sidecar semantics, derive a
polynomial envelope dynamic program, complete BudgetResolve or the complete
no-lower ledger, discharge H0--H4 blocker semantics, prove selector/HB/BCEL
composition at the `ZeroSlack` record, establish unconditional `ZeroSlack`,
prove PCCMin exactness or polynomial runtime, put SAT in P, remove a project
assumption, or prove `P = NP`.

## Required evidence

- root import and compiled theorem-inventory inclusion;
- an explicit axiom transcript for every new public declaration;
- a concrete zero-budget regression showing exhaustive no-support exclusion,
  plus independent exact and gain routes that retain their semantic meanings;
- hostile mutations for retained string handles, caller-supplied acceptance,
  supplied family/predicates, omitted search binding, hidden classical choice,
  assumptions, fixed dimensions, and claim widening;
- publication-map and formal-status rows with reviewed kernel fingerprints;
- current reconstruction, audit, pipeline, terminology, README, and canonical
  report documentation; and
- durable CI and aggregate-verifier coverage.

## Verification order and deduplication

Run lightweight source-shape checks before remote proof feedback.  On the
configured remote builder, compile the new dependency and root once, run its
axiom transcript and regression, reconcile generated publication evidence,
then run the complete core suite and one fresh exact-merge reproduction.  Do
not rerun a targeted command already covered by the unchanged full suite
unless diagnosing a failure.  PNPLabs consumes the exact verified core
artifacts byte-for-byte and must not invoke Lean, Lake, Elan, or the core proof
suite.
