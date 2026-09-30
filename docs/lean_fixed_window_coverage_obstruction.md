# Fixed windows do not certify global circuit minimality

This correction establishes a limitation of the source-derived physical-window
search: for every fixed circuit-independent support cap, there is a circuit
with a strictly smaller equivalent implementation even though the complete
bounded search finds no accepted improvement.

It does not decide P versus NP, refute every manuscript route, or supply a
polynomial solver. It does not exclude growing windows or global transformations.
It identifies a specific coverage obligation that a corrected route must meet.

## Exact general result

The [guarded family](../lean/PNP/NANDGuardedSpineFamily.lean) has an explicit
equivalent implementation with two fewer gates for every family parameter.
The saving is proved for every input valuation, not assumed or inferred from
a bounded synthesis experiment.

Nevertheless, [every proper extracted support](../lean/PNP/NANDGuardedSpineSupportMinimum.lean)
is minimum among all equivalent independent-boundary NAND implementations.
The theorem permits disconnected selections, arbitrary record widths, repeated
records, sharing, constants, and every ordered output position. It does not
assume an interval, a supplied minimum, an optimizer or a coverage certificate.
The full selected gate set is intentionally excluded: the whole circuit can
be improved.

The [all-limit theorem](../lean/PNP/NANDGuardedSpineBoundedQuiet.lean) therefore
proves:

```lean
theorem no_uniform_zero_slack_limit :
    ¬ ∃ limit : Nat, ∀ (inputs gates outputs : Nat)
      (source : Candidate inputs gates outputs),
      BoundedQuiet source limit → residualSlack source.toImplementation = 0
```

Here `BoundedQuiet` is the [existing all-record predicate](../lean/PNP/NANDCompleteBoundedWindowSearch.lean)
for the actual extractor and causal acceptance test, not a weakened substitute.
The actual complete scheduled scan returns `none` by a symbolic theorem;
verification does not run an exponentially large reference minimization.

## Why this matters to the intended proof

The manuscript's saturation, RW-BCELReady and unconditional ZeroSlack route
needs a justified connection from remaining global slack to an available
improving move. This result rules out obtaining that connection merely by
choosing one fixed physical support cap for the implemented local search.

Completeness inside a bounded class remains valid. Its fixed-cap candidate-count
bound is not a complete polynomial-runtime theorem, and allowing the cap to grow
does not preserve a uniform polynomial bound automatically. A repaired route
must derive both its global coverage and its encoded-size/runtime bounds.
Supplying either as an input premise would not discharge the missing proof.

This differs from the [earlier compatible-support slack obstruction](./lean_compatible_support_slack_obstruction.md):
that result concerns independent open replacements whose reconnection can be
cyclic. Here every proper support is already minimum even before restricting
competitors by the causal test. Both findings retain their distinct scopes.
Historical manuscript artifacts remain unchanged.

## Verification and progress treatment

The explicit root imports the result and its dependency chain. The three audits
cover all thirteen public conclusions in the joint-bound, proper-support-minimum
and bounded-quiet modules. Their kernel regression probes retain arbitrary
parameters, disconnected and repeated selections, equal-valued output positions,
the zero-cap case, and the necessary exclusion of the full support.

No positive publication row or fixed checkpoint is awarded for this correction.
The previously earned foundations, reductions, finite strict-gain/stopping
scaffolds and project-axiom removals do not assert fixed-window completeness.
The audit has not identified a basis for revoking those earned checkpoints.

At this correction review, the last earned-row baseline remains
`PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-20-280`:

- Formal artefact coverage: 256 of 258 current scoped publication rows earned.
- Risk-weighted proof completion estimate: 40%.
- Uncertainty range: 20% to 40%.
- Global gates closed: 0 of 5.

These are separate measurements; the evidence-row ratio is not proof completion.
The [canonical progress ledger](../status/PROOF_PROGRESS.json) governs future
checkpoint changes. This finding is dated 2026-09-30; it is not a retroactive
claim that the M280 publication already contained this theorem.
