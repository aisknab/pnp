# Computed wire-profile models and exact independent-field cost

Current coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-19-276`.

Formal artefact coverage: 252 of 254 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Exact scope

For arbitrary finite input, ordinary-output and computational-field widths, target-relative availability computes one actual constant, input or gate source that realizes a field uniformly over every input valuation. Rebinding constructs a carrier without adding gates and identifies terminal full and quotient profile minima with the corresponding wire-profile minima. The model constructor proves coherence between its base and ambient observers under unused-input padding and output rewording. A source-derived field seed and physical dependency closure yield an actual extracted support preserving every field at all ambient input valuations. For any old implementation with semantic minimum F and any natural width k, an explicit extension appends k independent NAND fields on disjoint fresh input pairs. Semantic gate retraction proves that every equivalent implementation needs at least F + k gates; the matching construction attains that bound. Its actual wire profile therefore has full minimum F + k, all-forgotten quotient minimum F, projection defect k and unchanged full slack. Three general coupling theorems establish these same exact minima and their difference inside the constructed terminal profile model, without a supplied model, minimum, field support or correctness certificate.

## Limits

This is a computed model for actual computational wire fields, not the complete manuscript profile grammar or a terminal-derived governed family. The extracted support is field-preserving but is not asserted to be proper, smaller or optimal. The exact additive cost theorem concerns the explicit independent fresh-input NAND family, not arbitrary correlated, duplicated or supplied manuscript fields. The semantic retraction helper has an explicit uniform constant-value hypothesis, discharged for that family; it is not a general polynomial semantic-constant detector. The existing shared materializer charge is only bounded below by the family's projection defect, not proved equal to it. Availability checks enumerate valuations and reference minima remain exhaustive; no complete polynomial minimizer follows. Complete Package E, global route coverage and rank decrease, unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.

## Proof interfaces

The [availability model](../lean/PNP/NANDWireProfileAvailability.lean) computes
one actual source uniformly across valuations; it does not choose a new source
for each valuation. The [ambient construction](../lean/PNP/NANDWireProfileAmbient.lean)
preserves that observer, and the [field closure](../lean/PNP/NANDWireProfileFieldClosed.lean)
selects actual dependencies before extraction.

[Semantic gate retraction](../lean/PNP/NANDSemanticGateRetraction.lean) removes
distinct gates whose values are uniformly constant after a zero-gate input
binding. For the [fresh-field lower bound](../lean/PNP/NANDFreshFieldCost.lean),
independent fresh outputs require distinct gates; setting their inputs false
justifies retraction while preserving the old computation. A
[matching extension](../lean/PNP/NANDFreshFieldExtension.lean) proves the exact
minimum, and the [actual profile](../lean/PNP/NANDFreshFieldProfile.lean) transfers
it to full and quotient minima. The
[coupling](../lean/PNP/NANDComputedWireProfileCost.lean) identifies those minima
inside the computed terminal model.

For physical old size N, old minimum F and extension width k:

- Physical size is N + k; full minimum is F + k.
- Forgetting every added field leaves quotient minimum F.
- Projection defect is k; full slack remains N - F.
- The shared materializer charge is at least k, not asserted equal to k.

## Independent regression boundaries

The permanent fixtures check arbitrary-dimension theorem types, observer-domain
obstructions, uniform versus pointwise source choice, unused inputs, ordinary
output wiring, actual support extraction, zero widths, redundant old circuits,
duplicate fields and invalid semantic erasure. Executable examples are checks,
not proof authority or new progress checkpoints.

The [publication audit](../audits/lean-computed-wire-profile-publication0.test.mjs)
pins the exact compiled interfaces and rejects weakened conclusions, supplied
conclusions, added axioms, missing evidence and widened publication scope.

## Progress and publication

M276 combines the source-derived computational-profile model with an exact independent-field cost family, then proves their general coupling. One uniformly valid actual source is computed for each available field; arbitrary input padding and output rewording preserve the observer, and actual field seeds derive a preserving support. A semantic gate-retraction argument and matching extension prove the exact additional cost for arbitrary old implementations and arbitrary widths of independent fresh NAND fields. This retires those bounded model and cost interfaces, not arbitrary manuscript-field transparency, proper-support discovery, terminal-family derivation, global routing or polynomial minimization. The two prepared components are integrated and reviewed as one milestone rather than separate release cycles. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

Publication decision: defer. This supplies a computed computational-profile model and exact costs for an explicit independent-field family, not the complete manuscript profile grammar, terminal-derived families, complete Package E or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.

See the [integration plan](./plans/2026-09-19-computed-wire-profile-exact-field-cost.md),
[canonical progress ledger](../status/PROOF_PROGRESS.json),
[previous restoration boundary](./lean_wire_profile_restoration.md) and
[pinned manuscript archive](../archive/legacy-v0/ARCHIVE.json).
