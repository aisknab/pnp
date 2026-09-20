# Computed whole-support minimum bridge

Current coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-20-279`.

Formal artefact coverage: 255 of 257 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Exact scope

For arbitrary finite wire carriers and keep masks, the physical whole-support seed is derived from all original gates. Its computed saturated interface contains exactly the original gate-valued ordinary outputs, while every computational field is available. Explicit size-preserving comparisons identify its full-profile reference minimum with the independent whole-carrier output-and-field minimum. The actual computed full-profile replacement attains that minimum, has zero remaining whole-carrier full slack, and returns no strict improvement exactly when the original whole-carrier full slack is zero. The seed, interface, observer, minimum and replacement are derived rather than supplied correctness data.

## Limits

The whole-span reference branch remains exhaustive, including minimum search, source matching and saturation influence. Zero slack after exhaustive reference minimization is not the manuscript's unconditional ZeroSlack theorem or a polynomial PCCMin algorithm. This does not discover a proper positive support, compile arbitrary minima into proper-local VerifyDW histories, reconstruct the complete noncomputational profile grammar, derive global route coverage or unconditional SaturatePositive and BCELReady, or establish complete polynomial runtime, output-size or certificate bounds. The eligible root theorem remains absent and P = NP is not proved.

## Construction and proof interfaces

The [whole-support construction](../lean/PNP/NANDClosedWholeMinimumPrefix.lean)
enumerates every actual gate record, then uses the existing saturation
construction. Every gate source and computational field is retained. The
ordinary interface contains exactly gate-valued ordinary outputs. An
output-index search identifies the corresponding original output;
non-interface positions are false padding, not unconstrained observations.

The [size-preserving comparison](../lean/PNP/NANDClosedWholeMinimum.lean)
renames any full-equivalent whole carrier’s original inputs into the padded
domain and reconstructs every required interface output from its actual
ordinary outputs. Required computational fields remain available. This
gives one minimum inequality; the preceding physical reconstruction gives
the other. Neither direction supplies the equality or an optimal replacement
as a premise. A false keep mask never authorizes forgetting a full-mode field.

The principal checked statements are:

```lean
theorem full_minimum (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (snapshot target keep).fullMinimum = WireProfile.fullMinimum target

theorem result_optimal (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (ClosedSupportFullGain.result target keep (seed target)).implementation.gateCount =
      WireProfile.fullMinimum target

theorem fullSlack_eq (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    (snapshot target keep).fullSlack = WireProfile.fullSlack target

theorem result_zero_fullSlack (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    WireProfile.fullSlack (ClosedSupportFullGain.result target keep (seed target)) = 0

theorem improvement_none_iff (target : WireCarrier inputs outputs fields)
    (keep : Fin fields → Bool) :
    ClosedSupportFullGain.improvement? target keep (seed target) = none ↔
      WireProfile.fullSlack target = 0
```

## Independent regression boundaries

The [regression](../lean-regression/PNPClosedWholeMinimum.lean) checks eight
general type contracts, six kernel guards with axiom audits and eight
executable cases: empty dimensions, primary/constant outputs, hidden fields,
full/quotient separation, field-only circuits, repeated outputs, keep-mask
independence and multiple independent inputs. Finite tests are not theorem
authority. Whole-span reference minimization is not a proper-local rewrite.

The [axiom audit](../lean-audit/PNPClosedWholeMinimumAxiomAudit.lean) imports
the explicit root and checks all 22 reviewed closures. They use only the
allowed standard axioms `propext` and `Quot.sound`, with no project-specific
assumptions or unexpected classical choice.

The [source contract](../audits/lean-closed-whole-minimum0.test.mjs) freezes
the general construction. The [compiled publication contract](../audits/lean-closed-whole-minimum-publication0.test.mjs)
rejects changed types, supplied correctness, altered fingerprints, missing
evidence, added authority and widened global or polynomial claims.

## Progress and publication

M279 closes the concrete whole-support compatibility edge between the candidate-derived ambient support minimum and the independent whole-carrier output-and-computational-field minimum. The proof uses actual size-preserving translations in both directions, not a supplied equality or an assumed optimal replacement. The resulting exact whole-span branch still performs exhaustive reference minimization and supplies neither proper-local rewrite discovery nor global route coverage or polynomial bounds. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

Publication decision: defer. This identifies two finite reference minima and the exact whole-span reference branch, not a new polynomial construction, proper-positive support discovery, complete manuscript profiles or global route closure. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.

See the [integration plan](./plans/2026-09-20-computed-whole-support-minimum-bridge.md),
[canonical progress ledger](../status/PROOF_PROGRESS.json),
[preceding physical reconstruction](./lean_closed_support_full_gain.md) and
[pinned manuscript archive](../archive/legacy-v0/ARCHIVE.json).
