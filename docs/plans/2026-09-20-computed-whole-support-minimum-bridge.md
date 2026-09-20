# M279: computed whole-support minimum bridge

Coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-20-279`.

Status: the general proof and focused explicit-root checks are complete.
Publication integration is under validation. Release must use the actual
verified M278 main-branch merge, not its feature-branch tip.

Formal artefact coverage: 255 of 257 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

## Legacy anchor and exact dependency

The manuscript pinned by [ARCHIVE.json](../../archive/legacy-v0/ARCHIVE.json)
at `final-pnp-proof-report-docs-hardened-7072f8d-sealed` distinguishes the
RW-MuBridge whole-circuit minimum from admissible local gain. It supplies
construction specification and provenance, not Lean theorem authority.

Existing terminal bridge and wire-profile theorems establish abstract
reference specifications. This closes a different concrete edge: the
candidate-derived saturated whole support, padded input domain, ordinary
interface and computed availability observer versus the independent
ordinary-output-and-computational-field whole minimum.

The local history language does not yet compile every semantic minimum
into manuscript-admissible rewrites. A supplied execution or correctness
certificate is not a substitute for that missing construction.

## Unbounded abstraction and exact theorem types

Only an arbitrary finite wire carrier and keep mask are supplied. Physical
seed, support, interface and observer are derived. Both inequalities use
size-preserving constructions. In `PNP.DirectWire.ClosedWholeMinimum`:

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

## Verification and integration order

1. Compile uniform support/interface facts and both comparisons in an
   isolated checkout; inspect their compiled axiom closures.
2. Add general contracts and independent hidden-field, empty-dimension and
   whole-span regressions. Runtime examples are not proof authority.
3. Reconcile root imports, both inventory name producers and publication
   pins; build the changed root chain before root-importing audits.
4. Export the inventory once, seal actual hashes, and reconcile status,
   progress, commands, tests and current documents before validation.
5. Generate current outputs, run focused checks and the nonduplicated
   validation union, then retain independent exact-object release evidence.
6. Merge after independent checks; defer the website unless a major
   public proof boundary changes.

## Remaining obligations and progress decision

The whole-span reference branch remains exhaustive, including minimum search, source matching and saturation influence. Zero slack after exhaustive reference minimization is not the manuscript's unconditional ZeroSlack theorem or a polynomial PCCMin algorithm. This does not discover a proper positive support, compile arbitrary minima into proper-local VerifyDW histories, reconstruct the complete noncomputational profile grammar, derive global route coverage or unconditional SaturatePositive and BCELReady, or establish complete polynomial runtime, output-size or certificate bounds. The eligible root theorem remains absent and P = NP is not proved.

M279 closes the concrete whole-support compatibility edge between the candidate-derived ambient support minimum and the independent whole-carrier output-and-computational-field minimum. The proof uses actual size-preserving translations in both directions, not a supplied equality or an assumed optimal replacement. The resulting exact whole-span branch still performs exhaustive reference minimization and supplies neither proper-local rewrite discovery nor global route coverage or polynomial bounds. No fixed load-bearing checkpoint changes state; weights, checkpoint statuses, proof estimate and uncertainty are unchanged.

## Publication decision

Publication decision: defer. This identifies two finite reference minima and the exact whole-span reference branch, not a new polynomial construction, proper-positive support discovery, complete manuscript profiles or global route closure. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.
