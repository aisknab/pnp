# Actual physical saturation accounting and first-obstruction fidelity

M235 connects the computed saturation trace to exact physical gate charges
and active dependencies. It then isolates the genuine remaining physical
obstructions without treating those obstructions as completed global routes.

## Exact theorem boundary

The [executable saturation module](../lean/PNP/ResidualTerminalExecutableSaturation.lean)
adds `terminalSaturateTrace_event_context`. For any finite system, seed and
actually generated event, the dependent is already in the before-records and
the required record is absent. The proof follows the real pending queue,
duplicate-free work state and cost-record invariant.

The [physical-accounting module](../lean/PNP/ResidualTerminalPhysicalSaturationAccounting.lean)
provides four downstream interfaces:

- `terminalCandidateSaturateTrace_supportCostBalanced` proves the exact
  support-size increase measured by the unchanged extractor: one for a newly
  generated gate and zero for metadata.
- `terminalCandidateSaturateTrace_event_owner` places the actual selected
  rule/dependent pair in the computed active-owner list.
- `terminalCandidateSaturateTrace_physicalObstruction` proves that a generated
  nontransparent event is a physical insertion with a real nonunique-owner,
  full-minimum-growth or quotient-cost obstruction.
- `terminalCandidateSaturateTrace_balance_or_physicalObstruction` uses the
  existing total classifier. It either preserves full slack and nondecreasing
  projection defect at canonical computed saturation, or returns the exact
  first physical obstruction and its transparent prefix.

These are arbitrary-dimension interfaces, not fixed circuits or finite schedule
prefixes. No freshness, charge-balance, active-owner, all-transparent-history or
preselected-route certificate replaces the existing computation.

Here an active owner is a rule/dependent pair in the existing computed
event-owner list. This does not construct or certify the manuscript-wide
charge-ownership map. Active dependency ownership is not uniqueness.

## Regressions and assumption audit

The [permanent regression](../lean-regression/PNPResidualTerminalPhysicalSaturationAccounting.lean)
applies all five interfaces at arbitrary dimensions. Its concrete execution
fixtures show two output records depending on one physical gate: there is one
new gate but two active owners. Duplicate seeds do not create another insertion
or owner. A separate unique-owner branch still has a full-minimum mismatch.
Thus exact unit support growth does not establish forced unit minimum growth.

Malformed raw events with an absent dependent or an already present required
record are excluded by the general context theorem itself. The unchanged
[M234 regression](../lean-regression/PNPResidualTerminalSaturationTraceFidelity.lean)
also checks cycles, all metadata constructors, actual nonconstant observers
and an open obligation that cost transparency does not discharge.

The [explicit-root axiom audit](../lean-audit/PNPResidualTerminalPhysicalSaturationAccountingAxiomAudit.lean)
covers all five interfaces. Their dependency closures use only `propext`
and `Quot.sound`, with no project-specific axiom or classical choice.
The [hostile contracts](../audits/lean-residual-terminal-physical-saturation-accounting0.test.mjs)
reject finite-instance substitutes, supplied certificates, weakened contexts,
incorrect physical charges, widened obstruction claims and fingerprint drift.

## Remaining proof burden

The executable observer and profile model remain supplied data. Influence and
semantic minima use exhaustive finite reference constructions; no polynomial
runtime is proved.

Exact physical support growth does not establish full-minimum growth, a
quotient bound, obligation discharge, complete closure safety or a global
named route. A first local obstruction is not thereby a verified gain, an
exact route or strict descent. No input-derived terminal family, global route
coverage, unconditional SaturatePositive, BCELReady or ZeroSlack, or complete
polynomial PCCMin construction is earned. Deterministic CNFSAT in P and the
eligible root theorem remain absent; the publication gate remains false.

The [milestone plan](plans/2026-09-11-physical-saturation-accounting.md) records
the section 3, section 4 and RW-SaturatePositive dependency edges.
No fixed weighted checkpoint or global gate closes.

Formal artefact coverage: 211 of 213 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

These distinct measures come from the
[canonical progress ledger](../status/PROOF_PROGRESS.json). Neither is confidence
that `P = NP` is true, a probability of success or a time estimate.

Publication decision: defer. Preserve the coherent M231 PNPLabs source pin
until a major publication is warranted. Core milestone and submilestone
notifications continue independently.
