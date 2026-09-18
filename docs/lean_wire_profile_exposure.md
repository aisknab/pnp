# Wire-backed computational profiles and exposure balance

Current component coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-19-274`.

## Dependency and construction

The pinned manuscript distinguishes full realizations from quotient comparisons
and requires positivity preservation or a real named route during exposure.
This component reconstructs the computational-field comparison boundary from
actual source wires. It does not assume that physical accounting establishes a
semantic lower bound. See the [research plan](./plans/2026-09-19-wire-profile-exposure.md).

For arbitrary finite input, ordinary-output and computational-field widths, full comparison preserves the ordinary Boolean outputs and every actual wire-backed field at every input valuation. Quotient comparison masks only selected profile constraints and still preserves every ordinary output. Exact characterization, full-lift, attained-witness and universal lower-bound theorems establish quotient minimum <= full minimum <= physical gate count. Full slack plus projection defect equals physical size minus quotient minimum. Exposure masks that both retain a fixed comparison mask preserve that quotient minimum and the combined measure; nested masks transfer exactly the lost full slack into projection defect. Loss of positive full slack to zero yields an attained quotient witness with a strict deficit that cannot be used as a full witness. Forgetting all profile constraints recovers the ordinary semantic minimum. The actual all-gate source tuple, checked normalization and checked splicing connect this model to computational wire carriers without a supplied observer, semantic minimum or correctness certificate for the comparison model.

`WireProfile.mask` preserves the physical implementation and every ordinary
Boolean output. It substitutes a constant only for a forgotten profile slot.
`full_iff` and `quotient_iff` characterize equality at every input valuation;
`full_lift_iff` requires restoration of all omitted fields before quotient
evidence can serve as full evidence.

## What the accounting theorem establishes

Write N for physical gate count, F for the full semantic minimum and Q for the
quotient semantic minimum. The checked comparison model establishes:

```text
Q <= F <= N
full slack = N - F
projection defect = F - Q
full slack + projection defect = N - Q
```

For two exposure masks retaining the same comparison mask, Q is unchanged.
If the second exposure retains at least the first mask's fields, F cannot
decrease. The decrease in full slack equals the increase in projection defect
exactly. If previously positive full slack falls to zero, the attained quotient
minimum still supplies a strict deficit, but its witness fails full comparison.
This is an obstruction to promoting a relaxed witness, not a constructed
positive route or an unconditional saturation theorem.

Forgetting all profile fields recovers the ordinary semantic minimum.
`allGateFields` reads each actual source gate, but retaining every internal value
may overconstrain replacement. It is not identified with a canonical governed
terminal family or with the older observer-based profile type.

## Checked transformation compatibility

Existing carrier normalization preserves the full comparison and both minima.
Checked splicing does likewise only with its actual equivalent open replacement
and successful compilation premises. The result does not assert that such a
replacement is available on every input. Ordinary outgoing interface wires are
never made forgettable by these profile masks.

## Exact boundary

This is a proposed reconstruction of computational profile comparison, not the complete manuscript ten-role grammar or a derived governed terminal family. Ordinary outgoing Boolean interface wires cannot be forgotten. The all-gate field tuple is source-derived but is not asserted to be a canonical terminal profile. Conservation of full slack plus projection defect proves neither forced-cost transparency nor a Package E route, positive-slack activation, global rank decrease or route coverage. A quotient witness cannot be used as a full replacement without restoring every omitted field. Checked splicing still requires an equivalent open replacement and successful compilation; global discovery is not proved. Reference minima and attained witnesses use exhaustive finite minimization, not a polynomial algorithm. Unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded-input runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.

## Evidence and verification

The compiled publication interface pins 35 exact theorem types, their defining
module and exact axiom closures. Only the Lean standard axioms `propext` and
`Quot.sound` occur where needed; no reviewed result uses `Classical.choice` or
a project-specific axiom. The explicit root, not just the leaf module, has been
checked.

- [General definitions and proofs](../lean/PNP/NANDWireProfileExposure.lean)
- [Exact root axiom probe](../lean-audit/PNPWireProfileExposureAxiomAudit.lean)
- [Kernel-checked regressions](../lean-regression/PNPWireProfileExposure.lean)
- [Source and hostile contracts](../audits/lean-wire-profile-exposure0.test.mjs)
- [Compiled publication and negative contracts](../audits/lean-wire-profile-exposure-publication0.test.mjs)

Seven arbitrary-dimension contracts cover the general interfaces. Six named
regressions cover exact hidden-value transfer, quotient-only acceptance, failed
full promotion, retained-field refusal, mandatory ordinary outputs and empty
dimensions. These fixtures are regression evidence, not the basis for an
all-input theorem or additional progress credit.

Use `npm run audit:m274` for the source and release contracts. The durable Lean
workflow runs this exact block after the explicit root build and inventory:

```bash
set -euo pipefail
node scripts/check-lean-axioms.mjs lean-audit/PNPWireProfileExposureAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPWireProfileExposure.lean
```

## Progress and publication

Formal artefact coverage: 250 of 252 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

No fixed load-bearing checkpoint changes state. The score, uncertainty range
and global gates remain unchanged. The eligible root is absent and the
publication gate remains false. Reference minimization remains exhaustive.
See the [canonical progress ledger](../status/PROOF_PROGRESS.json).

Publication decision: defer. This establishes a general computational profile-comparison and exposure-balance component, not full manuscript profiles, terminal-derived families or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.
