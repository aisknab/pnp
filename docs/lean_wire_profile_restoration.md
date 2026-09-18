# Constructive wire-profile restoration cost and exact gain boundary

Current component coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-19-275`.

## Dependency and construction

The pinned manuscript's mode firewall and Package E distinguish quotient
comparison from constructive full use. RW-SaturatePositive requires positivity
preservation or a genuine named route during exposure. Physical accounting
alone is not a semantic-minimum theorem. This component connects the existing
shared hidden-wire materializer to the actual comparison model rather than
creating a parallel restoration compiler.
See the [research plan](./plans/2026-09-19-wire-profile-restoration-cost.md).

For arbitrary finite input, ordinary-output and computational-field widths, the existing concrete quotient agreement is equivalent to wire-profile quotient comparison. The actual shared hidden-wire materializer restores the computed quotient-minimum witness into a full-equivalent carrier, preserving every ordinary output and actual field at every input valuation. If F is the full minimum, Q the quotient minimum, C the actual materializer charge, D = F - Q and S the actual full-field normalization saving, the theorems prove F <= Q + C, D <= C, paid cost = F + (C - D), S <= C - D and normalized cost = F + (C - D - S). Strict improvement against the original carrier is equivalent to the remaining overhead being smaller than its full slack; the executable acceptance test checks the actual final size and yields a sound strict equivalent gain. The existing complete one-input constructor has gate count exactly F for arbitrary output and field widths, and improves the original exactly when full slack is positive. No full replacement, minimum, charge or correctness certificate is supplied to the constructed route.

## Exact cost and acceptance boundary

Let N be the original physical size, F the full minimum, Q the quotient minimum,
C the actual shared materializer charge and S the actual saving from full-field
physical normalization of the paid witness. The checked identities are:

```text
D = F - Q
F <= Q + C
D <= C
paid cost = F + (C - D)
S <= C - D
normalized cost = F + (C - D - S)
strict original-size gain iff C - D - S < N - F
```

The defect is bounded by an actual construction cost; equality is not assumed.
The normalizer's trace supplies S. Neither its savings nor semantic optimality
are supplied as premises. The acceptance function compares the actual final
size with the original and returns a sound full-equivalent strict gain only
when that comparison succeeds.

## Limitation and existing recovery

Three successive negations give a kernel-checked positive-slack example for
which the paid restoration followed by fixed physical normalization finds no
gain. This does not refute the complete route family. The existing complete
unary constructor already recovers the example. Its general one-input minimum
compatibility theorem allows arbitrary output and field widths; it does not
claim completeness for arbitrary input widths or earn duplicate progress.

## Exact boundary

This is a cost and compatibility interface for computational wire profiles, not complete manuscript profiles or a terminal-derived family. The materializer charge only upper-bounds projection defect; equality and forced-cost transparency are not established. Physical normalization is not a semantic minimizer. A kernel-checked positive-slack example is refused by restoration plus normalization, while the existing unary route recovers it; this limits that component, not every route or the manuscript's complete route family. Returning no gain does not establish ZeroSlack. Unary completeness is restricted to one input and is reused, not newly proved for arbitrary inputs. Reference minimization is exhaustive, not a polynomial PCCMin algorithm. Complete Package E, global route coverage and rank decrease, unconditional SaturatePositive, BCELReady and ZeroSlack, exact polynomial PCCMin, encoded runtime, output and certificate bounds, deterministic CNFSAT in P and the eligible root remain open. No fixed weighted checkpoint or global proof gate closes, and P = NP is not proved.

## Evidence and verification

The compiled publication interface pins 19 exact theorem types, their defining
module and exact axiom closures. Every reviewed theorem uses only the Lean
standard axioms `propext` and `Quot.sound`; none uses `Classical.choice` or a
project-specific axiom. The helper `CheckedGain.strictGain` is a definition,
not a theorem pin; its use is covered by `CheckedGain.checked`.

- [General definitions and proofs](../lean/PNP/NANDWireProfileRestoration.lean)
- [Exact root axiom probe](../lean-audit/PNPWireProfileRestorationAxiomAudit.lean)
- [General contracts and executable cases](../lean-regression/PNPWireProfileRestoration.lean)
- [Kernel-checked limitation and recovery](../lean-regression/PNPWireProfileRestorationObstruction.lean)
- [Source and hostile contracts](../audits/lean-wire-profile-restoration0.test.mjs)
- [Compiled publication and negative contracts](../audits/lean-wire-profile-restoration-publication0.test.mjs)

Nine general type contracts cover arbitrary finite dimensions or, for the unary
compatibility, arbitrary output and field widths. Three guarded runtime cases
exercise hidden-value restoration, sharing recovered by normalization and empty
dimensions. Four kernel theorems establish positive slack, refusal, their
coexistence and existing unary recovery. Runtime cases are not proof authority
and do not establish a general theorem.

Use `npm run audit:m275` for the source and release contracts. After the explicit
root build and compiled inventory, the durable workflow executes:

```bash
set -euo pipefail
node scripts/check-lean-axioms.mjs lean-audit/PNPWireProfileRestorationAxiomAudit.lean
lake env lean -DwarningAsError=true --run lean-regression/PNPWireProfileRestoration.lean
lake env lean -DwarningAsError=true lean-regression/PNPWireProfileRestorationObstruction.lean
```

## Progress and publication

Formal artefact coverage: 251 of 253 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

No fixed load-bearing checkpoint changes state. The score, uncertainty range
and global gates remain unchanged. The eligible root is absent and the
publication gate remains false. Reference minimization remains exhaustive.
See the [canonical progress ledger](../status/PROOF_PROGRESS.json).

Publication decision: defer. This establishes a general restoration-cost interface and its checked limitations, not terminal-derived families, complete Package E or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.
