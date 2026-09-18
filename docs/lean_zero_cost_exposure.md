# Source-derived zero-cost alias exposure

Current component coordinate: `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-18-273`.

## Dependency and construction

The pinned manuscript requires a zero-cost retract before interface exposure may
preserve the residual optimization problem. This component constructs one such
branch instead of assuming that absence of newly allocated gates is sufficient.
It is a bounded reconstruction of that dependency, not the complete manuscript
exposure dichotomy. See the [research plan](./plans/2026-09-18-source-derived-zero-cost-exposure.md).

For arbitrary finite input, ordinary-output and extra-field widths, a literal output extension adds only input, constant or existing-output aliases and a literal projection recovers the original outputs without allocating gates. Both constructions transfer arbitrary equivalent realizations, proving exact equality of the semantic reference minimum and residual slack. A source-derived recognizer scans the actual output wires; a gate field is accepted exactly when an ordinary output names that same wire. The tuple compiler derives every alias and accepts exactly when all requested fields have such literal references. The actual WireCarrier exposure therefore preserves physical gate count, semantic minimum and slack whenever this executable source check accepts. Constructors and recognition do not enumerate truth tables or minimum implementations and do not receive an observer, semantic minimum, route or correctness certificate from the caller.

ZeroCostExposure.Reference has only input, constant and existing-output
constructors. The extension keeps the gate program and appends the referenced
fields; projection keeps the program and recovers the ordinary outputs. The
proofs transfer arbitrary equivalent realizations in both directions, not only
the chosen implementation. The two minimum inequalities therefore give exact
equality, and unchanged physical size gives exact residual-slack equality.

The recognizer examines the actual source. An internal gate can be used only if
an ordinary output names that same gate. The tuple compiler derives every
reference and succeeds exactly when the layout check accepts every requested
field. The carrier bridge applies those results to WireCarrier.exposed; no
supplied semantic observer or minimum realization is hidden in the interface.

## Exact boundary and counterexamples

This covers the literal input/constant/old-output alias class, not every semantically free exposure or arbitrary hidden internal wire. Refusal proves neither semantic impossibility nor a Package E gain or route. Adding no physical gates need not preserve the semantic minimum, and unique physical ownership or an extra recorded charge does not force an equal minimum increase. The concrete counterexamples are regression and obstruction evidence, not new global progress. The existing fresh-independent-input materializer theorem is reused, not re-awarded. Full manuscript profiles, positive-cost transparency for arbitrary materializers, terminal-family derivation, global route coverage, unconditional SaturatePositive, BCELReady and ZeroSlack, exact general PCCMin and complete encoded-input polynomial runtime, output and certificate bounds remain open. No fixed weighted checkpoint or global proof gate closes. Deterministic CNFSAT in P and the eligible root remain absent, and P = NP is not proved.

The regressions include inputs, both constants, repeated output aliases, empty
field lists and empty ordinary outputs. They also check two distinct obstructions:

- A hidden NOT output can change the semantic minimum when exposed even though
  the physical program gains no gate.
- A separately allocated duplicate NOT gate adds physical charge without forcing
  an equal increase in the minimum required by the output semantics.

A different gate computing the same value can be refused. This is intentional:
the checker is complete for literal aliases, not for semantic redundancy.
The existing fresh-independent-input materializer result remains separately
valid; its independence hypothesis cannot be dropped by physical bookkeeping.

## Evidence and verification

The compiled publication interface pins 22 exact theorem types, defining modules
and axiom closures. No project-specific axiom occurs. Most closures are empty;
some recognition results use the allowed Lean standard axioms Quot.sound or
propext. None of these 22 results uses Classical.choice.

- [General definitions and proofs](../lean/PNP/NANDZeroCostExposure.lean)
- [Actual carrier bridge](../lean/PNP/NANDWireCarrierZeroCostExposure.lean)
- [Axiom probe](../lean-audit/PNPZeroCostExposureAxiomAudit.lean)
- [Kernel-checked regressions](../lean-regression/PNPZeroCostExposure.lean)
- [Source contracts](../audits/lean-zero-cost-exposure0.test.mjs)
- [Compiled publication and negative contracts](../audits/lean-zero-cost-exposure-publication0.test.mjs)

Use `npm run audit:m273` for the source and release contracts. The durable Lean
workflow runs the exact axiom probe and regression after the root build:

```bash
set -euo pipefail
node scripts/check-lean-axioms.mjs lean-audit/PNPZeroCostExposureAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPZeroCostExposure.lean
```

The release reuses the verified unchanged root build and compiled inventory.
The focused negative checks reject weakened types, supplied conclusions, missing
evidence, extra proof authority, widened scope and changed status fields. The
compiled inventory and publication map are the authority for earned coverage.

## Progress and publication

Formal artefact coverage: 249 of 251 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%.
Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

No fixed load-bearing checkpoint changes state. The risk-weighted estimate,
uncertainty range and all five global gates are unchanged. The exact eligible
root `PNP.Main.p_eq_np` is absent and the publication gate remains false.
See the [canonical progress ledger](../status/PROOF_PROGRESS.json).

Publication decision: defer. This establishes a source-derived literal-alias branch with exact minimum and slack preservation, not all semantic exposure, full manuscript profiles or global route coverage. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.
