# Retained ambient-profile locality

M233 closes the arbitrary-support locality and retained-profile preservation
edge in the manuscript's saturation argument. It does not replace that route
with a finite fixture or strengthen it with a supplied correctness premise.

## Exact theorem boundary

The new [profile-locality module](../lean/PNP/ResidualTerminalProfileLocality.lean)
uses the existing candidate-derived dependency computation. Its structural
bridge is in [support extraction](../lean/PNP/ResidualTerminalSupportExtraction.lean).

- `extractTerminalSupport_eq_of_gateSelected_eq` proves that equal gate
  selection preserves all computed extraction fields; only the stored record
  list is replaced.
- `terminalAmbientSupportImplementation_eq_of_gateSelected_eq` turns that
  structural equality into equality of the actual ambient implementations.
- `terminalCandidateProfileObservation_eq_of_gateMembership_iff` normalizes
  arbitrary gate lists, including reordered and duplicated representations.
- `terminalCandidateSaturate_profile_locality` proves equality of actual
  observations for any two primitive-record supports that agree on the gates
  retained by the computed saturation, at every retained profile coordinate.
- `terminalCandidateSaturate_profile_preserved` applies that general locality
  theorem to the computed saturated support and the complete gate universe.

These statements quantify over arbitrary finite candidate dimensions, executable
models, seeds, primitive-record supports and retained profile coordinates.
Membership in the actual computed closure is a domain premise, not a supplied
dependency or completeness certificate.

The proof canonicalizes gate membership, extends M232's noninterference result
to arbitrary contexts, and removes every omitted gate by finite list induction.
The extraction algorithm and influence computation are unchanged.

## Regressions and assumption audit

The [permanent regression](../lean-regression/PNPResidualTerminalProfileLocality.lean)
contains arbitrary-dimension applications of all five interfaces. A concrete
nonconstant observer reads a real gate output: one gate is retained, an
independent gate is genuinely omitted, and the saturated observation still
equals the complete support's true output. Reordered records, duplicates and
non-gate metadata do not affect the result.

Empty closure gives false for that same observer while the complete support
gives true. This is a checked counterexample: the retained-profile premise is
necessary. An interaction-sensitive observer also exercises the theorem beyond
singleton-only dependency tests.

The [explicit root audit](../lean-audit/PNPResidualTerminalProfileLocalityAxiomAudit.lean)
checks all five theorem interfaces. Their dependency closures contain only
`propext` and `Quot.sound`, with no project-specific axiom or classical choice.
The [hostile contracts](../audits/lean-residual-terminal-profile-locality0.test.mjs)
reject weakened types, supplied premises, finite-only substitutes, changed
fingerprints and inflated publication claims.

## Remaining proof burden

The executable observer and profile model remain supplied data.
Influence enumerates all subsets and is not a polynomial-time construction.
This theorem does not identify the ambient observer with the differently typed
`profileSystem.observe`, derive faithful profile semantics or terminal families
from every valid input, prove transparent cost or complete routing, establish
unconditional SaturatePositive, BCELReady or ZeroSlack, or supply the complete
polynomial PCCMin construction and certificate bounds.

The [milestone plan](plans/2026-09-11-retained-ambient-profile-preservation.md)
records the legacy anchor and downstream obligations. No fixed weighted
checkpoint or global gate is closed by this local theorem.

Formal artefact coverage: 209 of 211 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%. Global gates closed: 0 of 5.

These are separate measurements from the
[canonical progress ledger](../status/PROOF_PROGRESS.json), not confidence in
`P = NP` or a time estimate. The eligible root theorem remains absent and the
publication gate remains false.

Publication decision: defer. Keep the verified M231 PNPLabs source pin and its
coherent metrics until a major publication is warranted; core milestone and
verified submilestone notifications continue independently.
