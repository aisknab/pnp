# Terminal profile-dependency semantics

M232 proves semantic reflection for the existing candidate-derived terminal
profile dependency computation. It is a local dependency theorem for the
manuscript's saturation argument, not unconditional SaturatePositive, BCELReady,
ZeroSlack, an exact PCCMin algorithm, or a polynomial-runtime result.

## Definitions and theorem boundary

The source is
[ResidualTerminalCandidateSaturation](../lean/PNP/ResidualTerminalCandidateSaturation.lean).
It already constructs physical edges from the candidate program and profile
edges from the supplied executable observer's exact finite influence relation.
M232 does not replace or weaken that computation.

- `terminalCandidateProfileObservation` observes the existing ambient
  implementation for a list of selected gates at one profile coordinate.
- `terminalGateInfluencesProfile_eq_true_iff` proves that the computed
  influence bit is true exactly when inserting that gate changes the observation
  in some canonical subset context of the other gates.
- `terminalCandidateProfileRequires_eq_influence` identifies every
  profile-to-gate edge with that influence bit and the coordinate's exact rule
  role. It covers all ten roles, not a chosen role or gate.
- `terminalCandidateSaturate_profile_noninterference` proves that a gate
  absent from the actual computed saturation cannot change a retained profile
  coordinate in any canonical context.

The results quantify over arbitrary finite input, gate, output and profile
sizes, candidates, executable models, coordinates, gates, seeds and canonical
contexts. Membership in the computed closure and in the specified context
domain is an ordinary domain premise, not a caller-supplied correctness or
coverage certificate. No arbitrary dependency relation replaces the computed
one.

In standard terms, the influence relation is a Boolean essential-variable
relation over finite subsets. The last theorem is a noninterference consequence
of closure under all such dependencies. It does not establish an unproved
normalization theorem for arbitrary lists or arbitrary ambient implementations.

## Interaction example and failure mode

An observer returning true exactly when at least two gates are present is
unchanged between the empty support and either singleton. Nevertheless, either
gate influences it in the context containing the other gate. The permanent
[regression](../lean-regression/PNPResidualTerminalProfileDependencySemantics.lean)
checks this interaction, all rule-role labels, rejection of a wrong role, and
a constant observer with a retained coordinate and genuinely absent gate.

A singleton-only influence test would miss that dependency. The general
reflection theorem and the hostile source contracts reject that substitute.
The theorem does not infer that every omitted gate is harmless without the
retained-profile and actual computed-closure premises.

## Evidence and remaining limitations

The [root audit](../lean-audit/PNPResidualTerminalProfileDependencySemanticsAxiomAudit.lean)
covers the observation definition and all three general theorems. Their compiled
dependency closures contain only the standard `propext` and
`Quot.sound` axioms, with no project-specific axiom or classical choice.

The executable observer and profile model remain supplied data. Influence
enumerates all subsets and is not a polynomial-time construction. This local
result does not derive the full terminal family, settle route completeness,
preserve positivity through every saturation event, or supply the positive
slack-to-activation bridge.

The [milestone plan](plans/2026-09-11-terminal-profile-dependency-noninterference.md)
records the legacy anchor and downstream obligations. No fixed weighted
checkpoint is earned by this result alone. Formal artefact coverage and the
risk-weighted estimate remain separate in the canonical
[progress ledger](../status/PROOF_PROGRESS.json).

Formal artefact coverage: 208 of 210 current scoped publication rows earned.
Risk-weighted proof completion estimate: 40%. Uncertainty range: 20% to 40%.
Global gates closed: 0 of 5.

A separate PNPLabs publication is deferred: this local theorem does not change
the published M231 bottom line. Keep its exact verified source pin and coherent
progress snapshot until a later major publication batch.
