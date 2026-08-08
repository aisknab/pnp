# Four-corner side-tight completion under local route silence

`lean/PNP/ResidualTerminalFourCornerSideTightCompletion.lean` reconstructs the
next dependency in the pinned legacy report's Section 11.1
`BN2-CoherentOptimum` paragraph. The previous milestone supplied a deterministic
classifier for the four canonical full and quotient optima. This module closes
the next local edge named `sideTightCompletionExists`: for every finite computed
terminal support square and selected comparison mode, either the classifier
returns its exact first local obstruction or a checked side-tight coherent
optimum tuple exists.

This is one unbounded theorem over arbitrary finite systems. The small carriers
in the regression module exercise the definitions, but they are not the source
of theorem credit.

## Exact route query

`TerminalOptimumRoutePhase` distinguishes two queries:

1. `.coherence mode` runs the existing first mode-appropriate coherence-failure
   query;
2. `.quotientPromotion` runs the existing forgotten-coordinate mismatch query.

`TerminalFourCornerCarrier.firstOptimumRoute?` is only this exact dispatch. It
does not consult a host-side schedule or accept a caller certificate.
`TerminalFourCornerOptimumRoutedFailure` stores a returned failure together with
an equality proving that it is the exact first result of the selected query.
Its `sound` theorem reduces to the previous kernel-checked soundness theorem for
that query.

The quotient-promotion phase stays separate. Silence of that phase is not used
to manufacture a full-mode completion, so quotient evidence remains
comparison-only.

## Total local result

`sideTightCompletionOrFirstRoute` gives the total result for every carrier,
observer, and selected mode:

- a `TerminalFourCornerCoherentOptimumTuple`; or
- a proof-bearing exact first local route.

The two branches cannot coexist.
`TerminalFourCornerOptimumRoutedFailure.excludesCoherentOptimum` proves that an
actual returned coherence route contradicts the tuple's exact no-failure field.

`NoOptimumCoherenceRoute` is definitionally the executable query returning
`none`. Under that computed premise, `sideTightCompletionExists` returns the
complete coherent tuple. The tuple retains the already-proved facts needed at
this boundary:

- common-carrier compatibility for all four optima;
- exact absence of a mode-appropriate first coherence failure;
- exact full and quotient minimum size vectors;
- numerical side-tightness in both modes;
- exact full and quotient incidence values;
- commutation of all four transport legs on the shared physical carrier.

`sideTightCompletionExistsEachMode` combines independently checked silence in
full and quotient modes. It does not use promotion silence.
`sideTightCompletion_fullValue` and
`sideTightCompletion_quotientValue` expose the exact minimum incidence value for
the selected mode.

## Deliberate boundary

This milestone proves the local Section 11.1 completion edge under local route
silence. It does not prove that every finite square has a silent route query.
It also does not:

- connect a local failure to the complete global CritC, Q, E, L, X, gain,
  exact, selector, and descent route system;
- prove BN2 square legitimacy;
- derive the terminal dependency system;
- extract and maximize the complete tight-basis family;
- prove `SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, polynomial runtime,
  SAT in P, or P = NP.

Those remain explicit downstream blockers. A later theorem must discharge the
complete global no-outcome premise before this conditional completion can serve
as the coherent branch of the manuscript's wider argument.

## Verification

```bash
lake build PNP.ResidualTerminalFourCornerSideTightCompletion
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFourCornerSideTightCompletionAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFourCornerSideTightCompletion.lean
node --test audits/lean-residual-terminal-four-corner-side-tight-completion0.test.mjs
```

The axiom transcript covers all 20 public declarations plus eight reused
dependencies. The approved closure contains only Lean's standard `propext` and
`Quot.sound`. The audit rejects project axioms, `Classical.choice`, `sorry`,
`admit`, native or SAT shortcuts, host-side lookup, caller certificates, a
collapsed promotion phase, unconditional completion, and downstream
overclaims.

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-113` records
24,999 declarations, 13,376 theorem-kind declarations, 7,022 assumption-free
theorems, 14,691 excluded private declarations, 229 source-closure modules,
and 2,364 reviewed milestone candidates. Its 15,930,331 canonical bytes have
SHA-256
`82fcdfd7443489f917d3987d31f604af6c163e9cb2a6fca2cd8aff98c38ff97f`;
the exact Lean source closure has SHA-256
`1ed937ea678bb853929da8c6958fe30fe09b837ad53fda5b53d5ce4da2584830`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-113`
contains 93 milestones: 90 earned and three deliberately unearned. Its
766,476 bytes pin 2,364 exact kernel theorem types. The canonical object has
SHA-256
`2e86afbec493f6cf4c30155c512e197a26e70b3c79b4f2a76dde71b0e6c650f9`
and the file has SHA-256
`6d05c3a4d70ea78994a0302a60c8ba8381e37ff4e9c30a774ab474a13bb9baac`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-113`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-SIDE-TIGHT-COMPLETION-112`,
has byte-identical 1,916,515-byte status mirrors with SHA-256
`b9aff3d3eee8fed7d232c41cf0e81dc2355a3cd27a720b64aafde01746b20656`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-113` has a
199,054-byte TeX source with SHA-256
`73ef5719cc112e91e262b42846db82f4e92cd1dc1184484ad67f2b0b5006a01f`
and a deterministic 78-page, 438,997-byte A4 PDF with SHA-256
`e196ce1a2c373dbab4bf5e0e70418f0029beed4e1cfb959c78981c4880c6db02`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` remain explicit.
