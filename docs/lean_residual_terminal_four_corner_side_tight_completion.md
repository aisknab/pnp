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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-114` records
25,059 declarations, 13,401 theorem-kind declarations, 7,025 assumption-free
theorems, 14,705 excluded private declarations, 230 source-closure modules,
and 2,385 reviewed milestone candidates. Its 16,124,474 canonical bytes have
SHA-256
`fe036a74807d08c1e763a850722eb8113c1b3d186ef41d900641ed6e9eadb44c`;
the exact Lean source closure has SHA-256
`588c6626fcd4c0996f770b1118648ee99c82453ab303faf884e5e712d0107771`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-114`
contains 94 milestones: 91 earned and three deliberately unearned. Its
773,039 bytes pin 2,385 exact kernel theorem types. The canonical object has
SHA-256
`7e5d8cfa5e15971a46f2e52d0fdf32edc06718673d95f1714c771f892e0360cb`
and the file has SHA-256
`5ee8bb52412e04ce7b5ba9bccb619070d0963df00044f8f26b2bfe0aef73d186`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-114`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-TIGHT-BASIS-MAXIMUM-113`,
has byte-identical 1,935,171-byte status mirrors with SHA-256
`a72f8bfd4df79e29c1ea8908883f6211e65094ab162cf98b19a12b8ae080b158`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-114` has a
200,233-byte TeX source with SHA-256
`785181cde2595e9f21cb95239530b1aa9bc194b2e5d5d0198925956c8e853fd5`
and a deterministic 78-page, 439,981-byte A4 PDF with SHA-256
`447832f2f4992227446044f188aed18d07443dc0f9c285799f8eeeee8617d6e7`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` remain explicit.
