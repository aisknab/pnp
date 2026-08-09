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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-09-115` records
25,099 declarations, 13,423 theorem-kind declarations, 7,025 assumption-free
theorems, 14,705 excluded private declarations, 231 source-closure modules,
and 2,397 reviewed milestone candidates. Its 16,265,958 canonical bytes have
SHA-256
`42695c4971028fff27f3c7f03eff1450c62845db0654436f59a190c3d2625af5`;
the exact Lean source closure has SHA-256
`01503dfe0db82b6672d8ace6cce5061846a8f0ad41322fc022f73676bad80124`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-09-115`
contains 95 milestones: 92 earned and three deliberately unearned. Its
777,623 bytes pin 2,397 exact kernel theorem types. The canonical object has
SHA-256
`6391db3d3a1f0530a9197b6193bb0ed507a18acfbc40ca75a418f98c9db3933b`
and the file has SHA-256
`9e688aae5553d680b6ff1f8fea8587f121edaf76c55efef110909f0d08173af8`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-09-115`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-09-RESIDUAL-TERMINAL-COMPUTED-BN2-SQUARE-LEGITIMACY-114`,
has byte-identical 1,949,873-byte status mirrors with SHA-256
`c8adb9479ce14f702d693fc175710dd37670b0095c29d8522ced3ddb534bbeda`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-09-115` has a
201,436-byte TeX source with SHA-256
`391a179f9889bde11aef29b8e7bf7d32c4a7182d55a6bc556b3f80e7001cbc6d`
and a deterministic 79-page, 440,948-byte A4 PDF with SHA-256
`8bb12a7777ef0aad2af88a644e08877820bfb667da9636d8fa696f6fec31226e`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` remain explicit.
