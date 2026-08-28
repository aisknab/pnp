# PkgC restoration-coverage BN6 ledger

M205 lifts M204's exact restoration-coverage classifier across the complete
arbitrary-finite active PkgC source ledger used at the M201 BN6 boundary. The
new classifier scans source cells in list order and retains the first exact
obstruction rather than accepting an always-total typed restorer.

The total classifier returns one of four proof-bearing outcomes:

- every source consumer system is singletonized, in which case the complete
  BN6 positive-cell ledger is constructed from the projected source cells;
- one source member carries the first exact `TerminalBN5HallDeficit`, its
  forced `qRestorationHall` route, and strict neighbourhood deficit;
- one source member carries a coverage-constructed balanced BN4 cancellation,
  computed ambient remainder, exact embedding, and residual-ledger reduction;
- or one source member and generated cell prove that no exact ambient
  embedding exists.

On the all-singletonized branch, Lean proves that the derived BN6 ledger has
exactly one cell per source cell, preserves payload order, and conserves the
source activation weight on every cut. The public endpoint is
`PNP.DirectWire.terminalPkgC_restorationCoverage_bn6_cellization_checked_complete`.

## Claim boundary

The active source cells and cuts, payloads, per-source restoration-coordinate
universes and maps, full-restoration coordinate lists, and ambient BN4 ledgers
remain supplied. Coordinate coverage does not materialize semantic full
candidates or derive the restoration data from every valid terminal input.

The Hall branch is not a verified global gain or rank-decreasing transition.
The computed remainder is not proved empty, and an ambient mismatch is not a
complete global route. The result therefore does not finish PkgC/BN3--BN6
integration, manuscript-wide `SaturatePositive` or `BCELReady`, unconditional
`ZeroSlack`, executable polynomial `PCCMin`, any global proof gate, `CNFSAT ∈
P`, the eligible root theorem, or `P = NP`.

Formal artefact coverage is 181 of 183 current scoped rows. The separate
risk-weighted proof-completion estimate remains 35 percent, its uncertainty
range remains 20 to 40 percent, and zero of five global gates are closed.

## Verification

```text
lake build PNP
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPkgCRestorationCoverageBN6Ledger.lean
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPkgCRestorationCoverageBN6LedgerAxiomAudit.lean
node --test audits/lean-residual-terminal-pkgc-restoration-coverage-bn6-ledger0.test.mjs
```

The axiom transcript covers 11 reviewed declarations. Every declaration
reaches only the approved Lean-standard closure (`propext` and `Quot.sound`);
no project-specific axiom, `sorryAx`, or `Classical.choice` is present.
