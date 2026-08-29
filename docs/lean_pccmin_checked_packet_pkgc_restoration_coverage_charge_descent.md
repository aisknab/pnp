# Checked PkgC restoration-coverage charge descent

M207 upgrades one exact M206 branch from a residual-reduction diagnostic to a
kernel-checked decrease of the manuscript residual rank.

The authoritative module is
`lean/PNP/PCCMinCheckedPacketPkgCRestorationCoverageChargeDescent.lean`.
Its public endpoint is
`PNP.DirectWire.pccmin_checked_packet_pkgc_restoration_coverage_charge_route_or_zeroslack_checked_complete`.

## Computed measure

For a finite BN4 cell ledger, `terminalBN4UnsignedChargeSize` sums the natural
mass of every cell. It is not a cell-count surrogate. Lean proves that the
measure is additive under concatenation and invariant under exact list
permutation.

Every complete restoration-coverage unit contributes one positive and one
negative BN4 cell, both with mass one. A PkgC separating pair has two nonempty
consumer sides, so its canonical cancellation subledger has unsigned charge

```text
2 * (left consumer length + right consumer length) > 0.
```

M206's exact multiset embedding states that the ambient ledger is a
permutation of this cancellation subledger followed by the computed
remainder. Consequently, the ambient charge is the removed positive charge
plus the remainder charge, and the remainder charge is strictly smaller.

## Exact rank interpretation

`TerminalPkgCBN4ChargeRankContext` contains exactly the other nine coordinates
of `TerminalResidualRank`. Its `rank` function inserts the computed unsigned
charge as the eighth `chargeSize` coordinate. For every such fixed context,
Lean applies `terminalResidualRank_chargeSize_lt` and proves

```text
rank(remainder charge) LexLT rank(ambient charge).
```

The proof-bearing
`TerminalPkgCRestorationCoverageAmbientBN4ChargeDescent` retains the exact
canonical residual-ledger equality, the strict scalar charge inequality, and
the context-parametric ten-coordinate rank inequality. The value is
constructed directly from the M206 embedding. No caller supplies a rank,
inequality, descent certificate, or success flag.

## Composed outcome

The M207 classifier preserves all five M206 outcomes:

1. conditional ZeroSlack;
2. exact restoration Hall deficit;
3. exact ambient charge-coordinate descent;
4. proved ambient incompatibility; or
5. exact source activation mismatch.

Only the third branch gains a formal descent theorem. The Hall,
incompatibility, and activation-mismatch branches remain explicit diagnostics.

## Claim boundary

M207 proves one genuine rank transition but not complete global route
coverage. It does not prove that the computed remainder is empty, derive the
source/restoration/ambient data from every terminal input, construct semantic
full candidates, close the other returned routes, establish HN/BUD/HB
semantic completeness, prove unconditional SaturatePositive, BCELReady, or
ZeroSlack, construct polynomial PCCMin, put CNFSAT in P, or prove P = NP.

The risk-weighted proof-completion estimate remains 35 percent with a 20 to 40
percent uncertainty range. Formal artefact coverage is 183 of 185 current
scoped rows, and zero of five global gates are closed.

## Verification

The focused evidence consists of:

- `lean-audit/PNPPCCMinCheckedPacketPkgCRestorationCoverageChargeDescentAxiomAudit.lean`;
- `lean-regression/PNPPCCMinCheckedPacketPkgCRestorationCoverageChargeDescent.lean`;
- `audits/lean-pccmin-checked-packet-pkgc-restoration-coverage-charge-descent0.test.mjs`;
- the compiled theorem inventory and formal publication map; and
- the exact M207 history entry in `status/PROOF_PROGRESS.json`.

The axiom transcript for all 16 reviewed declarations permits only the Lean
standard axioms already allowed by the repository and rejects project-specific
axioms and `Classical.choice`.
