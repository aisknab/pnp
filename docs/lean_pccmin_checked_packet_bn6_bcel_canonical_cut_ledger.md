# Canonical BN6 raw cut-ledger conservation

M198 closes an exact accounting edge left implicit at M197. A raw
`TerminalBN6PositiveCell` is converted to the existing V53 hyperedge using its
carrier-normalized footprint and positive payload mass. Its direct cut
contribution is that mass exactly when the footprint crosses the cut, and the
raw activation weight is the sum over the supplied positive-cell ledger.

Lean proves constructively that collecting atoms at one canonical footprint
preserves exactly the masses of the matching raw cells. The duplicate-free
canonical footprint universe then partitions every raw cell by its normalized
footprint. Consequently, for every finite carrier, raw cell ledger, and cut,
the activation weight of the canonical grouped family equals the direct raw
crossing-mass sum. Duplicate footprints may be coalesced, but no positive mass
is lost, duplicated, or reassigned.

`PCCMinCheckedPacketBN6BCELPositiveCells.groupedFamily_activationWeight_eq_raw`
installs that conservation theorem at the checked BCEL carrier. The public
theorem is
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_canonical_cut_ledger_route_or_zeroslack_checked_complete`.
Under the same complete checked selector-silence premise as M197, it returns
either zero residual slack or one explicit nonempty proper cut where the direct
raw positive-cell activation weight differs from the checked BCEL defect.

## Claim boundary

The raw positive cells, supports, masses, payload values, terminal problem,
checked BCEL-ready certificate, realizer table, claims, ranks, route-clear
equation, dependency table, and checked HB closure remain supplied. M198 does
not derive the raw cells from BN3, BN4, BN5, PkgC, or every terminal input, and
it does not derive the constant-activation equation.

The remaining raw cut-ledger mismatch is diagnostic route evidence, not a
verified gain or globally decreasing transition. The conservation proof does
not enumerate cuts, but the inherited M195 proper-cut classifier may enumerate
a powerset. No encoded-input-size polynomial theorem is claimed for the
complete construction.

M198 therefore does not close complete PkgC/BN3--BN6 integration, prove
manuscript-wide `SaturatePositive` or `BCELReady`, establish unconditional
`ZeroSlack`, construct polynomial `PCCMin`, put CNFSAT in P, close a global
gate, create `PNP.Main.p_eq_np`, or prove P = NP.

Formal artefact coverage is 174 of 176 current scoped rows. The separate
risk-weighted proof-completion estimate remains 35 percent, its uncertainty
range remains 20 to 40 percent, and zero of five global gates are closed.

## Verification

```text
lake build PNP
lake env lean -DwarningAsError=true lean-regression/PNPPCCMinCheckedPacketBN6BCELCanonicalCutLedger.lean
lake env lean -DwarningAsError=true lean-audit/PNPPCCMinCheckedPacketBN6BCELCanonicalCutLedgerAxiomAudit.lean
node --test audits/lean-pccmin-checked-packet-bn6-bcel-canonical-cut-ledger0.test.mjs
```

The axiom transcript covers nine reviewed declarations. Their compiled closure
contains only `propext` and `Quot.sound`; it contains no project-specific axiom,
`sorryAx`, or `Classical.choice`.
