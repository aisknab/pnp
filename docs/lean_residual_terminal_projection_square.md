# Governed terminal projection square

`lean/PNP/ResidualTerminalProjectionSquare.lean` reconstructs the next
all-finite dependency edge in §3 of the pinned legacy manuscript. The
manuscript requires the completed support square to remain a square after a
forgetful profile projection. Lean now proves that structural law for every
finite direct-wire candidate, every explicit terminal dependency system,
every computed saturated support square, and every forgetful terminal
projection.

This is one theorem over all finite inputs, gates, outputs, profile
widths, candidates, systems, squares, and projections. It is not a sequence
of fixed profile coordinates or a repeatable finite-prefix milestone.

## Exact forgetful projection

`TerminalGovernedFrontier.project` retains the complete physical boundary and
interface of a governed frontier. In each of the ten terminal profile roles,
it filters the finite coordinate list by the projection's Boolean `keep`
function. Lean proves:

- the boundary and interface are unchanged;
- role membership is exactly original membership together with `Keeps`;
- duplicate freedom is preserved; and
- applying the same projection twice is idempotent.

A coordinate satisfying `Forgets` occurs in no projected role at any square
corner. No caller certificate, host lookup, or hard-coded coordinate is used.

## The commutative square

The projected join is compared with
`terminalProjectedGovernedFrontierPushout`. That construction reads only the
completed left and right corners. Its physical fields are the already proved
side-only boundary and interface gluing, while each role profile is the
side-profile union filtered by the projection. It never reads the completed
join corner.

For every computed saturated support square, Lean proves:

- every projected corner keeps its exact computed physical frontier;
- the projected meet role is exactly the overlap of the projected side roles;
- the projected join role is exactly the union of the projected side roles;
- the independently completed and projected join equals the side-only
  projected pushout; and
- the whole statement is packaged by
  `TerminalSaturatedSupportSquare.governed_projection_compatible`.

Thus completion and gluing commute with every explicit forgetful terminal
projection at this structural frontier level.

## Legacy anchor and remaining boundary

This closes the §3 projection-commutation edge immediately after governed
frontier pushout. It keeps the manuscript's carrier conventions and
dependency order: physical ports come from the actual direct-wire program,
profile coordinates retain their computed terminal roles, and the terminal
dependency system remains explicit input.

The result is structural. It does not prove that a square was produced by the
later BN2 construction, that its four local minima are side-tight, that the
square is legitimate for the manuscript's contradiction, or that projection
creates positive slack. In particular, it does not prove BN2 square
legitimacy, `SaturatePositive`, `BCELReady`, complete obstruction routing,
ZeroSlack, PCCMin, polynomial runtime, SAT in P, or P = NP. Those remain
downstream obligations.

## Audit and reproduction

The closed audit covers all 20 public declarations in the module plus 13
reused projection, frontier, completion, and pushout interfaces. The only
permitted closure is the approved Lean-standard set `propext` and
`Quot.sound`. Project axioms, `Classical.choice`, `sorry`, `admit`, native
decision shortcuts, host lookup, and caller certificates are rejected.

```text
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalProjectionSquareAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalProjectionSquare.lean
node --test audits/lean-residual-terminal-projection-square0.test.mjs
```

The generated inventory, publication-map, status, TeX, PDF, size, hash, and
coordinate evidence was recorded only after the compiled source and
expectation chain stabilized:

- inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-112`, with
  24,934 declarations, 13,352 theorems, 7,015 assumption-free theorems,
  2,352 reviewed milestone candidates, 228 source-closure modules,
  15,824,195 bytes, and SHA-256
  `10ca3467d9c899300ac9c76c84ce62f87c8157e73fc39f8af82b203a4be9a8eb`;
- publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-112`,
  with 92 milestones, 89 earned milestones, 2,352 exact theorem pins,
  761,711 bytes, canonical-object SHA-256
  `2bab8fea8dbd56ee8594ceb2c5335efa7f8dd935fb11ff00f944c4c252b239c2`,
  and file SHA-256
  `8404f2c2b178d87c42f4501b4490286c90da593281dad2708297c22b0fbfa9df`;
- Lean source-closure SHA-256
  `3161b45bbf5468a66e86fac1cf8dd6bef3ea19b1d472c536a620695085e589d1`;
- status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-112`,
  with byte-identical 1,901,511-byte status mirrors and SHA-256
  `e0515fe3af9c24f155165f172f2f00c1bbcff21822b5479141183262cf34b8d5`;
- canonical TeX with 197,818 bytes and SHA-256
  `550fa4769b476b52cae5df3efa912a925b9e4c6d1460fe6a601d060e4a810f72`;
  and
- deterministic 77-page A4 PDF with 437,284 bytes and SHA-256
  `0e30911e395f6054e968b2ac0de1a27cf9bb2e77a182e6744ac37407dd1de058`.

The publication gate remains false, all four project assumptions and six
blockers remain explicit, activation fingerprints remain unset, and
`PNP.Main.p_eq_np` remains absent.
