# Four-corner optimum coherence classification

`lean/PNP/ResidualTerminalFourCornerOptimumCoherence.lean` reconstructs the
next bounded dependency in the pinned legacy report's §11.1
`BN2-CoherentOptimum` paragraph. The previous milestone put the four canonical
full and quotient optima on one faithful ambient carrier. This module now asks
the next exact question: do those independently selected optima agree along
all four legs of the support square?

The answer is computed for every finite support square, observer, projection,
and selected mode. It is not assumed. The result is either a checked coherent
tuple or the first exact mismatch in a deterministic finite order.

## Directed square transport

The classifier uses these four legs, in this order:

1. meet to left;
2. meet to right;
3. left to join;
4. right to join.

`TerminalOptimumLegTransport` contains only the selected leg. Its support
inclusion, profile transport, ambient coordinate, and retained-output query
are derived from the computed `TerminalFourCornerCarrier`. A caller cannot
supply a transport certificate.

The physical coordinate action is the identity on the existing common
ambient carrier. This proves the exact square commutation law
`TerminalFourCornerCarrier.optimumTransportTheta`. A source interface output
is compared only when `retainedOutput?` finds the identical producer in the
target interface. A `none` result is the fail-closed internalized case and no
external semantic value is invented for it.

## Deterministic checks

In full mode, the classifier first examines obligation-role coordinates in
corner order meet, left, right, join. An observed `true` value is returned as
an `openObligation` failure.

It then traverses the four legs. For each leg it checks:

1. every retained source output over `allBoolTuples` in canonical valuation
   order;
2. profile coordinates in the existing ten-role order and canonical
   coordinate order.

Full mode compares every selected profile coordinate. Quotient mode compares
only coordinates retained by the carrier's projection. The separate
`firstOptimumModeMismatch?` query checks forgotten quotient coordinates and
reports the first exact mismatch that prevents full-profile promotion. This
keeps quotient evidence comparison-only, as required by the existing mode
firewall.

The failure type distinguishes:

- an open obligation;
- a retained-output semantic mismatch;
- a non-charge profile mismatch;
- a charge-profile mismatch;
- a forgotten-coordinate mode mismatch.

Every returned failure carries the exact leg, coordinate or valuation,
producer where applicable, and both Boolean values. The soundness theorems
prove that the stored values really differ, or that the stored obligation is
really open.

## Successful branch

`TerminalFourCornerCoherentOptimumTuple` packages the successful branch. It
retains:

- the previous common-carrier compatibility theorem;
- absence of any mode-appropriate coherence failure;
- exact full and quotient minimum size vectors;
- numerical side-tightness in both modes;
- exact full and quotient incidence values;
- the physical square commutation law.

`noFailure_iff_coherentOptimumTuple` proves that the executable query returns
`none` exactly when this complete tuple exists.

The universal theorem
`TerminalFourCornerCarrier.fourCornerOptimumCoherenceDichotomy` states that
every finite computed terminal support square has either such a tuple or an
exact sound first failure. This is an unbounded structural classifier. The
small examples in the regression file are tests of the universal definitions,
not the source of theorem credit.

## Deliberate boundary

The theorem does not claim that every square reaches the coherent branch. It
does not convert a returned failure into one of the later no-outcome routes,
prove that those routes are absent, or prove `sideTightCompletionExists`.
Consequently it also does not prove BN2 square legitimacy,
`SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin, a polynomial residual
route, SAT in P, or P = NP.

Those implications remain downstream obligations. This module supplies the
finite, kernel-checked coherence-or-first-failure interface they can consume.

## Verification

```bash
lake build PNP.ResidualTerminalFourCornerOptimumCoherence
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFourCornerOptimumCoherenceAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFourCornerOptimumCoherence.lean
node --test audits/lean-residual-terminal-four-corner-optimum-coherence0.test.mjs
```

The audited closure permits only Lean's standard `propext` and `Quot.sound`.
It rejects project axioms, `Classical.choice`, placeholders, evaluator
shortcuts, host-side lookup, and caller-supplied correctness certificates.
The hostile audit also rejects downstream overclaims. Every mutation must be
rejected.

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-112` records
24,934 declarations, 13,352 theorem-kind declarations, 7,015 assumption-free
theorems, 14,691 excluded private declarations, 228 source-closure modules,
and 2,352 reviewed milestone candidates. Its 15,824,195 canonical bytes have
SHA-256
`10ca3467d9c899300ac9c76c84ce62f87c8157e73fc39f8af82b203a4be9a8eb`;
the exact Lean source closure has SHA-256
`3161b45bbf5468a66e86fac1cf8dd6bef3ea19b1d472c536a620695085e589d1`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-112`
contains 92 milestones: 89 earned and three deliberately unearned. Its
761,711 bytes pin 2,352 exact kernel theorem types. The canonical object has
SHA-256
`2bab8fea8dbd56ee8594ceb2c5335efa7f8dd935fb11ff00f944c4c252b239c2`
and the file has SHA-256
`8404f2c2b178d87c42f4501b4490286c90da593281dad2708297c22b0fbfa9df`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-112`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-OPTIMUM-COHERENCE-111`,
has byte-identical 1,901,511-byte status mirrors with SHA-256
`e0515fe3af9c24f155165f172f2f00c1bbcff21822b5479141183262cf34b8d5`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-112` has a
197,818-byte TeX source with SHA-256
`550fa4769b476b52cae5df3efa912a925b9e4c6d1460fe6a601d060e4a810f72`
and a deterministic 77-page, 437,284-byte A4 PDF with SHA-256
`0e30911e395f6054e968b2ac0de1a27cf9bb2e77a182e6744ac37407dd1de058`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` remain explicit.
