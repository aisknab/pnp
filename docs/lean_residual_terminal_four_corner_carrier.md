# Checked four-corner carrier transport

`lean/PNP/ResidualTerminalFourCornerCarrier.lean` reconstructs the carrier
transport needed between the legacy report §3 support square and the §11.1
`BN2-CoherentOptimum` obligation named
`fourCornerOptimaCarrierCompatible`.

The previous modules already compute a saturated meet, left side, right side,
and join from two finite seeds. They also compute each governed frontier,
extract each open candidate, prove the side-only frontier pushout, and prove
that a forgetful terminal projection commutes with the square. This module
packages those exact results as one checked carrier. It does not ask a caller
to supply a frontier, coordinate map, permutation, or compatibility
certificate.

## What is now kernel checked

`TerminalFourCornerCarrier` contains only:

- one computed `TerminalSaturatedSupportSquare`;
- one finite direct-wire candidate; and
- one explicit forgetful terminal projection.

Its meet, left, right, and join supports are obtained by calling the existing
computed corner function. Its extracted candidates and projected frontiers
are obtained from the same corner. Lean proves that every corner is governed
and physically compatible, that the extracted boundary and interface are
exactly the governed endpoints, and that every boundary, interface, and
role-indexed profile list is duplicate-free.

There is no host-side lookup and no fixed coordinate table. A boundary wire,
interface producer, or profile coordinate remains the same value in the
common ambient wire, gate, or profile type as it moves through the square.
The duplicate-free theorems prevent one corner from silently identifying two
entries in those canonical coordinate lists.

## Exact profile transport

For every terminal role and every profile coordinate, the meet contains that
coordinate exactly when both sides contain it. The join contains it exactly
when either side contains it. A coordinate on either side therefore reaches
the join unchanged.

These are unbounded finite statements. They quantify every computed square,
role, and coordinate admitted by the types. They are not another collection
of fixed example positions.

## Fail-closed physical transport

Physical coordinates can disappear when two sides are combined because they
have become internal. The carrier therefore exposes computed `Option`
classifiers rather than pretending that every side coordinate survives.

- A query for a wire outside the chosen side boundary returns `none`.
- A query for a producer outside the chosen side interface returns `none`.
- A retained boundary wire occurs at the identical coordinate in the join.
- An internalized boundary wire is a gate output selected by the opposite
  side.
- A retained interface producer occurs at the identical gate coordinate in
  the join.
- An internalized interface producer has neither an external consumer nor a
  global-output use in the combined support.

`TerminalFourCornerCarrier.complete_transport` collects the exact endpoints,
duplicate freedom, meet and join profile laws, total classification of every
present side coordinate, and projection compatibility in one proposition.
The construction derives every field from the carrier data.

## Proof and hostile checks

The dedicated axiom transcript audits all 28 new public declarations and ten
reused support-square interfaces. The observed closure is limited to Lean's
`propext` and `Quot.sound`. The audit rejects `Classical.choice`, project
axioms, `sorry`, `admit`, native or SAT shortcuts, host lookup, and
caller-supplied transport certificates.

The regression contains an active square where one boundary and one
interface coordinate become internal, retained boundary and interface
coordinates survive at the same ambient values, shared and one-sided profiles
transport exactly, all four corners retain their endpoints, and an empty
square rejects absent physical queries. It also checks the common projection
and the complete carrier proposition.

The hostile audit changes corner selection, extracted or projected endpoints,
meet and join logic, the opposite-side witness, join retention, fail-closed
queries, duplicate-freedom fields, and the final construction. It separately
injects assumptions, project axioms, caller certificates, host lookup, proof
shortcuts, and downstream overclaims. Every mutation must be rejected.

The focused commands are:

```bash
lake build PNP.ResidualTerminalFourCornerCarrier
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFourCornerCarrierAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFourCornerCarrier.lean
node --test audits/lean-residual-terminal-four-corner-carrier0.test.mjs
```

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
761,711 bytes pin 2,352 exact kernel theorem types and have canonical-object
SHA-256
`2bab8fea8dbd56ee8594ceb2c5335efa7f8dd935fb11ff00f944c4c252b239c2`
and file SHA-256
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

## Boundary still open

This milestone supplies the common ambient carrier needed before one can
compare four optimum realizers coherently. It does not construct those
optimum realizers on this square, prove that four independently attained
minima share one carrier, establish the full
`fourCornerOptimaCarrierCompatible` obligation, build a coherent four-corner
optimum, prove side-tight completion, or prove BN2 square legitimacy.

It also does not prove `SaturatePositive`, Package E, `BCELReady`, complete
obstruction routing, ZeroSlack, PCCMin, polynomial runtime, SAT in P, removal
of a project assumption, or P = NP. Those remain separate downstream proof
obligations.
