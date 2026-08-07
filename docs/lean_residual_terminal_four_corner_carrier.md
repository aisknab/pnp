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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-07-110` records
24,675 declarations, 13,260 theorem-kind declarations, 6,984 assumption-free
theorems, 14,607 excluded private declarations, 226 source-closure modules,
and 2,316 reviewed milestone candidates. Its 15,168,239 canonical bytes have
SHA-256
`2e585d493c1b5364f0bf340b7d141bbb231bef97d609056909f19481c77e45c9`;
the exact Lean source closure has SHA-256
`77155b9e3cd7ba5c931ccd20f587cb5aa0567e1b016b37845d904eec4205426d`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-07-110`
contains 90 milestones: 87 earned and three deliberately unearned. Its
750,275 bytes pin 2,316 exact kernel theorem types and have canonical-object
SHA-256
`94f46541a5e524e9b4989cf28331c74456c52d41098b5a2634c8cf2a8c11fc17`
and file SHA-256
`20d29d0d85e4edd2ee0ab1cfbe41f403e17b2655ea82651ffeb089c0fe88372b`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-07-110`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-07-RESIDUAL-TERMINAL-FOUR-CORNER-CARRIER-109`,
has byte-identical 1,867,836-byte status mirrors with SHA-256
`a411b2dae18d3869cea0ba236628604e9041f06010553d1e0cfc8b2434cef805`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-07-110` has a
195,614-byte TeX source with SHA-256
`51e174f1cbff5030a905ce6e791741a0f69facb1500acfad3b6b1c72ccdea641`
and a deterministic 77-page, 436,374-byte A4 PDF with SHA-256
`ed75cd52e1a5bb6a143838fa7a86f0d9a88ad66e9f1d039413fab5dc671690ad`.

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
