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

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-111` records
24,758 declarations, 13,298 theorem-kind declarations, 6,989 assumption-free
theorems, 14,645 excluded private declarations, 227 source-closure modules,
and 2,341 reviewed milestone candidates. Its 15,645,082 canonical bytes have
SHA-256
`ea373cfe65d8c99fab5c3896b7d594f96724a8eab2b3d2b7ddf0abdfee81aabe`;
the exact Lean source closure has SHA-256
`55b94c1f15c1003306e4efcf83469416817e29530e7eae8a25aa4948efa9d370`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-111`
contains 91 milestones: 88 earned and three deliberately unearned. Its
757,472 bytes pin 2,341 exact kernel theorem types and have canonical-object
SHA-256
`8c208bb3815b2513a3a167dd72adf77903c5a1f1d5c75e590e8064448a309737`
and file SHA-256
`8efcfb683a0aeb7f2b6884bf6374493b3e69c20f6bb5617d2e63252646b384d6`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-111`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-OPTIMUM-COMPATIBILITY-110`,
has byte-identical 1,887,604-byte status mirrors with SHA-256
`72d754abc757743f41696680d14a795d973fe86285fd93aa61ef322d65062a5f`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-111` has a
196,791-byte TeX source with SHA-256
`55ffa6aa19ba0c1c3143265d21ac3e481b05556a38f2d9b62591245078b0e492`
and a deterministic 77-page, 436,878-byte A4 PDF with SHA-256
`121978e29f6f37caf842fe8ad76c6ce7e8812bc1bbb7c018f068d5247e23e431`.

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
