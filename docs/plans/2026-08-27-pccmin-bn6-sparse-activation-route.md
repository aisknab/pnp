# M200: sparse proper-cut activation route

## Legacy anchor and dependency edge

- Legacy anchors: `RW-BCELReady`'s `properCutConstantEquation` and
  `bcelAnchorAlgebraBooleanOrRoutes` obligations, BN6's nonnegative
  hypergraph cellization, and V53 constant-cut rigidity in the pinned
  canonical manuscript.
- Current formal boundary: M198 returns an exact raw-ledger activation
  mismatch but obtains it from an all-proper-cut powerset scan. M199 removes
  that scan on the coherent branch by checking an exact shape-specific V53
  basis, but a rejected basis remains only a structural obstruction and does
  not name the proper cut required by the existing BCEL activation route.
- Exact edge closed by M200: prove that the singleton and two-anchor proper
  cuts form a complete cut-equation test family for every sparse positive V53
  hypergraph, then return the first exact small-cut activation mismatch on
  rejection and retain M199's conditional ZeroSlack branch on acceptance.

This is an arbitrary-finite theorem. It must not fix the carrier, cut, cell,
payload, rank, candidate, circuit, or number of anchors.

## Unbounded abstraction and theorem targets

Define one canonical duplicate-free list containing every singleton and
two-anchor order-preserving sublist of the carrier, filtered to nonempty proper
cuts. Prove that every emitted cut:

- is an order-preserving carrier sublist;
- is nonempty and proper;
- has length at most two; and
- belongs to a family whose length has a quadratic bound in the carrier
  length.

Define the small-cut equation as equality of the V53 crossing weight and the
declared positive cut value on every member of that list. Prove the general
equivalence

```text
2 <= system.carrier.length ->
  (system.SmallProperCutEquation <-> system.ConstantProperCuts)
```

without enumerating arbitrary subsets. The large-carrier implication must
reconstruct the V53 rigidity argument from singleton and pair equations: pair
weights vanish, every listed positive proper-footprint cell is impossible,
the remaining cells are full-span, and one singleton equation fixes the exact
full-span weight. The two- and three-anchor cases must use the exact existing
full-cell and complement-symmetry lemmas.

Add a total proof-bearing classifier that returns either the complete
constant-proper-cut equation or one explicit first mismatch from the canonical
small-cut list. A mismatch must retain the cut, its proper-cut proof, its
length-at-most-two proof, and the exact unequal cut weight. It must not return
an opaque Boolean, an untyped structural failure, or a caller-supplied
certificate.

The checked PCCMin endpoint will be
`PNP.DirectWire.pccmin_checked_packet_bn6_bcel_sparse_activation_route_or_zeroslack_checked_complete`.
Under the same checked selector-silence premise as M199, it must return either
zero residual slack or one singleton/pair proper cut where the direct raw
positive-cell activation ledger differs from the checked BCEL defect. The
accepted branch may reuse M199's exact constant-activation adapter; the
rejected branch must use M198's raw-ledger conservation theorem.

## Claim boundary and downstream blockers

The terminal problem, checked BCEL-ready certificate, raw positive cells and
their supports and payloads, realizer table, claims, finite ranks, dependency
table, route-clear result, and checked HB closure remain supplied. M200 turns
M199's basis rejection into the existing exact BCEL activation-obstruction
shape, but it does not prove that the obstruction is a verified gain or a
globally decreasing transition.

The quadratic bound concerns only the canonical cut-test list. Raw-cell
construction, terminal searches, selectors, tables, claims, blockers, and
certificates still lack a complete encoded-input-size polynomial construction
and runtime theorem. Upstream steps may still enumerate subsets.

Consequently M200 does not close complete PkgC/BN3--BN6 integration,
manuscript-wide `SaturatePositive` or `BCELReady`, unconditional `ZeroSlack`,
polynomial `PCCMin`, deterministic CNFSAT in P, a global gate, the eligible
root theorem, or P = NP. No fixed progress checkpoint changes state. The
risk-weighted estimate remains 35 percent, the uncertainty range remains 20
to 40 percent, and zero of five global gates remain closed. Formal artefact
coverage may change independently when the publication row is earned.

## Required evidence

- compilation of the arbitrary-finite small-cut sufficiency theorem, total
  classifier, checked PCCMin adapter, and explicit `PNP` root import;
- regressions for coherent and mismatching two-, three-, and four-plus-anchor
  systems, including a positive non-full large-carrier cell whose rejection
  yields a concrete singleton/pair mismatch;
- exact raw-ledger reflection and both public route-or-ZeroSlack branches;
- a quadratic test-family length theorem and hostile checks rejecting
  `terminalListSubsets`, the M195 powerset classifier, caller-supplied
  constant activation, erased mismatch evidence, fixed carriers, and claims
  of complete polynomial PCCMin or unconditional ZeroSlack;
- axiom transcripts for every reviewed declaration, rejecting project axioms,
  `sorryAx`, and `Classical.choice`;
- synchronized theorem inventory, publication map, status, progress history,
  report, workflow expectations, audit questions, and current documentation;
  and
- the normal exact-merge core evidence followed by the separate PNPLabs
  whole-publication, deployment, and production checks, without rebuilding
  Lean in PNPLabs.

## Stop condition

If singleton/pair equations do not suffice constructively for the arbitrary
finite sparse V53 system, or if a failed small-cut classifier cannot retain an
exact raw-ledger mismatch at the checked boundary, stop at that theorem edge.
Do not replace it with sampled cuts, a fixed carrier, an all-subset scan, a
caller-supplied mismatch witness, a new axiom, `sorry`, a weakened route, or an
unconditional or complete-polynomial claim.
